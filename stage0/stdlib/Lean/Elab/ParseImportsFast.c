// Lean compiler output
// Module: Lean.Elab.ParseImportsFast
// Imports: Lean.Parser.Module
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__3;
static lean_object* l_Lean_ParseImports_State_imports___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__1;
lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__2;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_finishCommentBlock_eoi___closed__2;
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2;
static lean_object* l_Lean_ParseImports_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object*);
extern uint32_t l_Lean_idBeginEscape;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pos___default;
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_error_x3f___default;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2;
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushModule___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_parseImports_x27___closed__1;
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1519____spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___rarg(lean_object*);
static lean_object* l_Lean_ParseImports_whitespace___closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_preludeOpt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1;
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2;
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__4;
static lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____lambda__1(lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1;
static lean_object* l_Lean_ParseImports_main___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_many(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464_(lean_object*);
static lean_object* l_Lean_ParseImports_State_mkEOIError___closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380_(lean_object*);
lean_object* l_List_bindTR_go___at___private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173____spec__1(lean_object*, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1519____spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object*);
static lean_object* l_Lean_ParseImports_State_mkEOIError___closed__1;
static lean_object* l_Lean_parseImports_x27___closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError(lean_object*, lean_object*);
static lean_object* l_Lean_instToJsonImport___closed__1;
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__3;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock_eoi(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrintImportResult_imports_x3f___default;
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrintImportResult_errors___default;
static lean_object* l_Lean_ParseImports_whitespace___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object*, lean_object*);
static lean_object* l_Lean_instToJsonPrintImportResult___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult;
LEAN_EXPORT lean_object* l_Lean_ParseImports_preludeOpt___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushModule(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t);
static lean_object* l_Lean_ParseImports_finishCommentBlock_eoi___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____lambda__1___boxed(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1519_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToJsonPrintImportsResult___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_imports___default;
LEAN_EXPORT lean_object* l_Lean_instToJsonImport;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
LEAN_EXPORT lean_object* lean_print_imports_json(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult;
static lean_object* _init_l_Lean_ParseImports_State_imports___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParseImports_State_imports___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ParseImports_State_imports___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_State_pos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_State_error_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_ParseImports_State_imports___default___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_ParseImports_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ParseImports_instInhabitedState___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParseImports_instInhabitedParser___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ParseImports_instInhabitedParser___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ParseImports_instInhabitedParser(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_1, 2, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lean_ParseImports_State_mkEOIError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_State_mkEOIError___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_State_mkEOIError___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_dec(x_3);
x_4 = l_Lean_ParseImports_State_mkEOIError___closed__2;
lean_ctor_set(x_1, 2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = l_Lean_ParseImports_State_mkEOIError___closed__2;
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_string_utf8_next(x_2, x_3);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_string_utf8_next(x_2, x_3);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_State_next(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_string_utf8_next_fast(x_2, x_3);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_string_utf8_next_fast(x_2, x_3);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ParseImports_State_next_x27(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_ParseImports_finishCommentBlock_eoi___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unterminated comment", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_finishCommentBlock_eoi___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_finishCommentBlock_eoi___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock_eoi(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_dec(x_3);
x_4 = l_Lean_ParseImports_finishCommentBlock_eoi___closed__2;
lean_ctor_set(x_1, 2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = l_Lean_ParseImports_finishCommentBlock_eoi___closed__2;
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get_fast(x_2, x_5);
x_9 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_10 = 45;
x_11 = lean_uint32_dec_eq(x_8, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 47;
x_13 = lean_uint32_dec_eq(x_8, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 0);
lean_dec(x_17);
lean_ctor_set(x_3, 1, x_9);
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_6);
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
x_21 = lean_string_utf8_at_end(x_2, x_9);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_3, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_3, 0);
lean_dec(x_25);
x_26 = lean_string_utf8_get_fast(x_2, x_9);
x_27 = lean_uint32_dec_eq(x_26, x_10);
if (x_27 == 0)
{
lean_ctor_set(x_3, 1, x_9);
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_1, x_29);
lean_dec(x_1);
x_31 = lean_string_utf8_next_fast(x_2, x_9);
lean_dec(x_9);
lean_ctor_set(x_3, 1, x_31);
x_1 = x_30;
goto _start;
}
}
else
{
uint32_t x_33; uint8_t x_34; 
lean_dec(x_3);
x_33 = lean_string_utf8_get_fast(x_2, x_9);
x_34 = lean_uint32_dec_eq(x_33, x_10);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_35, 2, x_6);
x_3 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_1, x_37);
lean_dec(x_1);
x_39 = lean_string_utf8_next_fast(x_2, x_9);
lean_dec(x_9);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_6);
x_1 = x_38;
x_3 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_42 = l_Lean_ParseImports_finishCommentBlock_eoi(x_3);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = lean_string_utf8_at_end(x_2, x_9);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_3);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint32_t x_48; uint32_t x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_3, 2);
lean_dec(x_45);
x_46 = lean_ctor_get(x_3, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_3, 0);
lean_dec(x_47);
x_48 = lean_string_utf8_get_fast(x_2, x_9);
x_49 = 47;
x_50 = lean_uint32_dec_eq(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_string_utf8_next_fast(x_2, x_9);
lean_dec(x_9);
lean_ctor_set(x_3, 1, x_51);
goto _start;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_dec_eq(x_1, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_nat_sub(x_1, x_53);
lean_dec(x_1);
x_56 = lean_string_utf8_next_fast(x_2, x_9);
lean_dec(x_9);
lean_ctor_set(x_3, 1, x_56);
x_1 = x_55;
goto _start;
}
else
{
lean_object* x_58; 
lean_dec(x_1);
x_58 = lean_string_utf8_next(x_2, x_9);
lean_dec(x_9);
lean_ctor_set(x_3, 1, x_58);
return x_3;
}
}
}
else
{
uint32_t x_59; uint32_t x_60; uint8_t x_61; 
lean_dec(x_3);
x_59 = lean_string_utf8_get_fast(x_2, x_9);
x_60 = 47;
x_61 = lean_uint32_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_string_utf8_next_fast(x_2, x_9);
lean_dec(x_9);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_6);
x_3 = x_63;
goto _start;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_dec_eq(x_1, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_nat_sub(x_1, x_65);
lean_dec(x_1);
x_68 = lean_string_utf8_next_fast(x_2, x_9);
lean_dec(x_9);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_4);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_6);
x_1 = x_67;
x_3 = x_69;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_71 = lean_string_utf8_next(x_2, x_9);
lean_dec(x_9);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_6);
return x_72;
}
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_73 = l_Lean_ParseImports_finishCommentBlock_eoi(x_3);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_74 = l_Lean_ParseImports_finishCommentBlock_eoi(x_3);
return x_74;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_finishCommentBlock(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get_fast(x_2, x_5);
x_9 = lean_box_uint32(x_8);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_16 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_16);
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_6);
x_3 = x_19;
goto _start;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeUntil(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get_fast(x_2, x_5);
x_9 = lean_box_uint32(x_8);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_16 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_16);
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_6);
x_3 = x_19;
goto _start;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeWhile(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_apply_2(x_2, x_3, x_5);
return x_7;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_3(x_2, x_7, x_3, x_5);
return x_8;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = lean_string_utf8_get_fast(x_2, x_5);
x_9 = lean_uint32_dec_eq(x_8, x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_14);
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_6);
x_3 = x_17;
goto _start;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_3;
}
}
}
static lean_object* _init_l_Lean_ParseImports_whitespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tabs are not allowed; please configure your editor to expand them", 65, 65);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_whitespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_whitespace___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get_fast(x_1, x_4);
x_8 = 9;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 32;
x_11 = lean_uint32_dec_eq(x_7, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_7, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_7, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 45;
x_17 = lean_uint32_dec_eq(x_7, x_16);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 47;
x_19 = lean_uint32_dec_eq(x_7, x_18);
if (x_19 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_21 = lean_string_utf8_get(x_1, x_20);
x_22 = lean_uint32_dec_eq(x_21, x_16);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_23 = lean_string_utf8_next(x_1, x_20);
lean_dec(x_20);
x_24 = lean_string_utf8_get(x_1, x_23);
x_25 = lean_uint32_dec_eq(x_24, x_16);
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 33;
x_27 = lean_uint32_dec_eq(x_24, x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_2, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_2, 0);
lean_dec(x_31);
x_32 = lean_string_utf8_next(x_1, x_23);
lean_dec(x_23);
lean_ctor_set(x_2, 1, x_32);
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_ParseImports_finishCommentBlock(x_33, x_1, x_2);
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
x_2 = x_34;
goto _start;
}
else
{
lean_dec(x_35);
return x_34;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_37 = lean_string_utf8_next(x_1, x_23);
lean_dec(x_23);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_5);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_ParseImports_finishCommentBlock(x_39, x_1, x_38);
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
x_2 = x_40;
goto _start;
}
else
{
lean_dec(x_41);
return x_40;
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
}
}
}
else
{
lean_object* x_43; uint32_t x_44; uint8_t x_45; 
x_43 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_44 = lean_string_utf8_get(x_1, x_43);
x_45 = lean_uint32_dec_eq(x_44, x_16);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_2, 2);
lean_dec(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_2, 0);
lean_dec(x_49);
x_50 = lean_string_utf8_next(x_1, x_43);
lean_dec(x_43);
lean_ctor_set(x_2, 1, x_50);
x_51 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(x_14, x_1, x_2);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
x_2 = x_51;
goto _start;
}
else
{
lean_dec(x_52);
return x_51;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
x_54 = lean_string_utf8_next(x_1, x_43);
lean_dec(x_43);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_3);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_5);
x_56 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(x_14, x_1, x_55);
x_57 = lean_ctor_get(x_56, 2);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
x_2 = x_56;
goto _start;
}
else
{
lean_dec(x_57);
return x_56;
}
}
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_2, 2);
lean_dec(x_60);
x_61 = lean_ctor_get(x_2, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_2, 0);
lean_dec(x_62);
x_63 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_63);
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
x_65 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_5);
x_2 = x_66;
goto _start;
}
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_2);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_2, 2);
lean_dec(x_69);
x_70 = lean_ctor_get(x_2, 1);
lean_dec(x_70);
x_71 = lean_ctor_get(x_2, 0);
lean_dec(x_71);
x_72 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_72);
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_2);
x_74 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_3);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_5);
x_2 = x_75;
goto _start;
}
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_2, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_2, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_2, 0);
lean_dec(x_80);
x_81 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_81);
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_2);
x_83 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_3);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_5);
x_2 = x_84;
goto _start;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_5);
x_86 = !lean_is_exclusive(x_2);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_2, 2);
lean_dec(x_87);
x_88 = lean_ctor_get(x_2, 1);
lean_dec(x_88);
x_89 = lean_ctor_get(x_2, 0);
lean_dec(x_89);
x_90 = l_Lean_ParseImports_whitespace___closed__2;
lean_ctor_set(x_2, 2, x_90);
return x_2;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
x_91 = l_Lean_ParseImports_whitespace___closed__2;
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_3);
lean_ctor_set(x_92, 1, x_4);
lean_ctor_set(x_92, 2, x_91);
return x_92;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_whitespace(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec(x_3);
x_13 = lean_apply_2(x_2, x_4, x_5);
return x_13;
}
else
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
}
else
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_17 = lean_apply_2(x_2, x_4, x_5);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 1);
lean_dec(x_19);
lean_ctor_set(x_5, 1, x_7);
x_20 = l_Lean_ParseImports_whitespace(x_4, x_5);
x_21 = lean_apply_2(x_3, x_4, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_7);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lean_ParseImports_whitespace(x_4, x_24);
x_26 = lean_apply_2(x_3, x_4, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParseImports_keywordCore_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
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
x_8 = l_Lean_ParseImports_keywordCore_go(x_1, x_2, x_3, x_4, x_5, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` expected", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_3, x_6);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_string_utf8_get_fast(x_3, x_6);
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
x_12 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1;
x_13 = lean_string_append(x_12, x_1);
x_14 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_4, 2);
lean_dec(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_4, 2, x_18);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_24 = lean_string_utf8_next_fast(x_3, x_6);
lean_dec(x_6);
x_5 = x_23;
x_6 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_5);
x_26 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1;
x_27 = lean_string_append(x_26, x_1);
x_28 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_4, 2);
lean_dec(x_31);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_4, 2, x_32);
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_29);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_4, 1);
lean_dec(x_38);
lean_ctor_set(x_4, 1, x_6);
x_39 = l_Lean_ParseImports_whitespace(x_3, x_4);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_4);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_6);
lean_ctor_set(x_42, 2, x_41);
x_43 = l_Lean_ParseImports_whitespace(x_3, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1(x_1, x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_keyword(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_string_utf8_next(x_1, x_3);
x_9 = lean_string_utf8_at_end(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; lean_object* x_11; uint32_t x_20; uint8_t x_21; 
x_10 = lean_string_utf8_get_fast(x_1, x_8);
lean_dec(x_8);
x_20 = 65;
x_21 = lean_uint32_dec_le(x_20, x_10);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 97;
x_23 = lean_uint32_dec_le(x_22, x_10);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
x_11 = x_24;
goto block_19;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 122;
x_26 = lean_uint32_dec_le(x_10, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
x_11 = x_27;
goto block_19;
}
else
{
uint8_t x_28; 
x_28 = 1;
return x_28;
}
}
}
else
{
uint32_t x_29; uint8_t x_30; 
x_29 = 90;
x_30 = lean_uint32_dec_le(x_10, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; 
x_31 = 97;
x_32 = lean_uint32_dec_le(x_31, x_10);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_11 = x_33;
goto block_19;
}
else
{
uint32_t x_34; uint8_t x_35; 
x_34 = 122;
x_35 = lean_uint32_dec_le(x_10, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
x_11 = x_36;
goto block_19;
}
else
{
uint8_t x_37; 
x_37 = 1;
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = 1;
return x_38;
}
}
block_19:
{
uint32_t x_12; uint8_t x_13; 
lean_dec(x_11);
x_12 = 95;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_isLetterLike(x_10);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = l_Lean_idBeginEscape;
x_16 = lean_uint32_dec_eq(x_10, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
x_39 = 0;
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_ParseImports_isIdCont(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushModule(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*1, x_2);
x_7 = lean_array_push(x_5, x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_2);
x_12 = lean_array_push(x_8, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_ParseImports_State_pushModule(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 95;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 39;
x_5 = lean_uint32_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 33;
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 63;
x_9 = lean_uint32_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_isLetterLike(x_1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_isSubScriptAlnum(x_1);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
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
lean_object* x_2; lean_object* x_28; uint32_t x_37; uint8_t x_38; 
x_37 = 65;
x_38 = lean_uint32_dec_le(x_37, x_1);
if (x_38 == 0)
{
uint32_t x_39; uint8_t x_40; 
x_39 = 97;
x_40 = lean_uint32_dec_le(x_39, x_1);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
x_28 = x_41;
goto block_36;
}
else
{
uint32_t x_42; uint8_t x_43; 
x_42 = 122;
x_43 = lean_uint32_dec_le(x_1, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_box(0);
x_28 = x_44;
goto block_36;
}
else
{
uint8_t x_45; 
x_45 = 1;
return x_45;
}
}
}
else
{
uint32_t x_46; uint8_t x_47; 
x_46 = 90;
x_47 = lean_uint32_dec_le(x_1, x_46);
if (x_47 == 0)
{
uint32_t x_48; uint8_t x_49; 
x_48 = 97;
x_49 = lean_uint32_dec_le(x_48, x_1);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_28 = x_50;
goto block_36;
}
else
{
uint32_t x_51; uint8_t x_52; 
x_51 = 122;
x_52 = lean_uint32_dec_le(x_1, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_28 = x_53;
goto block_36;
}
else
{
uint8_t x_54; 
x_54 = 1;
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = 1;
return x_55;
}
}
block_27:
{
uint32_t x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = 46;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 10;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 32;
x_8 = lean_uint32_dec_eq(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 95;
x_10 = lean_uint32_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 39;
x_12 = lean_uint32_dec_eq(x_1, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 33;
x_14 = lean_uint32_dec_eq(x_1, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 63;
x_16 = lean_uint32_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_isLetterLike(x_1);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_isSubScriptAlnum(x_1);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = 1;
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = 1;
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
block_36:
{
uint32_t x_29; uint8_t x_30; 
lean_dec(x_28);
x_29 = 48;
x_30 = lean_uint32_dec_le(x_29, x_1);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_box(0);
x_2 = x_31;
goto block_27;
}
else
{
uint32_t x_32; uint8_t x_33; 
x_32 = 57;
x_33 = lean_uint32_dec_le(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_2 = x_34;
goto block_27;
}
else
{
uint8_t x_35; 
x_35 = 1;
return x_35;
}
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_15 = lean_string_utf8_at_end(x_1, x_3);
if (x_15 == 0)
{
uint32_t x_16; lean_object* x_17; lean_object* x_41; uint32_t x_50; uint8_t x_51; 
x_16 = lean_string_utf8_get_fast(x_1, x_3);
x_50 = 65;
x_51 = lean_uint32_dec_le(x_50, x_16);
if (x_51 == 0)
{
uint32_t x_52; uint8_t x_53; 
x_52 = 97;
x_53 = lean_uint32_dec_le(x_52, x_16);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_41 = x_54;
goto block_49;
}
else
{
uint32_t x_55; uint8_t x_56; 
x_55 = 122;
x_56 = lean_uint32_dec_le(x_16, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_41 = x_57;
goto block_49;
}
else
{
lean_object* x_58; 
x_58 = lean_box(0);
x_4 = x_58;
goto block_14;
}
}
}
else
{
uint32_t x_59; uint8_t x_60; 
x_59 = 90;
x_60 = lean_uint32_dec_le(x_16, x_59);
if (x_60 == 0)
{
uint32_t x_61; uint8_t x_62; 
x_61 = 97;
x_62 = lean_uint32_dec_le(x_61, x_16);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_box(0);
x_41 = x_63;
goto block_49;
}
else
{
uint32_t x_64; uint8_t x_65; 
x_64 = 122;
x_65 = lean_uint32_dec_le(x_16, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_box(0);
x_41 = x_66;
goto block_49;
}
else
{
lean_object* x_67; 
x_67 = lean_box(0);
x_4 = x_67;
goto block_14;
}
}
}
else
{
lean_object* x_68; 
x_68 = lean_box(0);
x_4 = x_68;
goto block_14;
}
}
block_40:
{
uint32_t x_18; uint8_t x_19; 
lean_dec(x_17);
x_18 = 46;
x_19 = lean_uint32_dec_eq(x_16, x_18);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 10;
x_21 = lean_uint32_dec_eq(x_16, x_20);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 32;
x_23 = lean_uint32_dec_eq(x_16, x_22);
if (x_23 == 0)
{
uint32_t x_24; uint8_t x_25; 
x_24 = 95;
x_25 = lean_uint32_dec_eq(x_16, x_24);
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 39;
x_27 = lean_uint32_dec_eq(x_16, x_26);
if (x_27 == 0)
{
uint32_t x_28; uint8_t x_29; 
x_28 = 33;
x_29 = lean_uint32_dec_eq(x_16, x_28);
if (x_29 == 0)
{
uint32_t x_30; uint8_t x_31; 
x_30 = 63;
x_31 = lean_uint32_dec_eq(x_16, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_isLetterLike(x_16);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_isSubScriptAlnum(x_16);
if (x_33 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_34; 
x_34 = lean_box(0);
x_4 = x_34;
goto block_14;
}
}
else
{
lean_object* x_35; 
x_35 = lean_box(0);
x_4 = x_35;
goto block_14;
}
}
else
{
lean_object* x_36; 
x_36 = lean_box(0);
x_4 = x_36;
goto block_14;
}
}
else
{
lean_object* x_37; 
x_37 = lean_box(0);
x_4 = x_37;
goto block_14;
}
}
else
{
lean_object* x_38; 
x_38 = lean_box(0);
x_4 = x_38;
goto block_14;
}
}
else
{
lean_object* x_39; 
x_39 = lean_box(0);
x_4 = x_39;
goto block_14;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
block_49:
{
uint32_t x_42; uint8_t x_43; 
lean_dec(x_41);
x_42 = 48;
x_43 = lean_uint32_dec_le(x_42, x_16);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_box(0);
x_17 = x_44;
goto block_40;
}
else
{
uint32_t x_45; uint8_t x_46; 
x_45 = 57;
x_46 = lean_uint32_dec_le(x_16, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_17 = x_47;
goto block_40;
}
else
{
lean_object* x_48; 
x_48 = lean_box(0);
x_4 = x_48;
goto block_14;
}
}
}
}
else
{
lean_dec(x_3);
return x_2;
}
block_14:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_6);
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_11);
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get_fast(x_1, x_4);
x_8 = l_Lean_idEndEscape;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_14);
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_5);
x_2 = x_17;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
}
static lean_object* _init_l_Lean_ParseImports_moduleIdent_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected identifier", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_moduleIdent_parse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_moduleIdent_parse___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParseImports_moduleIdent_parse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unterminated identifier escape", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_moduleIdent_parse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_moduleIdent_parse___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_string_utf8_at_end(x_2, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint32_t x_70; lean_object* x_71; uint32_t x_80; uint8_t x_81; 
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_9 = x_4;
} else {
 lean_dec_ref(x_4);
 x_9 = lean_box(0);
}
x_70 = lean_string_utf8_get_fast(x_2, x_6);
x_80 = l_Lean_idBeginEscape;
x_81 = lean_uint32_dec_eq(x_70, x_80);
if (x_81 == 0)
{
uint32_t x_82; uint8_t x_83; 
x_82 = 65;
x_83 = lean_uint32_dec_le(x_82, x_70);
if (x_83 == 0)
{
uint32_t x_84; uint8_t x_85; 
x_84 = 97;
x_85 = lean_uint32_dec_le(x_84, x_70);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_box(0);
x_71 = x_86;
goto block_79;
}
else
{
uint32_t x_87; uint8_t x_88; 
x_87 = 122;
x_88 = lean_uint32_dec_le(x_70, x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_box(0);
x_71 = x_89;
goto block_79;
}
else
{
lean_object* x_90; 
x_90 = lean_box(0);
x_10 = x_90;
goto block_69;
}
}
}
else
{
uint32_t x_91; uint8_t x_92; 
x_91 = 90;
x_92 = lean_uint32_dec_le(x_70, x_91);
if (x_92 == 0)
{
uint32_t x_93; uint8_t x_94; 
x_93 = 97;
x_94 = lean_uint32_dec_le(x_93, x_70);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_box(0);
x_71 = x_95;
goto block_79;
}
else
{
uint32_t x_96; uint8_t x_97; 
x_96 = 122;
x_97 = lean_uint32_dec_le(x_70, x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_box(0);
x_71 = x_98;
goto block_79;
}
else
{
lean_object* x_99; 
x_99 = lean_box(0);
x_10 = x_99;
goto block_69;
}
}
}
else
{
lean_object* x_100; 
x_100 = lean_box(0);
x_10 = x_100;
goto block_69;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_9);
x_101 = lean_string_utf8_next_fast(x_2, x_6);
lean_dec(x_6);
lean_inc(x_101);
x_102 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_102, 0, x_5);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_7);
x_103 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(x_2, x_102);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_ctor_get(x_103, 1);
x_107 = lean_ctor_get(x_103, 2);
x_108 = lean_string_utf8_at_end(x_2, x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint32_t x_117; uint32_t x_118; uint8_t x_119; 
x_109 = lean_string_utf8_next_fast(x_2, x_106);
lean_inc(x_107);
lean_inc(x_109);
lean_inc(x_105);
lean_ctor_set(x_103, 1, x_109);
x_110 = lean_string_utf8_extract(x_2, x_101, x_106);
lean_dec(x_106);
lean_dec(x_101);
x_111 = l_Lean_Name_str___override(x_3, x_110);
x_117 = lean_string_utf8_get(x_2, x_109);
x_118 = 46;
x_119 = lean_uint32_dec_eq(x_117, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_105);
x_120 = l_Lean_ParseImports_State_pushModule(x_111, x_1, x_103);
x_121 = l_Lean_ParseImports_whitespace(x_2, x_120);
return x_121;
}
else
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_string_utf8_next(x_2, x_109);
x_123 = lean_string_utf8_at_end(x_2, x_122);
if (x_123 == 0)
{
uint32_t x_124; lean_object* x_125; uint32_t x_136; uint8_t x_137; 
x_124 = lean_string_utf8_get_fast(x_2, x_122);
lean_dec(x_122);
x_136 = 65;
x_137 = lean_uint32_dec_le(x_136, x_124);
if (x_137 == 0)
{
uint32_t x_138; uint8_t x_139; 
x_138 = 97;
x_139 = lean_uint32_dec_le(x_138, x_124);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_box(0);
x_125 = x_140;
goto block_135;
}
else
{
uint32_t x_141; uint8_t x_142; 
x_141 = 122;
x_142 = lean_uint32_dec_le(x_124, x_141);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_box(0);
x_125 = x_143;
goto block_135;
}
else
{
lean_object* x_144; 
lean_dec(x_103);
x_144 = lean_box(0);
x_112 = x_144;
goto block_116;
}
}
}
else
{
uint32_t x_145; uint8_t x_146; 
x_145 = 90;
x_146 = lean_uint32_dec_le(x_124, x_145);
if (x_146 == 0)
{
uint32_t x_147; uint8_t x_148; 
x_147 = 97;
x_148 = lean_uint32_dec_le(x_147, x_124);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_125 = x_149;
goto block_135;
}
else
{
uint32_t x_150; uint8_t x_151; 
x_150 = 122;
x_151 = lean_uint32_dec_le(x_124, x_150);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_box(0);
x_125 = x_152;
goto block_135;
}
else
{
lean_object* x_153; 
lean_dec(x_103);
x_153 = lean_box(0);
x_112 = x_153;
goto block_116;
}
}
}
else
{
lean_object* x_154; 
lean_dec(x_103);
x_154 = lean_box(0);
x_112 = x_154;
goto block_116;
}
}
block_135:
{
uint32_t x_126; uint8_t x_127; 
lean_dec(x_125);
x_126 = 95;
x_127 = lean_uint32_dec_eq(x_124, x_126);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_isLetterLike(x_124);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = lean_uint32_dec_eq(x_124, x_80);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_105);
x_130 = l_Lean_ParseImports_State_pushModule(x_111, x_1, x_103);
x_131 = l_Lean_ParseImports_whitespace(x_2, x_130);
return x_131;
}
else
{
lean_object* x_132; 
lean_dec(x_103);
x_132 = lean_box(0);
x_112 = x_132;
goto block_116;
}
}
else
{
lean_object* x_133; 
lean_dec(x_103);
x_133 = lean_box(0);
x_112 = x_133;
goto block_116;
}
}
else
{
lean_object* x_134; 
lean_dec(x_103);
x_134 = lean_box(0);
x_112 = x_134;
goto block_116;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_122);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_105);
x_155 = l_Lean_ParseImports_State_pushModule(x_111, x_1, x_103);
x_156 = l_Lean_ParseImports_whitespace(x_2, x_155);
return x_156;
}
}
block_116:
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_112);
x_113 = lean_string_utf8_next(x_2, x_109);
lean_dec(x_109);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_107);
x_3 = x_111;
x_4 = x_114;
goto _start;
}
}
else
{
lean_object* x_157; 
lean_dec(x_107);
lean_dec(x_101);
lean_dec(x_3);
x_157 = l_Lean_ParseImports_moduleIdent_parse___closed__4;
lean_ctor_set(x_103, 2, x_157);
return x_103;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_158 = lean_ctor_get(x_103, 0);
x_159 = lean_ctor_get(x_103, 1);
x_160 = lean_ctor_get(x_103, 2);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_103);
x_161 = lean_string_utf8_at_end(x_2, x_159);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint32_t x_171; uint32_t x_172; uint8_t x_173; 
x_162 = lean_string_utf8_next_fast(x_2, x_159);
lean_inc(x_160);
lean_inc(x_162);
lean_inc(x_158);
x_163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_163, 0, x_158);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_160);
x_164 = lean_string_utf8_extract(x_2, x_101, x_159);
lean_dec(x_159);
lean_dec(x_101);
x_165 = l_Lean_Name_str___override(x_3, x_164);
x_171 = lean_string_utf8_get(x_2, x_162);
x_172 = 46;
x_173 = lean_uint32_dec_eq(x_171, x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_158);
x_174 = l_Lean_ParseImports_State_pushModule(x_165, x_1, x_163);
x_175 = l_Lean_ParseImports_whitespace(x_2, x_174);
return x_175;
}
else
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_string_utf8_next(x_2, x_162);
x_177 = lean_string_utf8_at_end(x_2, x_176);
if (x_177 == 0)
{
uint32_t x_178; lean_object* x_179; uint32_t x_190; uint8_t x_191; 
x_178 = lean_string_utf8_get_fast(x_2, x_176);
lean_dec(x_176);
x_190 = 65;
x_191 = lean_uint32_dec_le(x_190, x_178);
if (x_191 == 0)
{
uint32_t x_192; uint8_t x_193; 
x_192 = 97;
x_193 = lean_uint32_dec_le(x_192, x_178);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_box(0);
x_179 = x_194;
goto block_189;
}
else
{
uint32_t x_195; uint8_t x_196; 
x_195 = 122;
x_196 = lean_uint32_dec_le(x_178, x_195);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_box(0);
x_179 = x_197;
goto block_189;
}
else
{
lean_object* x_198; 
lean_dec(x_163);
x_198 = lean_box(0);
x_166 = x_198;
goto block_170;
}
}
}
else
{
uint32_t x_199; uint8_t x_200; 
x_199 = 90;
x_200 = lean_uint32_dec_le(x_178, x_199);
if (x_200 == 0)
{
uint32_t x_201; uint8_t x_202; 
x_201 = 97;
x_202 = lean_uint32_dec_le(x_201, x_178);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_box(0);
x_179 = x_203;
goto block_189;
}
else
{
uint32_t x_204; uint8_t x_205; 
x_204 = 122;
x_205 = lean_uint32_dec_le(x_178, x_204);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_box(0);
x_179 = x_206;
goto block_189;
}
else
{
lean_object* x_207; 
lean_dec(x_163);
x_207 = lean_box(0);
x_166 = x_207;
goto block_170;
}
}
}
else
{
lean_object* x_208; 
lean_dec(x_163);
x_208 = lean_box(0);
x_166 = x_208;
goto block_170;
}
}
block_189:
{
uint32_t x_180; uint8_t x_181; 
lean_dec(x_179);
x_180 = 95;
x_181 = lean_uint32_dec_eq(x_178, x_180);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = l_Lean_isLetterLike(x_178);
if (x_182 == 0)
{
uint8_t x_183; 
x_183 = lean_uint32_dec_eq(x_178, x_80);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_158);
x_184 = l_Lean_ParseImports_State_pushModule(x_165, x_1, x_163);
x_185 = l_Lean_ParseImports_whitespace(x_2, x_184);
return x_185;
}
else
{
lean_object* x_186; 
lean_dec(x_163);
x_186 = lean_box(0);
x_166 = x_186;
goto block_170;
}
}
else
{
lean_object* x_187; 
lean_dec(x_163);
x_187 = lean_box(0);
x_166 = x_187;
goto block_170;
}
}
else
{
lean_object* x_188; 
lean_dec(x_163);
x_188 = lean_box(0);
x_166 = x_188;
goto block_170;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_176);
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_158);
x_209 = l_Lean_ParseImports_State_pushModule(x_165, x_1, x_163);
x_210 = l_Lean_ParseImports_whitespace(x_2, x_209);
return x_210;
}
}
block_170:
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_166);
x_167 = lean_string_utf8_next(x_2, x_162);
lean_dec(x_162);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_158);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_168, 2, x_160);
x_3 = x_165;
x_4 = x_168;
goto _start;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_160);
lean_dec(x_101);
lean_dec(x_3);
x_211 = l_Lean_ParseImports_moduleIdent_parse___closed__4;
x_212 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_212, 0, x_158);
lean_ctor_set(x_212, 1, x_159);
lean_ctor_set(x_212, 2, x_211);
return x_212;
}
}
}
block_69:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_28; uint32_t x_29; uint8_t x_30; 
lean_dec(x_10);
x_11 = lean_string_utf8_next_fast(x_2, x_6);
if (lean_is_scalar(x_9)) {
 x_12 = lean_alloc_ctor(0, 3, 0);
} else {
 x_12 = x_9;
}
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_7);
x_13 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(x_2, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_string_utf8_extract(x_2, x_6, x_14);
lean_dec(x_6);
x_16 = l_Lean_Name_str___override(x_3, x_15);
x_28 = lean_string_utf8_get(x_2, x_14);
x_29 = 46;
x_30 = lean_uint32_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_14);
x_31 = l_Lean_ParseImports_State_pushModule(x_16, x_1, x_13);
x_32 = l_Lean_ParseImports_whitespace(x_2, x_31);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_string_utf8_next(x_2, x_14);
x_34 = lean_string_utf8_at_end(x_2, x_33);
if (x_34 == 0)
{
uint32_t x_35; lean_object* x_36; uint32_t x_48; uint8_t x_49; 
x_35 = lean_string_utf8_get_fast(x_2, x_33);
lean_dec(x_33);
x_48 = 65;
x_49 = lean_uint32_dec_le(x_48, x_35);
if (x_49 == 0)
{
uint32_t x_50; uint8_t x_51; 
x_50 = 97;
x_51 = lean_uint32_dec_le(x_50, x_35);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
x_36 = x_52;
goto block_47;
}
else
{
uint32_t x_53; uint8_t x_54; 
x_53 = 122;
x_54 = lean_uint32_dec_le(x_35, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_box(0);
x_36 = x_55;
goto block_47;
}
else
{
lean_object* x_56; 
x_56 = lean_box(0);
x_17 = x_56;
goto block_27;
}
}
}
else
{
uint32_t x_57; uint8_t x_58; 
x_57 = 90;
x_58 = lean_uint32_dec_le(x_35, x_57);
if (x_58 == 0)
{
uint32_t x_59; uint8_t x_60; 
x_59 = 97;
x_60 = lean_uint32_dec_le(x_59, x_35);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_box(0);
x_36 = x_61;
goto block_47;
}
else
{
uint32_t x_62; uint8_t x_63; 
x_62 = 122;
x_63 = lean_uint32_dec_le(x_35, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_box(0);
x_36 = x_64;
goto block_47;
}
else
{
lean_object* x_65; 
x_65 = lean_box(0);
x_17 = x_65;
goto block_27;
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_box(0);
x_17 = x_66;
goto block_27;
}
}
block_47:
{
uint32_t x_37; uint8_t x_38; 
lean_dec(x_36);
x_37 = 95;
x_38 = lean_uint32_dec_eq(x_35, x_37);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_isLetterLike(x_35);
if (x_39 == 0)
{
uint32_t x_40; uint8_t x_41; 
x_40 = l_Lean_idBeginEscape;
x_41 = lean_uint32_dec_eq(x_35, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_14);
x_42 = l_Lean_ParseImports_State_pushModule(x_16, x_1, x_13);
x_43 = l_Lean_ParseImports_whitespace(x_2, x_42);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_box(0);
x_17 = x_44;
goto block_27;
}
}
else
{
lean_object* x_45; 
x_45 = lean_box(0);
x_17 = x_45;
goto block_27;
}
}
else
{
lean_object* x_46; 
x_46 = lean_box(0);
x_17 = x_46;
goto block_27;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_33);
lean_dec(x_14);
x_67 = l_Lean_ParseImports_State_pushModule(x_16, x_1, x_13);
x_68 = l_Lean_ParseImports_whitespace(x_2, x_67);
return x_68;
}
}
block_27:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_17);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_string_utf8_next(x_2, x_14);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
lean_ctor_set(x_13, 1, x_19);
x_3 = x_16;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_13, 2);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_24);
x_3 = x_16;
x_4 = x_25;
goto _start;
}
}
}
block_79:
{
uint32_t x_72; uint8_t x_73; 
lean_dec(x_71);
x_72 = 95;
x_73 = lean_uint32_dec_eq(x_70, x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_isLetterLike(x_70);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
x_75 = l_Lean_ParseImports_moduleIdent_parse___closed__2;
x_76 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_76, 0, x_5);
lean_ctor_set(x_76, 1, x_6);
lean_ctor_set(x_76, 2, x_75);
return x_76;
}
else
{
lean_object* x_77; 
x_77 = lean_box(0);
x_10 = x_77;
goto block_69;
}
}
else
{
lean_object* x_78; 
x_78 = lean_box(0);
x_10 = x_78;
goto block_69;
}
}
}
else
{
lean_object* x_213; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_213 = l_Lean_ParseImports_State_mkEOIError(x_4);
return x_213;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_ParseImports_moduleIdent_parse(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_ParseImports_moduleIdent_parse(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParseImports_moduleIdent(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_array_get_size(x_4);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Array_shrink___rarg(x_14, x_6);
lean_dec(x_6);
x_16 = lean_box(0);
lean_ctor_set(x_3, 2, x_16);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Array_shrink___rarg(x_19, x_6);
lean_dec(x_6);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2;
x_12 = 0;
x_13 = l_Lean_ParseImports_State_pushModule(x_11, x_12, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_15 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_14;
x_5 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2;
x_18 = 0;
x_19 = l_Lean_ParseImports_State_pushModule(x_17, x_18, x_3);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
lean_ctor_set(x_3, 1, x_5);
x_22 = l_Lean_ParseImports_whitespace(x_2, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Lean_ParseImports_whitespace(x_2, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_preludeOpt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_preludeOpt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_preludeOpt(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1;
x_2 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2;
x_2 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 2);
lean_dec(x_12);
x_13 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
lean_ctor_set(x_3, 2, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_19 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 2);
lean_dec(x_22);
x_23 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
lean_ctor_set(x_3, 2, x_23);
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_3, 1);
lean_dec(x_29);
lean_ctor_set(x_3, 1, x_5);
x_30 = l_Lean_ParseImports_whitespace(x_2, x_3);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_3);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_32);
x_34 = l_Lean_ParseImports_whitespace(x_2, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Lean_ParseImports_moduleIdent_parse(x_11, x_2, x_12, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_15 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_14;
x_5 = x_15;
goto _start;
}
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Lean_ParseImports_moduleIdent_parse(x_17, x_2, x_18, x_3);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
lean_ctor_set(x_3, 1, x_5);
x_22 = l_Lean_ParseImports_whitespace(x_2, x_3);
x_23 = 1;
x_24 = lean_box(0);
x_25 = l_Lean_ParseImports_moduleIdent_parse(x_23, x_2, x_24, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Lean_ParseImports_whitespace(x_2, x_28);
x_30 = 1;
x_31 = lean_box(0);
x_32 = l_Lean_ParseImports_moduleIdent_parse(x_30, x_2, x_31, x_29);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_array_get_size(x_4);
lean_dec(x_4);
x_7 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1;
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_8 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(x_7, x_2, x_3, x_1, x_5);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1;
lean_inc(x_1);
x_16 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(x_15, x_2, x_8, x_1, x_14);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_1);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Array_shrink___rarg(x_19, x_6);
lean_dec(x_6);
x_21 = lean_box(0);
lean_ctor_set(x_3, 2, x_21);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_1);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = l_Array_shrink___rarg(x_22, x_6);
lean_dec(x_6);
x_24 = lean_box(0);
lean_ctor_set(x_3, 2, x_24);
lean_ctor_set(x_3, 0, x_23);
return x_3;
}
}
else
{
lean_object* x_25; 
lean_dec(x_3);
x_25 = lean_ctor_get(x_8, 2);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
x_27 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1;
lean_inc(x_1);
x_28 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(x_27, x_2, x_8, x_1, x_26);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_1);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Array_shrink___rarg(x_31, x_6);
lean_dec(x_6);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_5);
lean_ctor_set(x_34, 2, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
lean_dec(x_1);
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
lean_dec(x_8);
x_36 = l_Array_shrink___rarg(x_35, x_6);
lean_dec(x_6);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_5);
lean_ctor_set(x_38, 2, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_ParseImports_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("prelude", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_ParseImports_main___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(x_4, x_1, x_2, x_5, x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(x_5, x_1, x_6);
return x_8;
}
else
{
lean_dec(x_7);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_parseImports_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_parseImports_x27___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_ParseImports_instInhabitedState___closed__1;
x_5 = l_Lean_ParseImports_whitespace(x_1, x_4);
x_6 = l_Lean_ParseImports_main(x_1, x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = l_Lean_parseImports_x27___closed__1;
x_13 = lean_string_append(x_12, x_2);
x_14 = l_Lean_parseImports_x27___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_11);
lean_dec(x_11);
x_17 = lean_string_append(x_16, x_12);
lean_ctor_set_tag(x_7, 18);
lean_ctor_set(x_7, 0, x_17);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Lean_parseImports_x27___closed__1;
x_21 = lean_string_append(x_20, x_2);
x_22 = l_Lean_parseImports_x27___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_19);
lean_dec(x_19);
x_25 = lean_string_append(x_24, x_20);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_parseImports_x27(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtimeOnly", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__1;
x_5 = l_Lean_Name_toString(x_2, x_3, x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_12, 0, x_11);
x_13 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_ParseImports_State_imports___default___closed__1;
x_19 = l_List_bindTR_go___at___private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173____spec__1(x_17, x_18);
x_20 = l_Lean_Json_mkObj(x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToJsonImport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToJsonImport() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToJsonImport___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_PrintImportResult_imports_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrintImportResult_errors___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ParseImports_State_imports___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380_(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_array_size(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__2(x_6, x_7, x_5);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 0, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_array_size(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__2(x_13, x_14, x_12);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imports", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("errors", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__1;
x_4 = l_Lean_Json_opt___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__1(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_size(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__3(x_6, x_7, x_5);
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_ParseImports_State_imports___default___closed__1;
x_17 = l_List_bindTR_go___at___private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173____spec__1(x_15, x_16);
x_18 = l_Lean_Json_mkObj(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____spec__3(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToJsonPrintImportResult___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1519____spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464_(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1519_(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_array_size(x_1);
x_3 = 0;
x_4 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1519____spec__1(x_2, x_3, x_1);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_ParseImports_State_imports___default___closed__1;
x_12 = l_List_bindTR_go___at___private_Lean_Server_Rpc_Basic_0__Lean_Lsp_toJsonRpcRef____x40_Lean_Server_Rpc_Basic___hyg_173____spec__1(x_10, x_11);
x_13 = l_Lean_Json_mkObj(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1519____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1519____spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportsResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1519_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportsResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToJsonPrintImportsResult___closed__1;
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = l_IO_FS_readFile(x_7, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_parseImports_x27(x_11, x_7, x_12);
lean_dec(x_7);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = l_Lean_ParseImports_State_imports___default___closed__1;
lean_ctor_set(x_13, 1, x_18);
lean_ctor_set(x_13, 0, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_9, x_2, x_13);
x_2 = x_20;
x_3 = x_21;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_Lean_ParseImports_State_imports___default___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = 1;
x_29 = lean_usize_add(x_2, x_28);
x_30 = lean_array_uset(x_9, x_2, x_27);
x_2 = x_29;
x_3 = x_30;
x_4 = x_24;
goto _start;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
x_35 = lean_box(0);
x_36 = lean_io_error_to_string(x_33);
x_37 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
x_38 = lean_array_push(x_37, x_36);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 1, x_38);
lean_ctor_set(x_13, 0, x_35);
x_39 = 1;
x_40 = lean_usize_add(x_2, x_39);
x_41 = lean_array_uset(x_9, x_2, x_13);
x_2 = x_40;
x_3 = x_41;
x_4 = x_34;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_box(0);
x_46 = lean_io_error_to_string(x_43);
x_47 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
x_48 = lean_array_push(x_47, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = 1;
x_51 = lean_usize_add(x_2, x_50);
x_52 = lean_array_uset(x_9, x_2, x_49);
x_2 = x_51;
x_3 = x_52;
x_4 = x_44;
goto _start;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_10);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_10, 0);
x_56 = lean_ctor_get(x_10, 1);
x_57 = lean_box(0);
x_58 = lean_io_error_to_string(x_55);
x_59 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
x_60 = lean_array_push(x_59, x_58);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_60);
lean_ctor_set(x_10, 0, x_57);
x_61 = 1;
x_62 = lean_usize_add(x_2, x_61);
x_63 = lean_array_uset(x_9, x_2, x_10);
x_2 = x_62;
x_3 = x_63;
x_4 = x_56;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_67 = lean_box(0);
x_68 = lean_io_error_to_string(x_65);
x_69 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
x_70 = lean_array_push(x_69, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = 1;
x_73 = lean_usize_add(x_2, x_72);
x_74 = lean_array_uset(x_9, x_2, x_71);
x_2 = x_73;
x_3 = x_74;
x_4 = x_66;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_print_imports_json(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1(x_3, x_4, x_1, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1519_(x_6);
x_9 = l_Lean_Json_compress(x_8);
x_10 = l_IO_println___at_Lean_instEval___spec__1(x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1(x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ParseImports_State_imports___default___closed__1 = _init_l_Lean_ParseImports_State_imports___default___closed__1();
lean_mark_persistent(l_Lean_ParseImports_State_imports___default___closed__1);
l_Lean_ParseImports_State_imports___default = _init_l_Lean_ParseImports_State_imports___default();
lean_mark_persistent(l_Lean_ParseImports_State_imports___default);
l_Lean_ParseImports_State_pos___default = _init_l_Lean_ParseImports_State_pos___default();
lean_mark_persistent(l_Lean_ParseImports_State_pos___default);
l_Lean_ParseImports_State_error_x3f___default = _init_l_Lean_ParseImports_State_error_x3f___default();
lean_mark_persistent(l_Lean_ParseImports_State_error_x3f___default);
l_Lean_ParseImports_instInhabitedState___closed__1 = _init_l_Lean_ParseImports_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_ParseImports_instInhabitedState___closed__1);
l_Lean_ParseImports_instInhabitedState = _init_l_Lean_ParseImports_instInhabitedState();
lean_mark_persistent(l_Lean_ParseImports_instInhabitedState);
l_Lean_ParseImports_State_mkEOIError___closed__1 = _init_l_Lean_ParseImports_State_mkEOIError___closed__1();
lean_mark_persistent(l_Lean_ParseImports_State_mkEOIError___closed__1);
l_Lean_ParseImports_State_mkEOIError___closed__2 = _init_l_Lean_ParseImports_State_mkEOIError___closed__2();
lean_mark_persistent(l_Lean_ParseImports_State_mkEOIError___closed__2);
l_Lean_ParseImports_finishCommentBlock_eoi___closed__1 = _init_l_Lean_ParseImports_finishCommentBlock_eoi___closed__1();
lean_mark_persistent(l_Lean_ParseImports_finishCommentBlock_eoi___closed__1);
l_Lean_ParseImports_finishCommentBlock_eoi___closed__2 = _init_l_Lean_ParseImports_finishCommentBlock_eoi___closed__2();
lean_mark_persistent(l_Lean_ParseImports_finishCommentBlock_eoi___closed__2);
l_Lean_ParseImports_whitespace___closed__1 = _init_l_Lean_ParseImports_whitespace___closed__1();
lean_mark_persistent(l_Lean_ParseImports_whitespace___closed__1);
l_Lean_ParseImports_whitespace___closed__2 = _init_l_Lean_ParseImports_whitespace___closed__2();
lean_mark_persistent(l_Lean_ParseImports_whitespace___closed__2);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2);
l_Lean_ParseImports_moduleIdent_parse___closed__1 = _init_l_Lean_ParseImports_moduleIdent_parse___closed__1();
lean_mark_persistent(l_Lean_ParseImports_moduleIdent_parse___closed__1);
l_Lean_ParseImports_moduleIdent_parse___closed__2 = _init_l_Lean_ParseImports_moduleIdent_parse___closed__2();
lean_mark_persistent(l_Lean_ParseImports_moduleIdent_parse___closed__2);
l_Lean_ParseImports_moduleIdent_parse___closed__3 = _init_l_Lean_ParseImports_moduleIdent_parse___closed__3();
lean_mark_persistent(l_Lean_ParseImports_moduleIdent_parse___closed__3);
l_Lean_ParseImports_moduleIdent_parse___closed__4 = _init_l_Lean_ParseImports_moduleIdent_parse___closed__4();
lean_mark_persistent(l_Lean_ParseImports_moduleIdent_parse___closed__4);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4);
l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1 = _init_l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1();
lean_mark_persistent(l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1);
l_Lean_ParseImports_main___closed__1 = _init_l_Lean_ParseImports_main___closed__1();
lean_mark_persistent(l_Lean_ParseImports_main___closed__1);
l_Lean_parseImports_x27___closed__1 = _init_l_Lean_parseImports_x27___closed__1();
lean_mark_persistent(l_Lean_parseImports_x27___closed__1);
l_Lean_parseImports_x27___closed__2 = _init_l_Lean_parseImports_x27___closed__2();
lean_mark_persistent(l_Lean_parseImports_x27___closed__2);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__1 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__1();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__1);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__2 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__2();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__2);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__3 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__3();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1380____closed__3);
l_Lean_instToJsonImport___closed__1 = _init_l_Lean_instToJsonImport___closed__1();
lean_mark_persistent(l_Lean_instToJsonImport___closed__1);
l_Lean_instToJsonImport = _init_l_Lean_instToJsonImport();
lean_mark_persistent(l_Lean_instToJsonImport);
l_Lean_PrintImportResult_imports_x3f___default = _init_l_Lean_PrintImportResult_imports_x3f___default();
lean_mark_persistent(l_Lean_PrintImportResult_imports_x3f___default);
l_Lean_PrintImportResult_errors___default = _init_l_Lean_PrintImportResult_errors___default();
lean_mark_persistent(l_Lean_PrintImportResult_errors___default);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__1 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__1();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__1);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__2 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__2();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1464____closed__2);
l_Lean_instToJsonPrintImportResult___closed__1 = _init_l_Lean_instToJsonPrintImportResult___closed__1();
lean_mark_persistent(l_Lean_instToJsonPrintImportResult___closed__1);
l_Lean_instToJsonPrintImportResult = _init_l_Lean_instToJsonPrintImportResult();
lean_mark_persistent(l_Lean_instToJsonPrintImportResult);
l_Lean_instToJsonPrintImportsResult___closed__1 = _init_l_Lean_instToJsonPrintImportsResult___closed__1();
lean_mark_persistent(l_Lean_instToJsonPrintImportsResult___closed__1);
l_Lean_instToJsonPrintImportsResult = _init_l_Lean_instToJsonPrintImportsResult();
lean_mark_persistent(l_Lean_instToJsonPrintImportsResult);
l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
