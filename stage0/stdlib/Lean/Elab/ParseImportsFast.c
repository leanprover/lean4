// Lean compiler output
// Module: Lean.Elab.ParseImportsFast
// Imports: Init Lean.Parser.Module
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
lean_object* l_List_join___rarg(lean_object*);
static lean_object* l_Lean_ParseImports_State_imports___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718_(lean_object*);
static lean_object* l_Lean_ParseImports_finishCommentBlock_eoi___closed__2;
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__2;
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2;
static lean_object* l_Lean_ParseImports_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pos___default;
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_error_x3f___default;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushModule___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_parseImports_x27___closed__1;
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil(lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isAlphanum(uint32_t);
uint8_t l_Char_isWhitespace(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___rarg(lean_object*);
static lean_object* l_Lean_ParseImports_whitespace___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_preludeOpt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__2;
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2;
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__4;
static lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1;
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1799_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1;
static lean_object* l_Lean_ParseImports_main___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628_(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_many(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_State_mkEOIError___closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1799____spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object*);
static lean_object* l_Lean_ParseImports_State_mkEOIError___closed__1;
static lean_object* l_Lean_parseImports_x27___closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToJsonImport___closed__1;
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__3;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock_eoi(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrintImportResult_imports_x3f___default;
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrintImportResult_errors___default;
static lean_object* l_Lean_ParseImports_whitespace___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_instToJsonPrintImportResult___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult;
LEAN_EXPORT lean_object* l_Lean_ParseImports_preludeOpt___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1799____spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushModule(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t);
static lean_object* l_Lean_ParseImports_finishCommentBlock_eoi___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToJsonPrintImportsResult___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_imports___default;
LEAN_EXPORT lean_object* l_Lean_instToJsonImport;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
uint8_t l_Lean_isIdFirst(uint32_t);
LEAN_EXPORT lean_object* lean_print_imports_json(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object*, lean_object*);
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
x_1 = lean_mk_string_from_bytes("unexpected end of input", 23);
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
x_1 = lean_mk_string_from_bytes("unterminated comment", 20);
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = 10;
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
static lean_object* _init_l_Lean_ParseImports_whitespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tabs are not allowed; please configure your editor to expand them", 65);
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
uint8_t x_10; 
x_10 = l_Char_isWhitespace(x_7);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 45;
x_12 = lean_uint32_dec_eq(x_7, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 47;
x_14 = lean_uint32_dec_eq(x_7, x_13);
if (x_14 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_16 = lean_string_utf8_get(x_1, x_15);
x_17 = lean_uint32_dec_eq(x_16, x_11);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_string_utf8_next(x_1, x_15);
lean_dec(x_15);
x_19 = lean_string_utf8_get(x_1, x_18);
x_20 = lean_uint32_dec_eq(x_19, x_11);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 33;
x_22 = lean_uint32_dec_eq(x_19, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_2, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = lean_string_utf8_next(x_1, x_18);
lean_dec(x_18);
lean_ctor_set(x_2, 1, x_27);
x_28 = lean_unsigned_to_nat(1u);
x_29 = l_Lean_ParseImports_finishCommentBlock(x_28, x_1, x_2);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
x_2 = x_29;
goto _start;
}
else
{
lean_dec(x_30);
return x_29;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
x_32 = lean_string_utf8_next(x_1, x_18);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_5);
x_34 = lean_unsigned_to_nat(1u);
x_35 = l_Lean_ParseImports_finishCommentBlock(x_34, x_1, x_33);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
x_2 = x_35;
goto _start;
}
else
{
lean_dec(x_36);
return x_35;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
}
}
}
else
{
lean_object* x_38; uint32_t x_39; uint8_t x_40; 
x_38 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_39 = lean_string_utf8_get(x_1, x_38);
x_40 = lean_uint32_dec_eq(x_39, x_11);
if (x_40 == 0)
{
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_2, 2);
lean_dec(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_2, 0);
lean_dec(x_44);
x_45 = lean_string_utf8_next(x_1, x_38);
lean_dec(x_38);
lean_ctor_set(x_2, 1, x_45);
x_46 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(x_1, x_2);
x_47 = lean_ctor_get(x_46, 2);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
x_2 = x_46;
goto _start;
}
else
{
lean_dec(x_47);
return x_46;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
x_49 = lean_string_utf8_next(x_1, x_38);
lean_dec(x_38);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_5);
x_51 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(x_1, x_50);
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
}
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_2);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_2, 2);
lean_dec(x_55);
x_56 = lean_ctor_get(x_2, 1);
lean_dec(x_56);
x_57 = lean_ctor_get(x_2, 0);
lean_dec(x_57);
x_58 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_58);
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_2);
x_60 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_3);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_5);
x_2 = x_61;
goto _start;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_5);
x_63 = !lean_is_exclusive(x_2);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_2, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_2, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_2, 0);
lean_dec(x_66);
x_67 = l_Lean_ParseImports_whitespace___closed__2;
lean_ctor_set(x_2, 2, x_67);
return x_2;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
x_68 = l_Lean_ParseImports_whitespace___closed__2;
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_3);
lean_ctor_set(x_69, 1, x_4);
lean_ctor_set(x_69, 2, x_68);
return x_69;
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
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
x_1 = lean_mk_string_from_bytes("`", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` expected", 10);
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
uint32_t x_10; uint8_t x_11; 
x_10 = lean_string_utf8_get_fast(x_1, x_8);
lean_dec(x_8);
x_11 = l_Lean_isIdFirst(x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = l_Lean_idBeginEscape;
x_13 = lean_uint32_dec_eq(x_10, x_12);
return x_13;
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
lean_dec(x_8);
x_15 = 0;
return x_15;
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
uint8_t x_2; 
x_2 = l_Char_isAlphanum(x_1);
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
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
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
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
uint8_t x_7; uint32_t x_18; uint8_t x_19; 
x_18 = lean_string_utf8_get_fast(x_1, x_4);
x_19 = l_Char_isAlphanum(x_18);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 46;
x_21 = lean_uint32_dec_eq(x_18, x_20);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 10;
x_23 = lean_uint32_dec_eq(x_18, x_22);
if (x_23 == 0)
{
uint32_t x_24; uint8_t x_25; 
x_24 = 32;
x_25 = lean_uint32_dec_eq(x_18, x_24);
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 95;
x_27 = lean_uint32_dec_eq(x_18, x_26);
if (x_27 == 0)
{
uint32_t x_28; uint8_t x_29; 
x_28 = 39;
x_29 = lean_uint32_dec_eq(x_18, x_28);
if (x_29 == 0)
{
uint32_t x_30; uint8_t x_31; 
x_30 = 33;
x_31 = lean_uint32_dec_eq(x_18, x_30);
if (x_31 == 0)
{
uint32_t x_32; uint8_t x_33; 
x_32 = 63;
x_33 = lean_uint32_dec_eq(x_18, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_isLetterLike(x_18);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_isSubScriptAlnum(x_18);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = 1;
x_7 = x_36;
goto block_17;
}
else
{
uint8_t x_37; 
x_37 = 0;
x_7 = x_37;
goto block_17;
}
}
else
{
uint8_t x_38; 
x_38 = 0;
x_7 = x_38;
goto block_17;
}
}
else
{
uint8_t x_39; 
x_39 = 0;
x_7 = x_39;
goto block_17;
}
}
else
{
uint8_t x_40; 
x_40 = 0;
x_7 = x_40;
goto block_17;
}
}
else
{
uint8_t x_41; 
x_41 = 0;
x_7 = x_41;
goto block_17;
}
}
else
{
uint8_t x_42; 
x_42 = 0;
x_7 = x_42;
goto block_17;
}
}
else
{
uint8_t x_43; 
x_43 = 1;
x_7 = x_43;
goto block_17;
}
}
else
{
uint8_t x_44; 
x_44 = 1;
x_7 = x_44;
goto block_17;
}
}
else
{
uint8_t x_45; 
x_45 = 1;
x_7 = x_45;
goto block_17;
}
}
else
{
uint8_t x_46; 
x_46 = 0;
x_7 = x_46;
goto block_17;
}
block_17:
{
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 0);
lean_dec(x_11);
x_12 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_12);
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_5);
x_2 = x_15;
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
x_1 = lean_mk_string_from_bytes("expected identifier", 19);
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
x_1 = lean_mk_string_from_bytes("unterminated identifier escape", 30);
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_4, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = lean_string_utf8_get_fast(x_2, x_6);
x_14 = l_Lean_idBeginEscape;
x_15 = lean_uint32_dec_eq(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_isIdFirst(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_3);
x_17 = l_Lean_ParseImports_moduleIdent_parse___closed__2;
lean_ctor_set(x_4, 2, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint32_t x_36; uint32_t x_37; uint8_t x_38; 
x_18 = lean_string_utf8_next_fast(x_2, x_6);
lean_ctor_set(x_4, 1, x_18);
x_19 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(x_2, x_4);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_string_utf8_extract(x_2, x_6, x_20);
lean_dec(x_6);
x_22 = l_Lean_Name_str___override(x_3, x_21);
x_36 = lean_string_utf8_get(x_2, x_20);
x_37 = 46;
x_38 = lean_uint32_dec_eq(x_36, x_37);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = 0;
x_23 = x_39;
goto block_35;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_string_utf8_next(x_2, x_20);
x_41 = lean_string_utf8_at_end(x_2, x_40);
if (x_41 == 0)
{
uint32_t x_42; uint8_t x_43; 
x_42 = lean_string_utf8_get_fast(x_2, x_40);
lean_dec(x_40);
x_43 = l_Lean_isIdFirst(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = lean_uint32_dec_eq(x_42, x_14);
x_23 = x_44;
goto block_35;
}
else
{
uint8_t x_45; 
x_45 = 1;
x_23 = x_45;
goto block_35;
}
}
else
{
uint8_t x_46; 
lean_dec(x_40);
x_46 = 0;
x_23 = x_46;
goto block_35;
}
}
block_35:
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
x_24 = l_Lean_ParseImports_State_pushModule(x_22, x_1, x_19);
x_25 = l_Lean_ParseImports_whitespace(x_2, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
x_27 = lean_string_utf8_next(x_2, x_20);
lean_dec(x_20);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
lean_ctor_set(x_19, 1, x_27);
x_3 = x_22;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_19, 2);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_32);
x_3 = x_22;
x_4 = x_33;
goto _start;
}
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_string_utf8_next_fast(x_2, x_6);
lean_dec(x_6);
lean_inc(x_47);
lean_ctor_set(x_4, 1, x_47);
x_48 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(x_2, x_4);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_ctor_get(x_48, 2);
x_53 = lean_string_utf8_at_end(x_2, x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint32_t x_64; uint32_t x_65; uint8_t x_66; 
x_54 = lean_string_utf8_next_fast(x_2, x_51);
lean_inc(x_52);
lean_inc(x_54);
lean_inc(x_50);
lean_ctor_set(x_48, 1, x_54);
x_55 = lean_string_utf8_extract(x_2, x_47, x_51);
lean_dec(x_51);
lean_dec(x_47);
x_56 = l_Lean_Name_str___override(x_3, x_55);
x_64 = lean_string_utf8_get(x_2, x_54);
x_65 = 46;
x_66 = lean_uint32_dec_eq(x_64, x_65);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = 0;
x_57 = x_67;
goto block_63;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_string_utf8_next(x_2, x_54);
x_69 = lean_string_utf8_at_end(x_2, x_68);
if (x_69 == 0)
{
uint32_t x_70; uint8_t x_71; 
x_70 = lean_string_utf8_get_fast(x_2, x_68);
lean_dec(x_68);
x_71 = l_Lean_isIdFirst(x_70);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = lean_uint32_dec_eq(x_70, x_14);
x_57 = x_72;
goto block_63;
}
else
{
uint8_t x_73; 
x_73 = 1;
x_57 = x_73;
goto block_63;
}
}
else
{
uint8_t x_74; 
lean_dec(x_68);
x_74 = 0;
x_57 = x_74;
goto block_63;
}
}
block_63:
{
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_50);
x_58 = l_Lean_ParseImports_State_pushModule(x_56, x_1, x_48);
x_59 = l_Lean_ParseImports_whitespace(x_2, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_48);
x_60 = lean_string_utf8_next(x_2, x_54);
lean_dec(x_54);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_52);
x_3 = x_56;
x_4 = x_61;
goto _start;
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_52);
lean_dec(x_47);
lean_dec(x_3);
x_75 = l_Lean_ParseImports_moduleIdent_parse___closed__4;
lean_ctor_set(x_48, 2, x_75);
return x_48;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_48, 0);
x_77 = lean_ctor_get(x_48, 1);
x_78 = lean_ctor_get(x_48, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_48);
x_79 = lean_string_utf8_at_end(x_2, x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint32_t x_91; uint32_t x_92; uint8_t x_93; 
x_80 = lean_string_utf8_next_fast(x_2, x_77);
lean_inc(x_78);
lean_inc(x_80);
lean_inc(x_76);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_78);
x_82 = lean_string_utf8_extract(x_2, x_47, x_77);
lean_dec(x_77);
lean_dec(x_47);
x_83 = l_Lean_Name_str___override(x_3, x_82);
x_91 = lean_string_utf8_get(x_2, x_80);
x_92 = 46;
x_93 = lean_uint32_dec_eq(x_91, x_92);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = 0;
x_84 = x_94;
goto block_90;
}
else
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_string_utf8_next(x_2, x_80);
x_96 = lean_string_utf8_at_end(x_2, x_95);
if (x_96 == 0)
{
uint32_t x_97; uint8_t x_98; 
x_97 = lean_string_utf8_get_fast(x_2, x_95);
lean_dec(x_95);
x_98 = l_Lean_isIdFirst(x_97);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = lean_uint32_dec_eq(x_97, x_14);
x_84 = x_99;
goto block_90;
}
else
{
uint8_t x_100; 
x_100 = 1;
x_84 = x_100;
goto block_90;
}
}
else
{
uint8_t x_101; 
lean_dec(x_95);
x_101 = 0;
x_84 = x_101;
goto block_90;
}
}
block_90:
{
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_76);
x_85 = l_Lean_ParseImports_State_pushModule(x_83, x_1, x_81);
x_86 = l_Lean_ParseImports_whitespace(x_2, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_81);
x_87 = lean_string_utf8_next(x_2, x_80);
lean_dec(x_80);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_78);
x_3 = x_83;
x_4 = x_88;
goto _start;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_78);
lean_dec(x_47);
lean_dec(x_3);
x_102 = l_Lean_ParseImports_moduleIdent_parse___closed__4;
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_76);
lean_ctor_set(x_103, 1, x_77);
lean_ctor_set(x_103, 2, x_102);
return x_103;
}
}
}
}
else
{
uint32_t x_104; uint32_t x_105; uint8_t x_106; 
lean_dec(x_4);
x_104 = lean_string_utf8_get_fast(x_2, x_6);
x_105 = l_Lean_idBeginEscape;
x_106 = lean_uint32_dec_eq(x_104, x_105);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_isIdFirst(x_104);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_7);
lean_dec(x_3);
x_108 = l_Lean_ParseImports_moduleIdent_parse___closed__2;
x_109 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_109, 0, x_5);
lean_ctor_set(x_109, 1, x_6);
lean_ctor_set(x_109, 2, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint32_t x_126; uint32_t x_127; uint8_t x_128; 
x_110 = lean_string_utf8_next_fast(x_2, x_6);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_5);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_7);
x_112 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(x_2, x_111);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
x_114 = lean_string_utf8_extract(x_2, x_6, x_113);
lean_dec(x_6);
x_115 = l_Lean_Name_str___override(x_3, x_114);
x_126 = lean_string_utf8_get(x_2, x_113);
x_127 = 46;
x_128 = lean_uint32_dec_eq(x_126, x_127);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = 0;
x_116 = x_129;
goto block_125;
}
else
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_string_utf8_next(x_2, x_113);
x_131 = lean_string_utf8_at_end(x_2, x_130);
if (x_131 == 0)
{
uint32_t x_132; uint8_t x_133; 
x_132 = lean_string_utf8_get_fast(x_2, x_130);
lean_dec(x_130);
x_133 = l_Lean_isIdFirst(x_132);
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = lean_uint32_dec_eq(x_132, x_105);
x_116 = x_134;
goto block_125;
}
else
{
uint8_t x_135; 
x_135 = 1;
x_116 = x_135;
goto block_125;
}
}
else
{
uint8_t x_136; 
lean_dec(x_130);
x_136 = 0;
x_116 = x_136;
goto block_125;
}
}
block_125:
{
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_113);
x_117 = l_Lean_ParseImports_State_pushModule(x_115, x_1, x_112);
x_118 = l_Lean_ParseImports_whitespace(x_2, x_117);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
x_120 = lean_string_utf8_next(x_2, x_113);
lean_dec(x_113);
x_121 = lean_ctor_get(x_112, 2);
lean_inc(x_121);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 x_122 = x_112;
} else {
 lean_dec_ref(x_112);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 3, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_120);
lean_ctor_set(x_123, 2, x_121);
x_3 = x_115;
x_4 = x_123;
goto _start;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_137 = lean_string_utf8_next_fast(x_2, x_6);
lean_dec(x_6);
lean_inc(x_137);
x_138 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_138, 0, x_5);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_7);
x_139 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(x_2, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 2);
lean_inc(x_142);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 lean_ctor_release(x_139, 2);
 x_143 = x_139;
} else {
 lean_dec_ref(x_139);
 x_143 = lean_box(0);
}
x_144 = lean_string_utf8_at_end(x_2, x_141);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint32_t x_156; uint32_t x_157; uint8_t x_158; 
x_145 = lean_string_utf8_next_fast(x_2, x_141);
lean_inc(x_142);
lean_inc(x_145);
lean_inc(x_140);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 3, 0);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_142);
x_147 = lean_string_utf8_extract(x_2, x_137, x_141);
lean_dec(x_141);
lean_dec(x_137);
x_148 = l_Lean_Name_str___override(x_3, x_147);
x_156 = lean_string_utf8_get(x_2, x_145);
x_157 = 46;
x_158 = lean_uint32_dec_eq(x_156, x_157);
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = 0;
x_149 = x_159;
goto block_155;
}
else
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_string_utf8_next(x_2, x_145);
x_161 = lean_string_utf8_at_end(x_2, x_160);
if (x_161 == 0)
{
uint32_t x_162; uint8_t x_163; 
x_162 = lean_string_utf8_get_fast(x_2, x_160);
lean_dec(x_160);
x_163 = l_Lean_isIdFirst(x_162);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = lean_uint32_dec_eq(x_162, x_105);
x_149 = x_164;
goto block_155;
}
else
{
uint8_t x_165; 
x_165 = 1;
x_149 = x_165;
goto block_155;
}
}
else
{
uint8_t x_166; 
lean_dec(x_160);
x_166 = 0;
x_149 = x_166;
goto block_155;
}
}
block_155:
{
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_145);
lean_dec(x_142);
lean_dec(x_140);
x_150 = l_Lean_ParseImports_State_pushModule(x_148, x_1, x_146);
x_151 = l_Lean_ParseImports_whitespace(x_2, x_150);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_146);
x_152 = lean_string_utf8_next(x_2, x_145);
lean_dec(x_145);
x_153 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_153, 0, x_140);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_142);
x_3 = x_148;
x_4 = x_153;
goto _start;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_142);
lean_dec(x_137);
lean_dec(x_3);
x_167 = l_Lean_ParseImports_moduleIdent_parse___closed__4;
if (lean_is_scalar(x_143)) {
 x_168 = lean_alloc_ctor(0, 3, 0);
} else {
 x_168 = x_143;
}
lean_ctor_set(x_168, 0, x_140);
lean_ctor_set(x_168, 1, x_141);
lean_ctor_set(x_168, 2, x_167);
return x_168;
}
}
}
}
else
{
lean_object* x_169; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_169 = l_Lean_ParseImports_State_mkEOIError(x_4);
return x_169;
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
x_1 = lean_mk_string_from_bytes("Init", 4);
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
x_1 = lean_mk_string_from_bytes("import", 6);
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
x_1 = lean_mk_string_from_bytes("runtime", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
lean_dec(x_5);
x_16 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1;
lean_inc(x_6);
lean_inc(x_1);
x_17 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(x_16, x_3, x_4, x_1, x_6);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
if (x_2 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1;
lean_inc(x_1);
x_21 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(x_20, x_3, x_17, x_1, x_19);
x_8 = x_21;
goto block_15;
}
else
{
x_8 = x_17;
goto block_15;
}
}
else
{
lean_dec(x_18);
x_8 = x_17;
goto block_15;
}
block_15:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Array_shrink___rarg(x_11, x_7);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
lean_dec(x_5);
x_16 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1;
lean_inc(x_6);
lean_inc(x_1);
x_17 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(x_16, x_3, x_4, x_1, x_6);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1;
lean_inc(x_1);
x_21 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(x_20, x_3, x_17, x_1, x_19);
x_8 = x_21;
goto block_15;
}
else
{
lean_dec(x_18);
if (x_2 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
x_23 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1;
lean_inc(x_1);
x_24 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(x_23, x_3, x_17, x_1, x_22);
x_8 = x_24;
goto block_15;
}
else
{
x_8 = x_17;
goto block_15;
}
}
block_15:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_4 = x_8;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Array_shrink___rarg(x_11, x_7);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_ParseImports_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("prelude", 7);
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
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(x_5, x_8, x_1, x_6);
lean_dec(x_1);
return x_9;
}
else
{
lean_dec(x_7);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__4(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_parseImports_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_parseImports_x27___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_parseImports_x27___closed__1;
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lean_parseImports_x27___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_10);
lean_dec(x_10);
x_16 = lean_string_append(x_15, x_11);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_parseImports_x27(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("module", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("runtimeOnly", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_Name_toString(x_2, x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_11, 0, x_10);
x_12 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_join___rarg(x_16);
x_18 = l_Lean_Json_mkObj(x_17);
return x_18;
}
}
static lean_object* _init_l_Lean_instToJsonImport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628_), 1, 0);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628_(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__2(x_6, x_7, x_4);
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("imports", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("errors", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__1;
x_4 = l_Lean_Json_opt___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__1(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__3(x_7, x_8, x_5);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__2;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_join___rarg(x_16);
x_18 = l_Lean_Json_mkObj(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____spec__3(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718_), 1, 0);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1799____spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718_(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1799_(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1799____spec__1(x_3, x_4, x_1);
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_List_join___rarg(x_11);
x_13 = l_Lean_Json_mkObj(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1799____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1799____spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportsResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1799_), 1, 0);
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
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Lean_ParseImports_State_imports___default___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_9, x_2, x_18);
x_2 = x_20;
x_3 = x_21;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_box(0);
x_26 = lean_io_error_to_string(x_23);
x_27 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
x_28 = lean_array_push(x_27, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_2, x_30);
x_32 = lean_array_uset(x_9, x_2, x_29);
x_2 = x_31;
x_3 = x_32;
x_4 = x_24;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
lean_dec(x_7);
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_box(0);
x_37 = lean_io_error_to_string(x_34);
x_38 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = 1;
x_42 = lean_usize_add(x_2, x_41);
x_43 = lean_array_uset(x_9, x_2, x_40);
x_2 = x_42;
x_3 = x_43;
x_4 = x_35;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lean_print_imports_json(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1(x_4, x_5, x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1799_(x_7);
x_10 = l_Lean_Json_compress(x_9);
x_11 = l_IO_println___at_Lean_instEval___spec__1(x_10, x_8);
return x_11;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__1 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__1();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__1);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__2 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__2();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1628____closed__2);
l_Lean_instToJsonImport___closed__1 = _init_l_Lean_instToJsonImport___closed__1();
lean_mark_persistent(l_Lean_instToJsonImport___closed__1);
l_Lean_instToJsonImport = _init_l_Lean_instToJsonImport();
lean_mark_persistent(l_Lean_instToJsonImport);
l_Lean_PrintImportResult_imports_x3f___default = _init_l_Lean_PrintImportResult_imports_x3f___default();
lean_mark_persistent(l_Lean_PrintImportResult_imports_x3f___default);
l_Lean_PrintImportResult_errors___default = _init_l_Lean_PrintImportResult_errors___default();
lean_mark_persistent(l_Lean_PrintImportResult_errors___default);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__1 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__1();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__1);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__2 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__2();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1718____closed__2);
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
