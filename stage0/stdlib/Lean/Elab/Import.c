// Lean compiler output
// Module: Lean.Elab.Import
// Imports: Lean.Parser.Module Lean.Util.Paths Lean.CoreM
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
LEAN_EXPORT lean_object* l_IO_println___at_Lean_Elab_printImports___spec__1(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* lean_print_imports(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__1;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__4;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__3;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__4;
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__6;
static lean_object* l_Lean_Elab_processHeaderCore___closed__2;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* lean_print_import_srcs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath(lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__2;
lean_object* l_Lean_Name_getRoot(lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__2;
static lean_object* l_Lean_Elab_processHeaderCore___closed__1;
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImports___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_IO_print___at_IO_println___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_isModule___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__8;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__3;
extern lean_object* l_Lean_instInhabitedImport;
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImportSrcs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImports___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1(lean_object*);
static lean_object* l_Lean_Elab_parseImports___closed__1;
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImportSrcs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_findLean(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__5;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__2;
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_inServer;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__3;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__1;
static lean_object* l_Lean_Elab_HeaderSyntax_imports___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = 0;
x_3 = l_Lean_Syntax_getPos_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_startPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_HeaderSyntax_startPos(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_isNone(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_isModule___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_HeaderSyntax_isModule(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedImport;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Import", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.HeaderSyntax.imports", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(27u);
x_4 = lean_unsigned_to_nat(13u);
x_5 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(3u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(4u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_matchesNull(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4;
x_12 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__2(x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = 1;
x_16 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_15);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; 
x_17 = 0;
x_18 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_17);
return x_18;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_19; lean_object* x_20; 
x_19 = 1;
x_20 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 1, x_19);
return x_20;
}
else
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = 1;
x_22 = 0;
x_23 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 1, x_22);
return x_23;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Module", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3;
x_4 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
x_8 = l_Lean_Syntax_matchesNull(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4;
x_10 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__2(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_5, x_11);
lean_dec(x_5);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__5;
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4;
x_16 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__2(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_Syntax_getArg(x_12, x_11);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_box(0);
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1(x_1, x_3, x_19, x_18);
lean_dec(x_18);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = lean_box(0);
x_23 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1(x_1, x_3, x_22, x_21);
return x_23;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("private", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3;
x_4 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
lean_inc(x_7);
x_10 = l_Lean_Syntax_isOfKind(x_7, x_1);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4;
x_14 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__2(x_13);
x_15 = lean_array_uset(x_9, x_4, x_14);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Syntax_getArg(x_7, x_8);
x_18 = l_Lean_Syntax_isNone(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(1u);
lean_inc(x_17);
x_20 = l_Lean_Syntax_matchesNull(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_7);
x_21 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4;
x_22 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__2(x_21);
x_23 = lean_array_uset(x_9, x_4, x_22);
x_4 = x_12;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_Syntax_getArg(x_17, x_8);
lean_dec(x_17);
x_26 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__2;
lean_inc(x_25);
x_27 = l_Lean_Syntax_isOfKind(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_7);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4;
x_29 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__2(x_28);
x_30 = lean_array_uset(x_9, x_4, x_29);
x_4 = x_12;
x_5 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_Syntax_getArg(x_25, x_8);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_box(0);
x_35 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2(x_7, x_34, x_33);
lean_dec(x_33);
lean_dec(x_7);
x_36 = lean_array_uset(x_9, x_4, x_35);
x_4 = x_12;
x_5 = x_36;
goto _start;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_17);
x_38 = lean_box(0);
x_39 = lean_box(0);
x_40 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2(x_7, x_39, x_38);
lean_dec(x_7);
x_41 = lean_array_uset(x_9, x_4, x_40);
x_4 = x_12;
x_5 = x_41;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3;
x_4 = l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__4;
x_2 = 0;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__6;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_8 = lean_array_size(x_7);
x_9 = 0;
x_10 = l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__2;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3(x_10, x_6, x_8, x_9, x_7);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__7;
x_13 = l_Array_append___rarg(x_12, x_11);
lean_dec(x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__8;
x_15 = l_Array_append___rarg(x_14, x_11);
lean_dec(x_11);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(28u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("prelude", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3;
x_4 = l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_5);
x_7 = l_Lean_Syntax_matchesNull(x_5, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__1;
x_9 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_5, x_10);
lean_dec(x_5);
x_12 = l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__3;
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__1;
x_15 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1(x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Syntax_getArg(x_11, x_10);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Elab_HeaderSyntax_imports___lambda__1(x_1, x_18, x_17);
lean_dec(x_17);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_HeaderSyntax_imports___lambda__1(x_1, x_21, x_20);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("header", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3;
x_4 = l_Lean_Elab_HeaderSyntax_imports___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moduleTk", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_HeaderSyntax_imports___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3;
x_4 = l_Lean_Elab_HeaderSyntax_imports___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_HeaderSyntax_imports___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__1;
x_5 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_isNone(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_10 = l_Lean_Syntax_matchesNull(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_11 = l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__1;
x_12 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1(x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Syntax_getArg(x_7, x_6);
lean_dec(x_7);
x_14 = l_Lean_Elab_HeaderSyntax_imports___closed__4;
lean_inc(x_13);
x_15 = l_Lean_Syntax_isOfKind(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_1);
x_16 = l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__1;
x_17 = l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_Syntax_getArg(x_13, x_6);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_HeaderSyntax_imports___lambda__2(x_1, x_20, x_19);
lean_dec(x_19);
lean_dec(x_1);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_HeaderSyntax_imports___lambda__2(x_1, x_23, x_22);
lean_dec(x_1);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_HeaderSyntax_imports___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_HeaderSyntax_imports___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_HeaderSyntax_imports___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_headerToImports(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_HeaderSyntax_imports(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot use `private import` without `module`", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot use `import all` across module path roots", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1(x_1, x_2, x_7, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_Lean_Name_getRoot(x_3);
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_Lean_Name_getRoot(x_10);
x_12 = lean_name_eq(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1(x_1, x_2, x_15, x_5);
return x_16;
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot use `import all` without `module`", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_7, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = lean_array_uget(x_5, x_7);
if (x_2 == 0)
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2(x_2, x_12, x_3, x_14, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_7, x_19);
x_7 = x_20;
x_8 = x_18;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
x_26 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__2;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2(x_2, x_12, x_3, x_28, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 1;
x_34 = lean_usize_add(x_7, x_33);
x_7 = x_34;
x_8 = x_32;
x_9 = x_31;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_Environment_setMainModule(x_5, x_1);
lean_ctor_set(x_2, 0, x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = l_Lean_Environment_setMainModule(x_8, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_processHeaderCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_processHeaderCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_inServer;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint32_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_box(0);
x_14 = lean_array_size(x_2);
x_15 = 0;
x_16 = lean_box(0);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1(x_2, x_3, x_10, x_13, x_2, x_14, x_15, x_16, x_12);
if (x_3 == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_dec(x_17);
x_44 = 1;
x_45 = 2;
x_46 = l_Lean_importModules(x_2, x_4, x_7, x_8, x_9, x_44, x_45, x_11, x_43);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 1);
lean_ctor_set(x_46, 1, x_5);
x_49 = l_Lean_Elab_processHeaderCore___lambda__1(x_10, x_46, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_5);
x_53 = l_Lean_Elab_processHeaderCore___lambda__1(x_10, x_52, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_18 = x_54;
x_19 = x_55;
goto block_42;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_56 = lean_ctor_get(x_17, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_17, 1);
lean_inc(x_57);
lean_dec(x_17);
x_18 = x_56;
x_19 = x_57;
goto block_42;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Elab_processHeaderCore___closed__2;
x_59 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_4, x_58);
if (x_59 == 0)
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
lean_dec(x_17);
x_61 = 1;
x_62 = 0;
x_63 = l_Lean_importModules(x_2, x_4, x_7, x_8, x_9, x_61, x_62, x_11, x_60);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
lean_dec(x_6);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 1);
lean_ctor_set(x_63, 1, x_5);
x_66 = l_Lean_Elab_processHeaderCore___lambda__1(x_10, x_63, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_63);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_5);
x_70 = l_Lean_Elab_processHeaderCore___lambda__1(x_10, x_69, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_dec(x_63);
x_18 = x_71;
x_19 = x_72;
goto block_42;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_73 = lean_ctor_get(x_17, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_17, 1);
lean_inc(x_74);
lean_dec(x_17);
x_18 = x_73;
x_19 = x_74;
goto block_42;
}
}
else
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_17, 1);
lean_inc(x_75);
lean_dec(x_17);
x_76 = 1;
x_77 = 1;
x_78 = l_Lean_importModules(x_2, x_4, x_7, x_8, x_9, x_76, x_77, x_11, x_75);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
lean_dec(x_6);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 1);
lean_ctor_set(x_78, 1, x_5);
x_81 = l_Lean_Elab_processHeaderCore___lambda__1(x_10, x_78, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_78, 0);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_78);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_5);
x_85 = l_Lean_Elab_processHeaderCore___lambda__1(x_10, x_84, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_78, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_78, 1);
lean_inc(x_87);
lean_dec(x_78);
x_18 = x_86;
x_19 = x_87;
goto block_42;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_88 = lean_ctor_get(x_17, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_17, 1);
lean_inc(x_89);
lean_dec(x_17);
x_18 = x_88;
x_19 = x_89;
goto block_42;
}
}
}
block_42:
{
uint32_t x_20; lean_object* x_21; 
x_20 = 0;
x_21 = lean_mk_empty_environment(x_20, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_6, 2);
lean_inc(x_24);
x_25 = l_Lean_FileMap_toPosition(x_24, x_1);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_box(0);
x_28 = lean_io_error_to_string(x_18);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_MessageData_ofFormat(x_29);
x_31 = 0;
x_32 = 2;
x_33 = l_Lean_Elab_processHeaderCore___closed__1;
x_34 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*5, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*5 + 1, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*5 + 2, x_31);
x_35 = l_Lean_MessageLog_add(x_34, x_5);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_processHeaderCore___lambda__1(x_10, x_36, x_23);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1(x_1, x_10, x_3, x_4, x_5, x_11, x_12, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeaderCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint32_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox_uint32(x_7);
lean_dec(x_7);
x_15 = lean_unbox(x_9);
lean_dec(x_9);
x_16 = l_Lean_Elab_processHeaderCore(x_1, x_2, x_13, x_4, x_5, x_6, x_14, x_8, x_15, x_10, x_11, x_12);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint32_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Elab_HeaderSyntax_startPos(x_1);
lean_inc(x_1);
x_11 = l_Lean_Elab_HeaderSyntax_imports(x_1);
x_12 = l_Lean_Elab_HeaderSyntax_isModule(x_1);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l_Lean_Elab_processHeaderCore(x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13, x_9);
lean_dec(x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_processHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint32_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l_Lean_Elab_processHeader(x_1, x_2, x_3, x_4, x_10, x_6, x_11, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_parseImports___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<input>", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_parseImports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Elab_parseImports___closed__1;
x_5 = 1;
x_6 = l_Lean_Parser_mkInputContext(x_1, x_4, x_5);
lean_inc(x_6);
x_7 = l_Lean_Parser_parseHeader(x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = l_Lean_Elab_HeaderSyntax_imports(x_13);
x_18 = lean_ctor_get(x_6, 2);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_FileMap_toPosition(x_18, x_19);
lean_dec(x_19);
lean_ctor_set(x_9, 0, x_20);
lean_ctor_set(x_8, 0, x_17);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = l_Lean_Elab_HeaderSyntax_imports(x_13);
x_24 = lean_ctor_get(x_6, 2);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_FileMap_toPosition(x_24, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_8, 1, x_27);
lean_ctor_set(x_8, 0, x_23);
return x_7;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_31 = x_9;
} else {
 lean_dec_ref(x_9);
 x_31 = lean_box(0);
}
x_32 = l_Lean_Elab_HeaderSyntax_imports(x_28);
x_33 = lean_ctor_get(x_6, 2);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = l_Lean_FileMap_toPosition(x_33, x_34);
lean_dec(x_34);
if (lean_is_scalar(x_31)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_31;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_7, 0, x_37);
return x_7;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_dec(x_7);
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_40 = x_8;
} else {
 lean_dec_ref(x_8);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_9, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_43 = x_9;
} else {
 lean_dec_ref(x_9);
 x_43 = lean_box(0);
}
x_44 = l_Lean_Elab_HeaderSyntax_imports(x_39);
x_45 = lean_ctor_get(x_6, 2);
lean_inc(x_45);
lean_dec(x_6);
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_FileMap_toPosition(x_45, x_46);
lean_dec(x_46);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
if (lean_is_scalar(x_40)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_40;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_38);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_7);
if (x_51 == 0)
{
return x_7;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_7, 0);
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_7);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
lean_dec(x_2);
x_56 = 1;
x_57 = l_Lean_Parser_mkInputContext(x_1, x_55, x_56);
lean_inc(x_57);
x_58 = l_Lean_Parser_parseHeader(x_57, x_3);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_58, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = l_Lean_Elab_HeaderSyntax_imports(x_64);
x_69 = lean_ctor_get(x_57, 2);
lean_inc(x_69);
lean_dec(x_57);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = l_Lean_FileMap_toPosition(x_69, x_70);
lean_dec(x_70);
lean_ctor_set(x_60, 0, x_71);
lean_ctor_set(x_59, 0, x_68);
return x_58;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_60, 0);
x_73 = lean_ctor_get(x_60, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_60);
x_74 = l_Lean_Elab_HeaderSyntax_imports(x_64);
x_75 = lean_ctor_get(x_57, 2);
lean_inc(x_75);
lean_dec(x_57);
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
lean_dec(x_72);
x_77 = l_Lean_FileMap_toPosition(x_75, x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_59, 1, x_78);
lean_ctor_set(x_59, 0, x_74);
return x_58;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_59, 0);
lean_inc(x_79);
lean_dec(x_59);
x_80 = lean_ctor_get(x_60, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_60, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_82 = x_60;
} else {
 lean_dec_ref(x_60);
 x_82 = lean_box(0);
}
x_83 = l_Lean_Elab_HeaderSyntax_imports(x_79);
x_84 = lean_ctor_get(x_57, 2);
lean_inc(x_84);
lean_dec(x_57);
x_85 = lean_ctor_get(x_80, 0);
lean_inc(x_85);
lean_dec(x_80);
x_86 = l_Lean_FileMap_toPosition(x_84, x_85);
lean_dec(x_85);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_82;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_58, 0, x_88);
return x_58;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_58, 1);
lean_inc(x_89);
lean_dec(x_58);
x_90 = lean_ctor_get(x_59, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_91 = x_59;
} else {
 lean_dec_ref(x_59);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_60, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_60, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_94 = x_60;
} else {
 lean_dec_ref(x_60);
 x_94 = lean_box(0);
}
x_95 = l_Lean_Elab_HeaderSyntax_imports(x_90);
x_96 = lean_ctor_get(x_57, 2);
lean_inc(x_96);
lean_dec(x_57);
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
x_98 = l_Lean_FileMap_toPosition(x_96, x_97);
lean_dec(x_97);
if (lean_is_scalar(x_94)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_94;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_93);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_89);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_57);
x_102 = !lean_is_exclusive(x_58);
if (x_102 == 0)
{
return x_58;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_58, 0);
x_104 = lean_ctor_get(x_58, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_58);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_println___at_Lean_Elab_printImports___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at_IO_println___spec__1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImports___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
x_10 = lean_array_uget(x_3, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_findOLean(x_11, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_IO_println___at_Lean_Elab_printImports___spec__1(x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_18 = lean_usize_add(x_5, x_17);
x_19 = lean_box(0);
x_5 = x_18;
x_6 = x_19;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_print_imports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_parseImports(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_array_size(x_7);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImports___spec__2(x_7, x_8, x_7, x_9, x_10, x_11, x_6);
lean_dec(x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
return x_4;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImports___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImports___spec__2(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImportSrcs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_11 = lean_array_uget(x_4, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_1);
x_13 = l_Lean_findLean(x_1, x_12, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_println___at_Lean_Elab_printImports___spec__1(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_6, x_18);
x_20 = lean_box(0);
x_6 = x_19;
x_7 = x_20;
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* lean_print_import_srcs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getSrcSearchPath(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_parseImports(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_array_size(x_10);
x_13 = 0;
x_14 = lean_box(0);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImportSrcs___spec__1(x_5, x_10, x_11, x_10, x_12, x_13, x_14, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
return x_4;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImportSrcs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_printImportSrcs___spec__1(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Import(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Paths(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1___closed__1 = _init_l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_HeaderSyntax_imports___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__1___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___lambda__2___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_HeaderSyntax_imports___spec__3___closed__2);
l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__1 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__1);
l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__2 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__2);
l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__3 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__3);
l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__4 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__4);
l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__5 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__5);
l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__6 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__6);
l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__7 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__7);
l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__8 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__1___closed__8);
l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__1 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__1);
l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__2 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__2);
l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__3 = _init_l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___lambda__2___closed__3);
l_Lean_Elab_HeaderSyntax_imports___closed__1 = _init_l_Lean_Elab_HeaderSyntax_imports___closed__1();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___closed__1);
l_Lean_Elab_HeaderSyntax_imports___closed__2 = _init_l_Lean_Elab_HeaderSyntax_imports___closed__2();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___closed__2);
l_Lean_Elab_HeaderSyntax_imports___closed__3 = _init_l_Lean_Elab_HeaderSyntax_imports___closed__3();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___closed__3);
l_Lean_Elab_HeaderSyntax_imports___closed__4 = _init_l_Lean_Elab_HeaderSyntax_imports___closed__4();
lean_mark_persistent(l_Lean_Elab_HeaderSyntax_imports___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__1___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___lambda__2___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_processHeaderCore___spec__1___closed__2);
l_Lean_Elab_processHeaderCore___closed__1 = _init_l_Lean_Elab_processHeaderCore___closed__1();
lean_mark_persistent(l_Lean_Elab_processHeaderCore___closed__1);
l_Lean_Elab_processHeaderCore___closed__2 = _init_l_Lean_Elab_processHeaderCore___closed__2();
lean_mark_persistent(l_Lean_Elab_processHeaderCore___closed__2);
l_Lean_Elab_parseImports___closed__1 = _init_l_Lean_Elab_parseImports___closed__1();
lean_mark_persistent(l_Lean_Elab_parseImports___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
