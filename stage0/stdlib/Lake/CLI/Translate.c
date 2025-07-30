// Lean compiler output
// Module: Lake.CLI.Translate
// Imports: Lake.Config.Lang Lake.Config.Package Lake.CLI.Translate.Toml Lake.CLI.Translate.Lean Lake.Load.Lean.Elab
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__10;
static lean_object* l_Lake_Package_mkConfigString___closed__27;
static lean_object* l_Lake_Package_mkConfigString___closed__1;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__26;
static lean_object* l_Lake_Package_mkConfigString___closed__3;
lean_object* l_Substring_takeWhileAux___at___Lean_Elab_Term_toParserDescr_isValidAtom_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__24;
static lean_object* l_Lake_Package_mkConfigString___closed__29;
lean_object* lean_io_get_num_heartbeats(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__21;
lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__13;
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__12;
static lean_object* l_Lake_Package_mkConfigString___closed__14;
static uint8_t l_Lake_Package_mkConfigString___closed__32;
static lean_object* l_Lake_Package_mkConfigString___closed__33;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__16;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__6;
static lean_object* l_Lake_Package_mkConfigString___closed__7;
static lean_object* l_Lake_Package_mkConfigString___closed__28;
static lean_object* l_Lake_Package_mkConfigString___closed__37;
lean_object* l_Lean_Option_get___at___Lean_Language_Lean_process_parseCmd_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__9;
static lean_object* l_Lake_Package_mkConfigString___closed__0;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lake_Package_mkConfigString___closed__8;
extern lean_object* l_Lean_inheritedTraceOptions;
static lean_object* l_Lake_Package_mkConfigString___closed__35;
static lean_object* l_Lake_Package_mkConfigString___closed__30;
static lean_object* l_Lake_Package_mkConfigString___closed__25;
static lean_object* l_Lake_Package_mkConfigString___closed__23;
static lean_object* l_Lake_Package_mkConfigString___closed__15;
static lean_object* l_Lake_Package_mkConfigString___closed__31;
static lean_object* l_Lake_Package_mkConfigString___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__36;
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_mkLeanConfig(lean_object*);
lean_object* l_Lake_Package_mkTomlConfig(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__38;
static lean_object* l_Lake_Package_mkConfigString___closed__20;
static lean_object* l_Lake_Package_mkConfigString___closed__22;
static lean_object* l_Lake_Package_mkConfigString___closed__11;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__34;
lean_object* l_Lake_Toml_ppTable(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__4;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__5;
static lean_object* l_Lake_Package_mkConfigString___closed__17;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_Package_mkConfigString___closed__19;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(lean_object*);
uint8_t l_Lean_Option_get___at___Lean_Firefox_Profile_export_spec__9(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__18;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Elab_Term_toParserDescr_isValidAtom_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_array_size(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(x_4, x_5, x_3);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_10 = lean_array_size(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(x_10, x_11, x_9);
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
return x_13;
}
}
case 3:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_erase_macro_scopes(x_15);
lean_ctor_set(x_1, 2, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_21 = lean_erase_macro_scopes(x_19);
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_20);
return x_22;
}
}
default: 
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lake_CLI_Translate_0__Lake_descopeSyntax_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(internal) failed to pretty print Lean configuration: ", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__3() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = 0;
x_3 = l_Lake_Package_mkConfigString___closed__2;
x_4 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__3;
x_2 = l_Lake_Package_mkConfigString___closed__4;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lake_Package_mkConfigString___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__12() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Package_mkConfigString___closed__10;
x_4 = l_Lake_Package_mkConfigString___closed__11;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__13() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__12;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__15;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__18() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Package_mkConfigString___closed__10;
x_4 = l_Lake_Package_mkConfigString___closed__17;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lake_Package_mkConfigString___closed__18;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__23() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lake_Package_mkConfigString___closed__10;
x_4 = l_Lake_Package_mkConfigString___closed__22;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lake_Package_mkConfigString___closed__23;
x_2 = l_Lake_Package_mkConfigString___closed__21;
x_3 = l_Lake_Package_mkConfigString___closed__20;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__28;
x_2 = l_Lake_Package_mkConfigString___closed__27;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lake_Package_mkConfigString___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__31;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at___Lean_Firefox_Profile_export_spec__9(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__33;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at___Lean_Language_Lean_process_parseCmd_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal exception #", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__37;
x_2 = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (x_2 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; lean_object* x_22; 
x_17 = 0;
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lake_Package_mkConfigString___closed__5;
x_20 = lean_box(0);
x_21 = 1024;
x_22 = l_Lake_importModulesUsingCache(x_19, x_20, x_21, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_117; uint8_t x_140; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_io_get_num_heartbeats(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_box(0);
x_30 = lean_unsigned_to_nat(2u);
x_31 = l_Lake_Package_mkConfigString___closed__8;
x_32 = l_Lake_Package_mkConfigString___closed__9;
x_33 = l_Lake_Package_mkConfigString___closed__13;
x_34 = l_Lake_Package_mkConfigString___closed__16;
x_35 = l_Lake_Package_mkConfigString___closed__19;
x_36 = l_Lake_Package_mkConfigString___closed__24;
x_37 = l_Lake_Package_mkConfigString___closed__25;
x_38 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_31);
lean_ctor_set(x_38, 3, x_32);
lean_ctor_set(x_38, 4, x_33);
lean_ctor_set(x_38, 5, x_34);
lean_ctor_set(x_38, 6, x_35);
lean_ctor_set(x_38, 7, x_36);
lean_ctor_set(x_38, 8, x_37);
x_39 = lean_st_mk_ref(x_38, x_27);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Lake_Package_mkConfigString___closed__26;
x_43 = lean_st_ref_get(x_42, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_st_ref_get(x_40, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_49);
lean_dec(x_47);
x_50 = l_Lake_Package_mkLeanConfig(x_1);
x_51 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_50);
x_52 = l_Lake_Package_mkConfigString___closed__27;
x_53 = l_Lake_Package_mkConfigString___closed__29;
x_54 = lean_box(0);
x_55 = lean_box(0);
x_56 = l_Lake_Package_mkConfigString___closed__30;
x_57 = lean_box(0);
x_58 = l_Lake_Package_mkConfigString___closed__32;
x_140 = l_Lean_Kernel_isDiagnosticsEnabled(x_49);
lean_dec_ref(x_49);
if (x_140 == 0)
{
if (x_58 == 0)
{
lean_inc(x_40);
x_59 = x_40;
x_60 = x_48;
goto block_116;
}
else
{
x_117 = x_140;
goto block_139;
}
}
else
{
x_117 = x_58;
goto block_139;
}
block_116:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = l_Lake_Package_mkConfigString___closed__34;
x_62 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_53);
lean_ctor_set(x_62, 2, x_20);
lean_ctor_set(x_62, 3, x_28);
lean_ctor_set(x_62, 4, x_61);
lean_ctor_set(x_62, 5, x_54);
lean_ctor_set(x_62, 6, x_29);
lean_ctor_set(x_62, 7, x_55);
lean_ctor_set(x_62, 8, x_26);
lean_ctor_set(x_62, 9, x_56);
lean_ctor_set(x_62, 10, x_18);
lean_ctor_set(x_62, 11, x_57);
lean_ctor_set(x_62, 12, x_44);
lean_ctor_set_uint8(x_62, sizeof(void*)*13, x_58);
lean_ctor_set_uint8(x_62, sizeof(void*)*13 + 1, x_17);
x_63 = l_Lean_PrettyPrinter_ppModule(x_51, x_62, x_59, x_60);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
x_67 = lean_st_ref_get(x_40, x_66);
lean_dec(x_40);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
x_70 = lean_unsigned_to_nat(120u);
x_71 = lean_format_pretty(x_65, x_70, x_28, x_28);
x_72 = lean_string_utf8_byte_size(x_71);
x_73 = l_Substring_takeWhileAux___at___Lean_Elab_Term_toParserDescr_isValidAtom_spec__0(x_71, x_72, x_28);
x_74 = l_Substring_takeRightWhileAux___at___Lean_Elab_Term_toParserDescr_isValidAtom_spec__1(x_71, x_73, x_72);
x_75 = lean_string_utf8_extract(x_71, x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
lean_dec_ref(x_71);
x_76 = l_Lake_Package_mkConfigString___closed__35;
x_77 = lean_string_append(x_75, x_76);
lean_ctor_set(x_63, 1, x_3);
lean_ctor_set(x_63, 0, x_77);
lean_ctor_set(x_67, 0, x_63);
return x_67;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_67, 1);
lean_inc(x_78);
lean_dec(x_67);
x_79 = lean_unsigned_to_nat(120u);
x_80 = lean_format_pretty(x_65, x_79, x_28, x_28);
x_81 = lean_string_utf8_byte_size(x_80);
x_82 = l_Substring_takeWhileAux___at___Lean_Elab_Term_toParserDescr_isValidAtom_spec__0(x_80, x_81, x_28);
x_83 = l_Substring_takeRightWhileAux___at___Lean_Elab_Term_toParserDescr_isValidAtom_spec__1(x_80, x_82, x_81);
x_84 = lean_string_utf8_extract(x_80, x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_80);
x_85 = l_Lake_Package_mkConfigString___closed__35;
x_86 = lean_string_append(x_84, x_85);
lean_ctor_set(x_63, 1, x_3);
lean_ctor_set(x_63, 0, x_86);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_63);
lean_ctor_set(x_87, 1, x_78);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_88 = lean_ctor_get(x_63, 0);
x_89 = lean_ctor_get(x_63, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_63);
x_90 = lean_st_ref_get(x_40, x_89);
lean_dec(x_40);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_unsigned_to_nat(120u);
x_94 = lean_format_pretty(x_88, x_93, x_28, x_28);
x_95 = lean_string_utf8_byte_size(x_94);
x_96 = l_Substring_takeWhileAux___at___Lean_Elab_Term_toParserDescr_isValidAtom_spec__0(x_94, x_95, x_28);
x_97 = l_Substring_takeRightWhileAux___at___Lean_Elab_Term_toParserDescr_isValidAtom_spec__1(x_94, x_96, x_95);
x_98 = lean_string_utf8_extract(x_94, x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
lean_dec_ref(x_94);
x_99 = l_Lake_Package_mkConfigString___closed__35;
x_100 = lean_string_append(x_98, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_3);
if (lean_is_scalar(x_92)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_92;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_91);
return x_102;
}
}
else
{
lean_object* x_103; 
lean_dec(x_40);
x_103 = lean_ctor_get(x_63, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_63, 1);
lean_inc(x_104);
lean_dec_ref(x_63);
x_105 = lean_ctor_get(x_103, 1);
lean_inc_ref(x_105);
lean_dec_ref(x_103);
x_106 = l_Lean_MessageData_toString(x_105, x_104);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec_ref(x_106);
x_109 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_109, 0, x_107);
x_5 = x_109;
x_6 = x_108;
goto block_16;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_63, 1);
lean_inc(x_110);
lean_dec_ref(x_63);
x_111 = lean_ctor_get(x_103, 0);
lean_inc(x_111);
lean_dec_ref(x_103);
x_112 = l_Lake_Package_mkConfigString___closed__36;
x_113 = l_Nat_reprFast(x_111);
x_114 = lean_string_append(x_112, x_113);
lean_dec_ref(x_113);
x_115 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_5 = x_115;
x_6 = x_110;
goto block_16;
}
}
}
block_139:
{
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_118 = lean_st_ref_take(x_40, x_48);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec_ref(x_118);
x_121 = !lean_is_exclusive(x_119);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_119, 0);
x_123 = lean_ctor_get(x_119, 5);
lean_dec(x_123);
x_124 = l_Lean_Kernel_enableDiag(x_122, x_58);
lean_ctor_set(x_119, 5, x_34);
lean_ctor_set(x_119, 0, x_124);
x_125 = lean_st_ref_set(x_40, x_119, x_120);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec_ref(x_125);
lean_inc(x_40);
x_59 = x_40;
x_60 = x_126;
goto block_116;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_127 = lean_ctor_get(x_119, 0);
x_128 = lean_ctor_get(x_119, 1);
x_129 = lean_ctor_get(x_119, 2);
x_130 = lean_ctor_get(x_119, 3);
x_131 = lean_ctor_get(x_119, 4);
x_132 = lean_ctor_get(x_119, 6);
x_133 = lean_ctor_get(x_119, 7);
x_134 = lean_ctor_get(x_119, 8);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_119);
x_135 = l_Lean_Kernel_enableDiag(x_127, x_58);
x_136 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_128);
lean_ctor_set(x_136, 2, x_129);
lean_ctor_set(x_136, 3, x_130);
lean_ctor_set(x_136, 4, x_131);
lean_ctor_set(x_136, 5, x_34);
lean_ctor_set(x_136, 6, x_132);
lean_ctor_set(x_136, 7, x_133);
lean_ctor_set(x_136, 8, x_134);
x_137 = lean_st_ref_set(x_40, x_136, x_120);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec_ref(x_137);
lean_inc(x_40);
x_59 = x_40;
x_60 = x_138;
goto block_116;
}
}
else
{
lean_inc(x_40);
x_59 = x_40;
x_60 = x_48;
goto block_116;
}
}
}
else
{
uint8_t x_141; 
lean_dec_ref(x_1);
x_141 = !lean_is_exclusive(x_22);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = lean_ctor_get(x_22, 0);
x_143 = lean_io_error_to_string(x_142);
x_144 = 3;
x_145 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_144);
x_146 = lean_array_get_size(x_3);
x_147 = lean_array_push(x_3, x_145);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_148);
return x_22;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_149 = lean_ctor_get(x_22, 0);
x_150 = lean_ctor_get(x_22, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_22);
x_151 = lean_io_error_to_string(x_149);
x_152 = 3;
x_153 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_152);
x_154 = lean_array_get_size(x_3);
x_155 = lean_array_push(x_3, x_153);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_150);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = l_Lake_Package_mkConfigString___closed__38;
x_159 = l_Lake_Package_mkTomlConfig(x_1, x_158);
x_160 = l_Lake_Toml_ppTable(x_159);
lean_dec_ref(x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_3);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_4);
return x_162;
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lake_Package_mkConfigString___closed__0;
x_8 = lean_io_error_to_string(x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec_ref(x_8);
x_10 = 3;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_array_get_size(x_3);
x_13 = lean_array_push(x_3, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_Package_mkConfigString(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Lake_Config_Lang(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate_Toml(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Translate(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Lang(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate_Toml(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_CLI_Translate_Lean(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Package_mkConfigString___closed__0 = _init_l_Lake_Package_mkConfigString___closed__0();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__0);
l_Lake_Package_mkConfigString___closed__1 = _init_l_Lake_Package_mkConfigString___closed__1();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__1);
l_Lake_Package_mkConfigString___closed__2 = _init_l_Lake_Package_mkConfigString___closed__2();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__2);
l_Lake_Package_mkConfigString___closed__3 = _init_l_Lake_Package_mkConfigString___closed__3();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__3);
l_Lake_Package_mkConfigString___closed__4 = _init_l_Lake_Package_mkConfigString___closed__4();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__4);
l_Lake_Package_mkConfigString___closed__5 = _init_l_Lake_Package_mkConfigString___closed__5();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__5);
l_Lake_Package_mkConfigString___closed__6 = _init_l_Lake_Package_mkConfigString___closed__6();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__6);
l_Lake_Package_mkConfigString___closed__7 = _init_l_Lake_Package_mkConfigString___closed__7();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__7);
l_Lake_Package_mkConfigString___closed__8 = _init_l_Lake_Package_mkConfigString___closed__8();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__8);
l_Lake_Package_mkConfigString___closed__9 = _init_l_Lake_Package_mkConfigString___closed__9();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__9);
l_Lake_Package_mkConfigString___closed__10 = _init_l_Lake_Package_mkConfigString___closed__10();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__10);
l_Lake_Package_mkConfigString___closed__11 = _init_l_Lake_Package_mkConfigString___closed__11();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__11);
l_Lake_Package_mkConfigString___closed__12 = _init_l_Lake_Package_mkConfigString___closed__12();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__12);
l_Lake_Package_mkConfigString___closed__13 = _init_l_Lake_Package_mkConfigString___closed__13();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__13);
l_Lake_Package_mkConfigString___closed__14 = _init_l_Lake_Package_mkConfigString___closed__14();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__14);
l_Lake_Package_mkConfigString___closed__15 = _init_l_Lake_Package_mkConfigString___closed__15();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__15);
l_Lake_Package_mkConfigString___closed__16 = _init_l_Lake_Package_mkConfigString___closed__16();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__16);
l_Lake_Package_mkConfigString___closed__17 = _init_l_Lake_Package_mkConfigString___closed__17();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__17);
l_Lake_Package_mkConfigString___closed__18 = _init_l_Lake_Package_mkConfigString___closed__18();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__18);
l_Lake_Package_mkConfigString___closed__19 = _init_l_Lake_Package_mkConfigString___closed__19();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__19);
l_Lake_Package_mkConfigString___closed__20 = _init_l_Lake_Package_mkConfigString___closed__20();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__20);
l_Lake_Package_mkConfigString___closed__21 = _init_l_Lake_Package_mkConfigString___closed__21();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__21);
l_Lake_Package_mkConfigString___closed__22 = _init_l_Lake_Package_mkConfigString___closed__22();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__22);
l_Lake_Package_mkConfigString___closed__23 = _init_l_Lake_Package_mkConfigString___closed__23();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__23);
l_Lake_Package_mkConfigString___closed__24 = _init_l_Lake_Package_mkConfigString___closed__24();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__24);
l_Lake_Package_mkConfigString___closed__25 = _init_l_Lake_Package_mkConfigString___closed__25();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__25);
l_Lake_Package_mkConfigString___closed__26 = _init_l_Lake_Package_mkConfigString___closed__26();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__26);
l_Lake_Package_mkConfigString___closed__27 = _init_l_Lake_Package_mkConfigString___closed__27();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__27);
l_Lake_Package_mkConfigString___closed__28 = _init_l_Lake_Package_mkConfigString___closed__28();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__28);
l_Lake_Package_mkConfigString___closed__29 = _init_l_Lake_Package_mkConfigString___closed__29();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__29);
l_Lake_Package_mkConfigString___closed__30 = _init_l_Lake_Package_mkConfigString___closed__30();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__30);
l_Lake_Package_mkConfigString___closed__31 = _init_l_Lake_Package_mkConfigString___closed__31();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__31);
l_Lake_Package_mkConfigString___closed__32 = _init_l_Lake_Package_mkConfigString___closed__32();
l_Lake_Package_mkConfigString___closed__33 = _init_l_Lake_Package_mkConfigString___closed__33();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__33);
l_Lake_Package_mkConfigString___closed__34 = _init_l_Lake_Package_mkConfigString___closed__34();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__34);
l_Lake_Package_mkConfigString___closed__35 = _init_l_Lake_Package_mkConfigString___closed__35();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__35);
l_Lake_Package_mkConfigString___closed__36 = _init_l_Lake_Package_mkConfigString___closed__36();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__36);
l_Lake_Package_mkConfigString___closed__37 = _init_l_Lake_Package_mkConfigString___closed__37();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__37);
l_Lake_Package_mkConfigString___closed__38 = _init_l_Lake_Package_mkConfigString___closed__38();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__38);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
