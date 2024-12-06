// Lean compiler output
// Module: Lake.CLI.Translate
// Imports: Lake.Config.Lang Lake.Config.Package Lake.CLI.Translate.Toml Lake.CLI.Translate.Lean Lake.Load.Lean.Elab Lean.PrettyPrinter
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___lambda__1___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty___rarg(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__26;
static lean_object* l_Lake_Package_mkConfigString___closed__3;
static lean_object* l_Lake_Package_mkConfigString___closed__24;
static lean_object* l_Lake_Package_mkConfigString___closed__29;
lean_object* lean_io_get_num_heartbeats(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__21;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__13;
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__12;
static lean_object* l_Lake_Package_mkConfigString___closed__14;
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___rarg(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__16;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__6;
static lean_object* l_Lake_Package_mkConfigString___closed__7;
static uint8_t l_Lake_Package_mkConfigString___closed__28;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__9;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lake_Package_mkConfigString___closed__8;
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__30;
static lean_object* l_Lake_Package_mkConfigString___closed__25;
static lean_object* l_Lake_Package_mkConfigString___closed__23;
static lean_object* l_Lake_Package_mkConfigString___closed__15;
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lake_Package_mkConfigString___closed__2;
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Translate_0__Lake_descopeSyntax___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Package_mkLeanConfig(lean_object*);
lean_object* l_Lake_Package_mkTomlConfig(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__20;
static lean_object* l_Lake_Package_mkConfigString___closed__22;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Translate_0__Lake_descopeSyntax___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__11;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lake_Toml_ppTable(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__4;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__5;
static lean_object* l_Lake_Package_mkConfigString___closed__17;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__19;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__18;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Translate_0__Lake_descopeSyntax___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Translate_0__Lake_descopeSyntax___spec__1(x_4, x_5, x_3);
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
x_12 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Translate_0__Lake_descopeSyntax___spec__1(x_10, x_11, x_9);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Translate_0__Lake_descopeSyntax___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Translate_0__Lake_descopeSyntax___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_5, 4);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_dec(x_10);
x_11 = l_Lake_Package_mkConfigString___lambda__1___closed__1;
x_12 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_11);
lean_ctor_set(x_5, 4, x_12);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*12, x_2);
x_13 = l_Lean_PrettyPrinter_ppModule(x_3, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 3);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get(x_5, 11);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*12 + 1);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_25 = l_Lake_Package_mkConfigString___lambda__1___closed__1;
x_26 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_25);
x_27 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_1);
lean_ctor_set(x_27, 3, x_16);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_17);
lean_ctor_set(x_27, 6, x_18);
lean_ctor_set(x_27, 7, x_19);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set(x_27, 9, x_21);
lean_ctor_set(x_27, 10, x_22);
lean_ctor_set(x_27, 11, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_27, sizeof(void*)*12 + 1, x_24);
x_28 = l_Lean_PrettyPrinter_ppModule(x_3, x_27, x_6, x_7);
return x_28;
}
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(internal) failed to pretty print Lean configuration: ", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkConfigString___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkConfigString___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__7;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__2;
x_2 = l_Lake_Package_mkConfigString___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkConfigString___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__14;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__16;
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
x_2 = l_Lake_Package_mkConfigString___closed__17;
x_3 = l_Lake_Package_mkConfigString___closed__16;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__19() {
_start:
{
uint64_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lake_Package_mkConfigString___closed__18;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__21;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__23() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lake_Package_mkConfigString___closed__18;
x_3 = l_Lean_NameSet_empty;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__24() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lake_Package_mkConfigString___closed__21;
x_3 = l_Lake_Package_mkConfigString___closed__18;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal exception #", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lake_Package_mkConfigString___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Package_mkConfigString___closed__27;
x_3 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__29;
x_2 = l_Lake_Toml_RBDict_empty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (x_2 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint32_t x_269; lean_object* x_270; lean_object* x_271; 
x_93 = lean_box(0);
x_269 = 1024;
x_270 = l_Lake_Package_mkConfigString___closed__8;
x_271 = l_Lake_importModulesUsingCache(x_270, x_93, x_269, x_4);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_271, 1);
lean_ctor_set(x_271, 1, x_3);
x_94 = x_271;
x_95 = x_273;
goto block_268;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_271, 0);
x_275 = lean_ctor_get(x_271, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_271);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_3);
x_94 = x_276;
x_95 = x_275;
goto block_268;
}
}
else
{
uint8_t x_277; 
x_277 = !lean_is_exclusive(x_271);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_278 = lean_ctor_get(x_271, 0);
x_279 = lean_ctor_get(x_271, 1);
x_280 = lean_io_error_to_string(x_278);
x_281 = 3;
x_282 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set_uint8(x_282, sizeof(void*)*1, x_281);
x_283 = lean_array_get_size(x_3);
x_284 = lean_array_push(x_3, x_282);
lean_ctor_set(x_271, 1, x_284);
lean_ctor_set(x_271, 0, x_283);
x_94 = x_271;
x_95 = x_279;
goto block_268;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_285 = lean_ctor_get(x_271, 0);
x_286 = lean_ctor_get(x_271, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_271);
x_287 = lean_io_error_to_string(x_285);
x_288 = 3;
x_289 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set_uint8(x_289, sizeof(void*)*1, x_288);
x_290 = lean_array_get_size(x_3);
x_291 = lean_array_push(x_3, x_289);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_94 = x_292;
x_95 = x_286;
goto block_268;
}
}
block_268:
{
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_130; lean_object* x_131; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_180; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_98 = x_94;
} else {
 lean_dec_ref(x_94);
 x_98 = lean_box(0);
}
x_99 = l_Lake_Package_mkLeanConfig(x_1);
x_100 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_99);
x_101 = lean_box(0);
x_102 = l_Lake_Package_mkConfigString___closed__12;
x_103 = l_Lake_Package_mkConfigString___closed__15;
x_104 = l_Lake_Package_mkConfigString___closed__19;
x_105 = l_Lake_Package_mkConfigString___closed__22;
x_106 = l_Lake_Package_mkConfigString___closed__23;
x_107 = l_Lake_Package_mkConfigString___closed__24;
x_108 = l_Lake_Package_mkConfigString___closed__25;
x_109 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_109, 0, x_96);
lean_ctor_set(x_109, 1, x_102);
lean_ctor_set(x_109, 2, x_103);
lean_ctor_set(x_109, 3, x_104);
lean_ctor_set(x_109, 4, x_105);
lean_ctor_set(x_109, 5, x_106);
lean_ctor_set(x_109, 6, x_107);
lean_ctor_set(x_109, 7, x_108);
x_159 = lean_io_get_num_heartbeats(x_95);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l_Lake_Package_mkConfigString___closed__2;
x_163 = l_Lake_Package_mkConfigString___closed__10;
x_164 = lean_unsigned_to_nat(0u);
x_165 = lean_unsigned_to_nat(1000u);
x_166 = lean_box(0);
x_167 = lean_box(0);
x_168 = l_Lake_Package_mkConfigString___closed__11;
x_169 = l_Lean_firstFrontendMacroScope;
x_170 = 0;
x_171 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_171, 0, x_162);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_93);
lean_ctor_set(x_171, 3, x_164);
lean_ctor_set(x_171, 4, x_165);
lean_ctor_set(x_171, 5, x_166);
lean_ctor_set(x_171, 6, x_167);
lean_ctor_set(x_171, 7, x_93);
lean_ctor_set(x_171, 8, x_160);
lean_ctor_set(x_171, 9, x_168);
lean_ctor_set(x_171, 10, x_169);
lean_ctor_set(x_171, 11, x_101);
lean_ctor_set_uint8(x_171, sizeof(void*)*12, x_170);
lean_ctor_set_uint8(x_171, sizeof(void*)*12 + 1, x_170);
x_172 = lean_st_mk_ref(x_109, x_161);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_st_ref_get(x_173, x_174);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec(x_176);
x_179 = l_Lean_Kernel_isDiagnosticsEnabled(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
uint8_t x_258; 
x_258 = l_Lake_Package_mkConfigString___closed__28;
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = 1;
x_180 = x_259;
goto block_257;
}
else
{
x_180 = x_170;
goto block_257;
}
}
else
{
uint8_t x_260; 
x_260 = l_Lake_Package_mkConfigString___closed__28;
if (x_260 == 0)
{
x_180 = x_170;
goto block_257;
}
else
{
uint8_t x_261; 
x_261 = 1;
x_180 = x_261;
goto block_257;
}
}
block_129:
{
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (lean_is_scalar(x_98)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_98;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_97);
lean_ctor_set(x_110, 0, x_114);
x_5 = x_110;
goto block_92;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_110, 0);
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_110);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_115);
if (lean_is_scalar(x_98)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_98;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_97);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
x_5 = x_119;
goto block_92;
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_110);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_110, 0);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
if (lean_is_scalar(x_98)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_98;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_97);
lean_ctor_set_tag(x_110, 0);
lean_ctor_set(x_110, 0, x_123);
x_5 = x_110;
goto block_92;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_110, 0);
x_125 = lean_ctor_get(x_110, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_110);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_124);
if (lean_is_scalar(x_98)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_98;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_97);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
x_5 = x_128;
goto block_92;
}
}
}
block_158:
{
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_MessageData_toString(x_132, x_131);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
x_136 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 0, x_136);
x_110 = x_133;
goto block_129;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_133, 0);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_133);
x_139 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_139, 0, x_137);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_110 = x_140;
goto block_129;
}
}
else
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_133);
if (x_141 == 0)
{
x_110 = x_133;
goto block_129;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_133, 0);
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_133);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_110 = x_144;
goto block_129;
}
}
}
else
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_130);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_130, 0);
x_147 = lean_ctor_get(x_130, 1);
lean_dec(x_147);
x_148 = l___private_Init_Data_Repr_0__Nat_reprFast(x_146);
x_149 = l_Lake_Package_mkConfigString___closed__26;
x_150 = lean_string_append(x_149, x_148);
lean_dec(x_148);
x_151 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_130, 1, x_131);
lean_ctor_set(x_130, 0, x_151);
x_110 = x_130;
goto block_129;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_130, 0);
lean_inc(x_152);
lean_dec(x_130);
x_153 = l___private_Init_Data_Repr_0__Nat_reprFast(x_152);
x_154 = l_Lake_Package_mkConfigString___closed__26;
x_155 = lean_string_append(x_154, x_153);
lean_dec(x_153);
x_156 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_131);
x_110 = x_157;
goto block_129;
}
}
}
block_257:
{
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_st_ref_take(x_173, x_177);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = !lean_is_exclusive(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_185 = lean_ctor_get(x_182, 0);
x_186 = lean_ctor_get(x_182, 4);
lean_dec(x_186);
x_187 = l_Lake_Package_mkConfigString___closed__28;
x_188 = l_Lean_Kernel_enableDiag(x_185, x_187);
lean_ctor_set(x_182, 4, x_105);
lean_ctor_set(x_182, 0, x_188);
x_189 = lean_st_ref_set(x_173, x_182, x_183);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_box(0);
lean_inc(x_173);
x_192 = l_Lake_Package_mkConfigString___lambda__1(x_93, x_187, x_100, x_191, x_171, x_173, x_190);
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_192, 1);
x_195 = lean_st_ref_get(x_173, x_194);
lean_dec(x_173);
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_195, 0);
lean_ctor_set(x_192, 1, x_197);
lean_ctor_set(x_195, 0, x_192);
x_110 = x_195;
goto block_129;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_195, 0);
x_199 = lean_ctor_get(x_195, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_195);
lean_ctor_set(x_192, 1, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_192);
lean_ctor_set(x_200, 1, x_199);
x_110 = x_200;
goto block_129;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_201 = lean_ctor_get(x_192, 0);
x_202 = lean_ctor_get(x_192, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_192);
x_203 = lean_st_ref_get(x_173, x_202);
lean_dec(x_173);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_206 = x_203;
} else {
 lean_dec_ref(x_203);
 x_206 = lean_box(0);
}
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_201);
lean_ctor_set(x_207, 1, x_204);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
x_110 = x_208;
goto block_129;
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_173);
x_209 = lean_ctor_get(x_192, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_192, 1);
lean_inc(x_210);
lean_dec(x_192);
x_130 = x_209;
x_131 = x_210;
goto block_158;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_211 = lean_ctor_get(x_182, 0);
x_212 = lean_ctor_get(x_182, 1);
x_213 = lean_ctor_get(x_182, 2);
x_214 = lean_ctor_get(x_182, 3);
x_215 = lean_ctor_get(x_182, 5);
x_216 = lean_ctor_get(x_182, 6);
x_217 = lean_ctor_get(x_182, 7);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_182);
x_218 = l_Lake_Package_mkConfigString___closed__28;
x_219 = l_Lean_Kernel_enableDiag(x_211, x_218);
x_220 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_212);
lean_ctor_set(x_220, 2, x_213);
lean_ctor_set(x_220, 3, x_214);
lean_ctor_set(x_220, 4, x_105);
lean_ctor_set(x_220, 5, x_215);
lean_ctor_set(x_220, 6, x_216);
lean_ctor_set(x_220, 7, x_217);
x_221 = lean_st_ref_set(x_173, x_220, x_183);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_223 = lean_box(0);
lean_inc(x_173);
x_224 = l_Lake_Package_mkConfigString___lambda__1(x_93, x_218, x_100, x_223, x_171, x_173, x_222);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
x_228 = lean_st_ref_get(x_173, x_226);
lean_dec(x_173);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_231 = x_228;
} else {
 lean_dec_ref(x_228);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_227;
}
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_229);
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_230);
x_110 = x_233;
goto block_129;
}
else
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_173);
x_234 = lean_ctor_get(x_224, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_224, 1);
lean_inc(x_235);
lean_dec(x_224);
x_130 = x_234;
x_131 = x_235;
goto block_158;
}
}
}
else
{
uint8_t x_236; lean_object* x_237; lean_object* x_238; 
x_236 = l_Lake_Package_mkConfigString___closed__28;
x_237 = lean_box(0);
lean_inc(x_173);
x_238 = l_Lake_Package_mkConfigString___lambda__1(x_93, x_236, x_100, x_237, x_171, x_173, x_177);
if (lean_obj_tag(x_238) == 0)
{
uint8_t x_239; 
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_240 = lean_ctor_get(x_238, 1);
x_241 = lean_st_ref_get(x_173, x_240);
lean_dec(x_173);
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_241, 0);
lean_ctor_set(x_238, 1, x_243);
lean_ctor_set(x_241, 0, x_238);
x_110 = x_241;
goto block_129;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_241, 0);
x_245 = lean_ctor_get(x_241, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_241);
lean_ctor_set(x_238, 1, x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_238);
lean_ctor_set(x_246, 1, x_245);
x_110 = x_246;
goto block_129;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_247 = lean_ctor_get(x_238, 0);
x_248 = lean_ctor_get(x_238, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_238);
x_249 = lean_st_ref_get(x_173, x_248);
lean_dec(x_173);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_252 = x_249;
} else {
 lean_dec_ref(x_249);
 x_252 = lean_box(0);
}
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_247);
lean_ctor_set(x_253, 1, x_250);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_252;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
x_110 = x_254;
goto block_129;
}
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_173);
x_255 = lean_ctor_get(x_238, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_238, 1);
lean_inc(x_256);
lean_dec(x_238);
x_130 = x_255;
x_131 = x_256;
goto block_158;
}
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_94);
if (x_262 == 0)
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_94);
lean_ctor_set(x_263, 1, x_95);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_94, 0);
x_265 = lean_ctor_get(x_94, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_94);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_95);
return x_267;
}
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = l_Lake_Package_mkConfigString___closed__30;
x_294 = l_Lake_Package_mkTomlConfig(x_1, x_293);
x_295 = l_Lake_Toml_ppTable(x_294);
lean_dec(x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_3);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_4);
return x_297;
}
block_92:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_io_error_to_string(x_13);
x_15 = l_Lake_Package_mkConfigString___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lake_Package_mkConfigString___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_get_size(x_11);
x_22 = lean_array_push(x_11, x_20);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_22);
lean_ctor_set(x_6, 0, x_21);
return x_5;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_24);
lean_dec(x_7);
x_25 = lean_io_error_to_string(x_24);
x_26 = l_Lake_Package_mkConfigString___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lake_Package_mkConfigString___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_get_size(x_23);
x_33 = lean_array_push(x_23, x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_5, 0, x_34);
return x_5;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_37 = x_6;
} else {
 lean_dec_ref(x_6);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_7, 0);
lean_inc(x_38);
lean_dec(x_7);
x_39 = lean_io_error_to_string(x_38);
x_40 = l_Lake_Package_mkConfigString___closed__1;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lake_Package_mkConfigString___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = 3;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_array_get_size(x_36);
x_47 = lean_array_push(x_36, x_45);
if (lean_is_scalar(x_37)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_37;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_35);
return x_49;
}
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_7, 0);
lean_inc(x_50);
lean_dec(x_7);
x_51 = !lean_is_exclusive(x_5);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_5, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_6);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_6, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec(x_50);
x_56 = l_Std_Format_defWidth;
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_format_pretty(x_55, x_56, x_57, x_57);
x_59 = lean_string_utf8_byte_size(x_58);
x_60 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_58, x_59, x_57);
x_61 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_58, x_60, x_59);
x_62 = lean_string_utf8_extract(x_58, x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
x_63 = l_Lake_Package_mkConfigString___closed__3;
x_64 = lean_string_append(x_62, x_63);
lean_ctor_set(x_6, 0, x_64);
return x_5;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_6, 1);
lean_inc(x_65);
lean_dec(x_6);
x_66 = lean_ctor_get(x_50, 0);
lean_inc(x_66);
lean_dec(x_50);
x_67 = l_Std_Format_defWidth;
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_format_pretty(x_66, x_67, x_68, x_68);
x_70 = lean_string_utf8_byte_size(x_69);
x_71 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_69, x_70, x_68);
x_72 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_69, x_71, x_70);
x_73 = lean_string_utf8_extract(x_69, x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
x_74 = l_Lake_Package_mkConfigString___closed__3;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_65);
lean_ctor_set(x_5, 0, x_76);
return x_5;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_77 = lean_ctor_get(x_5, 1);
lean_inc(x_77);
lean_dec(x_5);
x_78 = lean_ctor_get(x_6, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_79 = x_6;
} else {
 lean_dec_ref(x_6);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_50, 0);
lean_inc(x_80);
lean_dec(x_50);
x_81 = l_Std_Format_defWidth;
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_format_pretty(x_80, x_81, x_82, x_82);
x_84 = lean_string_utf8_byte_size(x_83);
x_85 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_83, x_84, x_82);
x_86 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_83, x_85, x_84);
x_87 = lean_string_utf8_extract(x_83, x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_83);
x_88 = l_Lake_Package_mkConfigString___closed__3;
x_89 = lean_string_append(x_87, x_88);
if (lean_is_scalar(x_79)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_79;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_78);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_77);
return x_91;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lake_Package_mkConfigString___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_Package_mkConfigString(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* initialize_Lake_Config_Lang(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate_Toml(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
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
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Package_mkConfigString___lambda__1___closed__1 = _init_l_Lake_Package_mkConfigString___lambda__1___closed__1();
lean_mark_persistent(l_Lake_Package_mkConfigString___lambda__1___closed__1);
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
l_Lake_Package_mkConfigString___closed__29 = _init_l_Lake_Package_mkConfigString___closed__29();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__29);
l_Lake_Package_mkConfigString___closed__30 = _init_l_Lake_Package_mkConfigString___closed__30();
lean_mark_persistent(l_Lake_Package_mkConfigString___closed__30);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
