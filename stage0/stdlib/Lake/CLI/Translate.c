// Lean compiler output
// Module: Lake.CLI.Translate
// Imports: Init Lake.Load.Elab Lake.Config.Lang Lake.Config.Package Lake.CLI.Translate.Toml Lake.CLI.Translate.Lean Lean.PrettyPrinter
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__10;
static lean_object* l_Lake_Package_mkConfigString___closed__27;
static lean_object* l_Lake_Package_mkConfigString___closed__1;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lake_Toml_RBDict_empty___rarg(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__26;
static lean_object* l_Lake_Package_mkConfigString___closed__3;
static lean_object* l_Lake_Package_mkConfigString___closed__24;
lean_object* lean_io_get_num_heartbeats(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__21;
lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__13;
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__12;
static lean_object* l_Lake_Package_mkConfigString___closed__14;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Translate_0__Lake_descopeTSyntax___rarg(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__16;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__6;
static lean_object* l_Lake_Package_mkConfigString___closed__7;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__9;
static lean_object* l_Lake_Package_mkConfigString___closed__8;
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lake_Package_mkConfigString___closed__25;
static lean_object* l_Lake_Package_mkConfigString___closed__23;
static lean_object* l_Lake_Package_mkConfigString___closed__15;
static lean_object* l_Lake_Package_mkConfigString___closed__2;
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
lean_object* l_Lake_Toml_ppTable(lean_object*);
static lean_object* l_Lake_Package_mkConfigString___closed__4;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
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
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Translate_0__Lake_descopeSyntax___spec__1(x_5, x_6, x_3);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Translate_0__Lake_descopeSyntax___spec__1(x_12, x_13, x_10);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
case 3:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_erase_macro_scopes(x_17);
lean_ctor_set(x_1, 2, x_18);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = lean_erase_macro_scopes(x_21);
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_22);
return x_24;
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
static lean_object* _init_l_Lake_Package_mkConfigString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(internal) failed to pretty print Lean configuration: ", 54);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lake", 4);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__7;
x_2 = l_Lake_Package_mkConfigString___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
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
x_1 = lean_mk_string_from_bytes("_uniq", 5);
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
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__19;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__20;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_mkConfigString___closed__20;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__24() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lake_Package_mkConfigString___closed__23;
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("internal exception #", 20);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Package_mkConfigString___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Package_mkConfigString___closed__26;
x_2 = l_Lake_Toml_RBDict_empty___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_mkConfigString(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (x_2 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint32_t x_175; lean_object* x_176; lean_object* x_177; 
x_57 = lean_box(0);
x_175 = 1024;
x_176 = l_Lake_Package_mkConfigString___closed__8;
x_177 = l_Lake_importModulesUsingCache(x_176, x_57, x_175, x_4);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_3);
x_58 = x_180;
x_59 = x_179;
goto block_174;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_181 = lean_ctor_get(x_177, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_177, 1);
lean_inc(x_182);
lean_dec(x_177);
x_183 = lean_io_error_to_string(x_181);
x_184 = 3;
x_185 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set_uint8(x_185, sizeof(void*)*1, x_184);
x_186 = lean_array_get_size(x_3);
x_187 = lean_array_push(x_3, x_185);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_58 = x_188;
x_59 = x_182;
goto block_174;
}
block_174:
{
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_61 = lean_ctor_get(x_58, 0);
x_62 = l_Lake_Package_mkLeanConfig(x_1);
x_63 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_62);
x_64 = l_Lake_Package_mkConfigString___closed__12;
x_65 = l_Lake_Package_mkConfigString___closed__15;
x_66 = l_Lake_Package_mkConfigString___closed__18;
x_67 = l_Lake_Package_mkConfigString___closed__22;
x_68 = l_Lake_Package_mkConfigString___closed__24;
x_69 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_66);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set(x_69, 5, x_66);
lean_ctor_set(x_69, 6, x_68);
x_70 = lean_io_get_num_heartbeats(x_59);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lake_Package_mkConfigString___closed__2;
x_74 = l_Lake_Package_mkConfigString___closed__10;
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_unsigned_to_nat(1000u);
x_77 = lean_box(0);
x_78 = lean_box(0);
x_79 = l_Lake_Package_mkConfigString___closed__11;
x_80 = l_Lean_firstFrontendMacroScope;
x_81 = 0;
x_82 = lean_alloc_ctor(0, 11, 2);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_57);
lean_ctor_set(x_82, 3, x_75);
lean_ctor_set(x_82, 4, x_76);
lean_ctor_set(x_82, 5, x_77);
lean_ctor_set(x_82, 6, x_78);
lean_ctor_set(x_82, 7, x_57);
lean_ctor_set(x_82, 8, x_71);
lean_ctor_set(x_82, 9, x_79);
lean_ctor_set(x_82, 10, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*11, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*11 + 1, x_81);
x_83 = lean_st_mk_ref(x_69, x_72);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_84);
x_86 = l_Lean_PrettyPrinter_ppModule(x_63, x_82, x_84, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_st_ref_get(x_84, x_88);
lean_dec(x_84);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_58, 0, x_93);
x_5 = x_58;
x_6 = x_91;
goto block_56;
}
else
{
lean_object* x_94; 
lean_dec(x_84);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
lean_dec(x_86);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_MessageData_toString(x_96, x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_100, 0, x_98);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_58, 0, x_101);
x_5 = x_58;
x_6 = x_99;
goto block_56;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 1);
lean_inc(x_103);
lean_dec(x_97);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_58, 0, x_104);
x_5 = x_58;
x_6 = x_103;
goto block_56;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_86, 1);
lean_inc(x_105);
lean_dec(x_86);
x_106 = lean_ctor_get(x_94, 0);
lean_inc(x_106);
lean_dec(x_94);
x_107 = l___private_Init_Data_Repr_0__Nat_reprFast(x_106);
x_108 = l_Lake_Package_mkConfigString___closed__25;
x_109 = lean_string_append(x_108, x_107);
lean_dec(x_107);
x_110 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_58, 0, x_111);
x_5 = x_58;
x_6 = x_105;
goto block_56;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_112 = lean_ctor_get(x_58, 0);
x_113 = lean_ctor_get(x_58, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_58);
x_114 = l_Lake_Package_mkLeanConfig(x_1);
x_115 = l___private_Lake_CLI_Translate_0__Lake_descopeSyntax(x_114);
x_116 = l_Lake_Package_mkConfigString___closed__12;
x_117 = l_Lake_Package_mkConfigString___closed__15;
x_118 = l_Lake_Package_mkConfigString___closed__18;
x_119 = l_Lake_Package_mkConfigString___closed__22;
x_120 = l_Lake_Package_mkConfigString___closed__24;
x_121 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_121, 0, x_112);
lean_ctor_set(x_121, 1, x_116);
lean_ctor_set(x_121, 2, x_117);
lean_ctor_set(x_121, 3, x_118);
lean_ctor_set(x_121, 4, x_119);
lean_ctor_set(x_121, 5, x_118);
lean_ctor_set(x_121, 6, x_120);
x_122 = lean_io_get_num_heartbeats(x_59);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lake_Package_mkConfigString___closed__2;
x_126 = l_Lake_Package_mkConfigString___closed__10;
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_unsigned_to_nat(1000u);
x_129 = lean_box(0);
x_130 = lean_box(0);
x_131 = l_Lake_Package_mkConfigString___closed__11;
x_132 = l_Lean_firstFrontendMacroScope;
x_133 = 0;
x_134 = lean_alloc_ctor(0, 11, 2);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_57);
lean_ctor_set(x_134, 3, x_127);
lean_ctor_set(x_134, 4, x_128);
lean_ctor_set(x_134, 5, x_129);
lean_ctor_set(x_134, 6, x_130);
lean_ctor_set(x_134, 7, x_57);
lean_ctor_set(x_134, 8, x_123);
lean_ctor_set(x_134, 9, x_131);
lean_ctor_set(x_134, 10, x_132);
lean_ctor_set_uint8(x_134, sizeof(void*)*11, x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*11 + 1, x_133);
x_135 = lean_st_mk_ref(x_121, x_124);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_136);
x_138 = l_Lean_PrettyPrinter_ppModule(x_115, x_134, x_136, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_st_ref_get(x_136, x_140);
lean_dec(x_136);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_139);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_113);
x_5 = x_146;
x_6 = x_143;
goto block_56;
}
else
{
lean_object* x_147; 
lean_dec(x_136);
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_138, 1);
lean_inc(x_148);
lean_dec(x_138);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_MessageData_toString(x_149, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_153, 0, x_151);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_113);
x_5 = x_155;
x_6 = x_152;
goto block_56;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_150, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_150, 1);
lean_inc(x_157);
lean_dec(x_150);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_156);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_113);
x_5 = x_159;
x_6 = x_157;
goto block_56;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_ctor_get(x_138, 1);
lean_inc(x_160);
lean_dec(x_138);
x_161 = lean_ctor_get(x_147, 0);
lean_inc(x_161);
lean_dec(x_147);
x_162 = l___private_Init_Data_Repr_0__Nat_reprFast(x_161);
x_163 = l_Lake_Package_mkConfigString___closed__25;
x_164 = lean_string_append(x_163, x_162);
lean_dec(x_162);
x_165 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_113);
x_5 = x_167;
x_6 = x_160;
goto block_56;
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_58);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_58);
lean_ctor_set(x_169, 1, x_59);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_58, 0);
x_171 = lean_ctor_get(x_58, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_58);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_59);
return x_173;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = l_Lake_Package_mkConfigString___closed__27;
x_190 = l_Lake_Package_mkTomlConfig(x_1, x_189);
x_191 = l_Lake_Toml_ppTable(x_190);
lean_dec(x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_3);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_4);
return x_193;
}
block_56:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_io_error_to_string(x_11);
x_13 = l_Lake_Package_mkConfigString___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lake_Package_mkConfigString___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = 3;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_get_size(x_9);
x_20 = lean_array_push(x_9, x_18);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_io_error_to_string(x_23);
x_25 = l_Lake_Package_mkConfigString___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lake_Package_mkConfigString___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_array_get_size(x_22);
x_32 = lean_array_push(x_22, x_30);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
lean_dec(x_7);
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_5, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Std_Format_defWidth;
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_format_pretty(x_38, x_39, x_40, x_40);
x_42 = l_String_trim(x_41);
lean_dec(x_41);
x_43 = l_Lake_Package_mkConfigString___closed__3;
x_44 = lean_string_append(x_42, x_43);
lean_ctor_set(x_5, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_6);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
lean_dec(x_5);
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec(x_35);
x_48 = l_Std_Format_defWidth;
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_format_pretty(x_47, x_48, x_49, x_49);
x_51 = l_String_trim(x_50);
lean_dec(x_50);
x_52 = l_Lake_Package_mkConfigString___closed__3;
x_53 = lean_string_append(x_51, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_6);
return x_55;
}
}
}
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Lang(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate_Toml(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_CLI_Translate_Lean(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Translate(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
