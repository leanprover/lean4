// Lean compiler output
// Module: Lake.CLI.Error
// Imports: Init.Data.ToString Init.System.FilePath
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
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__18;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__93;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__5;
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__73;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__96;
static lean_object* l_Lake_CliError_toString___closed__31;
static lean_object* l_Lake_CliError_toString___closed__6;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__84;
LEAN_EXPORT lean_object* l_Lake_instInhabitedCliError;
LEAN_EXPORT lean_object* l_Lake_CliError_toString___lambda__1___boxed(lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__38;
static lean_object* l_Lake_CliError_toString___closed__33;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__81;
static lean_object* l_Lake_CliError_toString___closed__27;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__62;
static lean_object* l_Lake_CliError_toString___closed__19;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__91;
static lean_object* l_Lake_CliError_toString___closed__16;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__59;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__45;
static lean_object* l_Lake_CliError_toString___closed__32;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__37;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__2;
static lean_object* l_Lake_CliError_toString___closed__17;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__99;
static lean_object* l_Lake_CliError_toString___closed__10;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__85;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__49;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__10;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__53;
static lean_object* l_Lake_CliError_toString___closed__21;
static lean_object* l_Lake_CliError_toString___closed__1;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__94;
static lean_object* l_Lake_CliError_toString___closed__38;
LEAN_EXPORT lean_object* l_Lake_instReprCliError;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__69;
lean_object* l_List_repr_x27___at___private_Init_Meta_0__Lean_Syntax_reprPreresolved____x40_Init_Meta___hyg_2064____spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_CliError_toString___closed__8;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__39;
static lean_object* l_Lake_CliError_toString___closed__37;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__31;
static lean_object* l_Lake_CliError_toString___closed__34;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__27;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__30;
static lean_object* l_Lake_CliError_toString___closed__7;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__72;
static lean_object* l_Lake_CliError_toString___closed__22;
static lean_object* l_Lake_CliError_toString___closed__15;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__50;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__48;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__34;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__25;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__70;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__15;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__44;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__40;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__32;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__23;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__80;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__1;
static lean_object* l_Lake_CliError_instToString___closed__1;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__8;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__58;
static lean_object* l_Lake_CliError_toString___closed__18;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__21;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__4;
static lean_object* l_Lake_CliError_toString___closed__5;
LEAN_EXPORT lean_object* l_Lake_CliError_toString(lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__60;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__42;
static lean_object* l_Lake_CliError_toString___closed__25;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__19;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__63;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__95;
lean_object* l_Char_quote(uint32_t);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__68;
static lean_object* l_Lake_CliError_toString___closed__41;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__52;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__55;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__97;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__88;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306_(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__101;
static lean_object* l_Lake_CliError_toString___closed__13;
static lean_object* l_Lake_CliError_toString___closed__30;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__28;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__61;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__76;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__77;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__41;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__83;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__16;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__82;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__98;
static lean_object* l_Lake_CliError_toString___closed__3;
static lean_object* l_Lake_CliError_toString___closed__20;
LEAN_EXPORT lean_object* l_Lake_CliError_instToString;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__71;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__79;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__47;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__43;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__11;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__22;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__17;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__65;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__56;
static lean_object* l_Lake_CliError_toString___closed__39;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__20;
static lean_object* l_Lake_CliError_toString___closed__23;
static lean_object* l_Lake_CliError_toString___closed__36;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__87;
static lean_object* l_Lake_CliError_toString___closed__2;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__78;
static lean_object* l_Lake_CliError_toString___closed__9;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__90;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__54;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__74;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__103;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__12;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__92;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__33;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Lake_CliError_toString___closed__24;
static lean_object* l_Lake_CliError_toString___closed__14;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__64;
static lean_object* l_Lake_CliError_toString___closed__35;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__89;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__9;
LEAN_EXPORT uint8_t l_Lake_CliError_toString___lambda__1(lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__51;
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__7;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__102;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__66;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__86;
static lean_object* l_Lake_instReprCliError___closed__1;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__24;
static lean_object* l_Lake_CliError_toString___closed__12;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__29;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__75;
static lean_object* l_Lake_CliError_toString___closed__11;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__36;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__35;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__14;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_CliError_toString___closed__26;
static lean_object* l_Lake_CliError_toString___closed__42;
static lean_object* l_Lake_CliError_toString___closed__4;
static lean_object* l_Lake_CliError_toString___closed__28;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__26;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__100;
static lean_object* l_Lake_CliError_toString___closed__40;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__46;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__13;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__67;
static lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__57;
static lean_object* l_Lake_CliError_toString___closed__29;
static lean_object* _init_l_Lake_instInhabitedCliError() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.missingCommand", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_2 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_2 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownCommand", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__10;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.missingArg", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__13;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.missingOptArg", 27, 27);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__16;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.invalidOptArg", 27, 27);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__18;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__19;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownShortOption", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__21;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__22;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownLongOption", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__24;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__25;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unexpectedArguments", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__27;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__28;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unexpectedPlus", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__30;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_2 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__31;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__33() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__32;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_2 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__31;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__35() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__34;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownTemplate", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__36;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__37;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownConfigLang", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__39;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__40;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownModule", 27, 27);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__42;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__43;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownPackage", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__45;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__46;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownFacet", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__48;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__49;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownTarget", 27, 27);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__51;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__52;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.missingModule", 27, 27);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__54;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__55;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__57() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.missingTarget", 27, 27);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__57;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__58;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__60() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.invalidBuildTarget", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__60;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__61;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__63() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.invalidTargetSpec", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__63;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__64;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__66() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.invalidFacet", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__66;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__67;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__69() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownExe", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__69;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__70;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__72() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownScript", 27, 27);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__72;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__73;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__75() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.missingScriptDoc", 30, 30);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__75;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__76;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__78() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.invalidScriptSpec", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__78;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__80() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__79;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__81() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.outputConfigExists", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__82() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__81;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__83() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__82;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__84() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__85() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__84;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__86() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownLeanInstall", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__87() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__86;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__88() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_2 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__87;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__89() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__88;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__90() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_2 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__87;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__91() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__90;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__92() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.unknownLakeInstall", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__93() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__92;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__94() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_2 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__93;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__95() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__94;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__96() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_2 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__93;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__97() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__96;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__98() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.leanRevMismatch", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__99() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__98;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__100() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__99;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__101() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CliError.invalidEnv", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__102() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__101;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__103() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__102;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_unsigned_to_nat(1024u);
x_12 = lean_nat_dec_le(x_11, x_2);
x_13 = l_String_quote(x_10);
lean_dec(x_10);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_13);
x_14 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__11;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
if (x_12 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = 0;
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
x_23 = 0;
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
x_25 = l_Repr_addAppParen(x_24, x_2);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_unsigned_to_nat(1024u);
x_28 = lean_nat_dec_le(x_27, x_2);
x_29 = l_String_quote(x_26);
lean_dec(x_26);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__11;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
if (x_28 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_33 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = 0;
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = l_Repr_addAppParen(x_36, x_2);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_38 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
x_40 = 0;
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = l_Repr_addAppParen(x_41, x_2);
return x_42;
}
}
}
case 2:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_unsigned_to_nat(1024u);
x_46 = lean_nat_dec_le(x_45, x_2);
x_47 = l_String_quote(x_44);
lean_dec(x_44);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_47);
x_48 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__14;
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_1);
if (x_46 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_50 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = 0;
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = l_Repr_addAppParen(x_53, x_2);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_55 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
x_57 = 0;
x_58 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = l_Repr_addAppParen(x_58, x_2);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
lean_dec(x_1);
x_61 = lean_unsigned_to_nat(1024u);
x_62 = lean_nat_dec_le(x_61, x_2);
x_63 = l_String_quote(x_60);
lean_dec(x_60);
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__14;
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
if (x_62 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_67 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = 0;
x_70 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = l_Repr_addAppParen(x_70, x_2);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_72 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_73 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
x_74 = 0;
x_75 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = l_Repr_addAppParen(x_75, x_2);
return x_76;
}
}
}
case 3:
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_1);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_78 = lean_ctor_get(x_1, 0);
x_79 = lean_ctor_get(x_1, 1);
x_80 = lean_unsigned_to_nat(1024u);
x_81 = lean_nat_dec_le(x_80, x_2);
x_82 = l_String_quote(x_78);
lean_dec(x_78);
x_83 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__17;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_83);
lean_ctor_set(x_1, 0, x_84);
x_85 = lean_box(1);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_String_quote(x_79);
lean_dec(x_79);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
if (x_81 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_90 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_91 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = 0;
x_93 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
x_94 = l_Repr_addAppParen(x_93, x_2);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_95 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_96 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_89);
x_97 = 0;
x_98 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = l_Repr_addAppParen(x_98, x_2);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_100 = lean_ctor_get(x_1, 0);
x_101 = lean_ctor_get(x_1, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_1);
x_102 = lean_unsigned_to_nat(1024u);
x_103 = lean_nat_dec_le(x_102, x_2);
x_104 = l_String_quote(x_100);
lean_dec(x_100);
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__17;
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_box(1);
x_109 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_String_quote(x_101);
lean_dec(x_101);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
if (x_103 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_113 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_114 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = 0;
x_116 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = l_Repr_addAppParen(x_116, x_2);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; 
x_118 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_119 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_112);
x_120 = 0;
x_121 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set_uint8(x_121, sizeof(void*)*1, x_120);
x_122 = l_Repr_addAppParen(x_121, x_2);
return x_122;
}
}
}
case 4:
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_1);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_124 = lean_ctor_get(x_1, 0);
x_125 = lean_ctor_get(x_1, 1);
x_126 = lean_unsigned_to_nat(1024u);
x_127 = lean_nat_dec_le(x_126, x_2);
x_128 = l_String_quote(x_124);
lean_dec(x_124);
x_129 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__20;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_129);
lean_ctor_set(x_1, 0, x_130);
x_131 = lean_box(1);
x_132 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_String_quote(x_125);
lean_dec(x_125);
x_134 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
if (x_127 == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_136 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_137 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = 0;
x_139 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_138);
x_140 = l_Repr_addAppParen(x_139, x_2);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; 
x_141 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_142 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_135);
x_143 = 0;
x_144 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*1, x_143);
x_145 = l_Repr_addAppParen(x_144, x_2);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_146 = lean_ctor_get(x_1, 0);
x_147 = lean_ctor_get(x_1, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_1);
x_148 = lean_unsigned_to_nat(1024u);
x_149 = lean_nat_dec_le(x_148, x_2);
x_150 = l_String_quote(x_146);
lean_dec(x_146);
x_151 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__20;
x_153 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = lean_box(1);
x_155 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_String_quote(x_147);
lean_dec(x_147);
x_157 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_158 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
if (x_149 == 0)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; 
x_159 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_160 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = 0;
x_162 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*1, x_161);
x_163 = l_Repr_addAppParen(x_162, x_2);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; 
x_164 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_165 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_158);
x_166 = 0;
x_167 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*1, x_166);
x_168 = l_Repr_addAppParen(x_167, x_2);
return x_168;
}
}
}
case 5:
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_1);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint32_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_170 = lean_ctor_get(x_1, 0);
x_171 = lean_unsigned_to_nat(1024u);
x_172 = lean_nat_dec_le(x_171, x_2);
x_173 = lean_unbox_uint32(x_170);
lean_dec(x_170);
x_174 = l_Char_quote(x_173);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_174);
x_175 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__23;
x_176 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_1);
if (x_172 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; 
x_177 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_178 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_179 = 0;
x_180 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_179);
x_181 = l_Repr_addAppParen(x_180, x_2);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; 
x_182 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_183 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_176);
x_184 = 0;
x_185 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set_uint8(x_185, sizeof(void*)*1, x_184);
x_186 = l_Repr_addAppParen(x_185, x_2);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; uint32_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_187 = lean_ctor_get(x_1, 0);
lean_inc(x_187);
lean_dec(x_1);
x_188 = lean_unsigned_to_nat(1024u);
x_189 = lean_nat_dec_le(x_188, x_2);
x_190 = lean_unbox_uint32(x_187);
lean_dec(x_187);
x_191 = l_Char_quote(x_190);
x_192 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__23;
x_194 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
if (x_189 == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; 
x_195 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_196 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = 0;
x_198 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*1, x_197);
x_199 = l_Repr_addAppParen(x_198, x_2);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; 
x_200 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_201 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_194);
x_202 = 0;
x_203 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_202);
x_204 = l_Repr_addAppParen(x_203, x_2);
return x_204;
}
}
}
case 6:
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_1);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_206 = lean_ctor_get(x_1, 0);
x_207 = lean_unsigned_to_nat(1024u);
x_208 = lean_nat_dec_le(x_207, x_2);
x_209 = l_String_quote(x_206);
lean_dec(x_206);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_209);
x_210 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__26;
x_211 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_1);
if (x_208 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_212 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_213 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = 0;
x_215 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set_uint8(x_215, sizeof(void*)*1, x_214);
x_216 = l_Repr_addAppParen(x_215, x_2);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
x_217 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_218 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_211);
x_219 = 0;
x_220 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set_uint8(x_220, sizeof(void*)*1, x_219);
x_221 = l_Repr_addAppParen(x_220, x_2);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_1, 0);
lean_inc(x_222);
lean_dec(x_1);
x_223 = lean_unsigned_to_nat(1024u);
x_224 = lean_nat_dec_le(x_223, x_2);
x_225 = l_String_quote(x_222);
lean_dec(x_222);
x_226 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__26;
x_228 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
if (x_224 == 0)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; 
x_229 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_230 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = 0;
x_232 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set_uint8(x_232, sizeof(void*)*1, x_231);
x_233 = l_Repr_addAppParen(x_232, x_2);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; 
x_234 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_235 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_228);
x_236 = 0;
x_237 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set_uint8(x_237, sizeof(void*)*1, x_236);
x_238 = l_Repr_addAppParen(x_237, x_2);
return x_238;
}
}
}
case 7:
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_1, 0);
lean_inc(x_239);
lean_dec(x_1);
x_240 = lean_unsigned_to_nat(1024u);
x_241 = lean_nat_dec_le(x_240, x_2);
x_242 = l_List_repr_x27___at___private_Init_Meta_0__Lean_Syntax_reprPreresolved____x40_Init_Meta___hyg_2064____spec__1(x_239, x_240);
x_243 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__29;
x_244 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
if (x_241 == 0)
{
lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_245 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_246 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
x_247 = 0;
x_248 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set_uint8(x_248, sizeof(void*)*1, x_247);
x_249 = l_Repr_addAppParen(x_248, x_2);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; 
x_250 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_251 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_244);
x_252 = 0;
x_253 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set_uint8(x_253, sizeof(void*)*1, x_252);
x_254 = l_Repr_addAppParen(x_253, x_2);
return x_254;
}
}
case 8:
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_unsigned_to_nat(1024u);
x_256 = lean_nat_dec_le(x_255, x_2);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__33;
x_258 = l_Repr_addAppParen(x_257, x_2);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__35;
x_260 = l_Repr_addAppParen(x_259, x_2);
return x_260;
}
}
case 9:
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_1);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_262 = lean_ctor_get(x_1, 0);
x_263 = lean_unsigned_to_nat(1024u);
x_264 = lean_nat_dec_le(x_263, x_2);
x_265 = l_String_quote(x_262);
lean_dec(x_262);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_265);
x_266 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__38;
x_267 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_1);
if (x_264 == 0)
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; 
x_268 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_269 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = 0;
x_271 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set_uint8(x_271, sizeof(void*)*1, x_270);
x_272 = l_Repr_addAppParen(x_271, x_2);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; 
x_273 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_274 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_267);
x_275 = 0;
x_276 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set_uint8(x_276, sizeof(void*)*1, x_275);
x_277 = l_Repr_addAppParen(x_276, x_2);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_278 = lean_ctor_get(x_1, 0);
lean_inc(x_278);
lean_dec(x_1);
x_279 = lean_unsigned_to_nat(1024u);
x_280 = lean_nat_dec_le(x_279, x_2);
x_281 = l_String_quote(x_278);
lean_dec(x_278);
x_282 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_282, 0, x_281);
x_283 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__38;
x_284 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_282);
if (x_280 == 0)
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; 
x_285 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_286 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_284);
x_287 = 0;
x_288 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set_uint8(x_288, sizeof(void*)*1, x_287);
x_289 = l_Repr_addAppParen(x_288, x_2);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; 
x_290 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_291 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_284);
x_292 = 0;
x_293 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*1, x_292);
x_294 = l_Repr_addAppParen(x_293, x_2);
return x_294;
}
}
}
case 10:
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_1);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_296 = lean_ctor_get(x_1, 0);
x_297 = lean_unsigned_to_nat(1024u);
x_298 = lean_nat_dec_le(x_297, x_2);
x_299 = l_String_quote(x_296);
lean_dec(x_296);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_299);
x_300 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__41;
x_301 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_1);
if (x_298 == 0)
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; lean_object* x_306; 
x_302 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_303 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_301);
x_304 = 0;
x_305 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set_uint8(x_305, sizeof(void*)*1, x_304);
x_306 = l_Repr_addAppParen(x_305, x_2);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; 
x_307 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_308 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_301);
x_309 = 0;
x_310 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set_uint8(x_310, sizeof(void*)*1, x_309);
x_311 = l_Repr_addAppParen(x_310, x_2);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_312 = lean_ctor_get(x_1, 0);
lean_inc(x_312);
lean_dec(x_1);
x_313 = lean_unsigned_to_nat(1024u);
x_314 = lean_nat_dec_le(x_313, x_2);
x_315 = l_String_quote(x_312);
lean_dec(x_312);
x_316 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__41;
x_318 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_316);
if (x_314 == 0)
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; 
x_319 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_320 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
x_321 = 0;
x_322 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set_uint8(x_322, sizeof(void*)*1, x_321);
x_323 = l_Repr_addAppParen(x_322, x_2);
return x_323;
}
else
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; 
x_324 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_325 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_318);
x_326 = 0;
x_327 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set_uint8(x_327, sizeof(void*)*1, x_326);
x_328 = l_Repr_addAppParen(x_327, x_2);
return x_328;
}
}
}
case 11:
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_329 = lean_ctor_get(x_1, 0);
lean_inc(x_329);
lean_dec(x_1);
x_330 = lean_unsigned_to_nat(1024u);
x_331 = lean_nat_dec_le(x_330, x_2);
x_332 = l_Lean_Name_reprPrec(x_329, x_330);
x_333 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__44;
x_334 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_332);
if (x_331 == 0)
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; 
x_335 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_336 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_334);
x_337 = 0;
x_338 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*1, x_337);
x_339 = l_Repr_addAppParen(x_338, x_2);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; 
x_340 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_341 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_334);
x_342 = 0;
x_343 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set_uint8(x_343, sizeof(void*)*1, x_342);
x_344 = l_Repr_addAppParen(x_343, x_2);
return x_344;
}
}
case 12:
{
uint8_t x_345; 
x_345 = !lean_is_exclusive(x_1);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_346 = lean_ctor_get(x_1, 0);
x_347 = lean_unsigned_to_nat(1024u);
x_348 = lean_nat_dec_le(x_347, x_2);
x_349 = l_String_quote(x_346);
lean_dec(x_346);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_349);
x_350 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__47;
x_351 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_1);
if (x_348 == 0)
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; lean_object* x_356; 
x_352 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_353 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
x_354 = 0;
x_355 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set_uint8(x_355, sizeof(void*)*1, x_354);
x_356 = l_Repr_addAppParen(x_355, x_2);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; 
x_357 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_358 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_351);
x_359 = 0;
x_360 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set_uint8(x_360, sizeof(void*)*1, x_359);
x_361 = l_Repr_addAppParen(x_360, x_2);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_362 = lean_ctor_get(x_1, 0);
lean_inc(x_362);
lean_dec(x_1);
x_363 = lean_unsigned_to_nat(1024u);
x_364 = lean_nat_dec_le(x_363, x_2);
x_365 = l_String_quote(x_362);
lean_dec(x_362);
x_366 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_366, 0, x_365);
x_367 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__47;
x_368 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
if (x_364 == 0)
{
lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; lean_object* x_373; 
x_369 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_370 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_368);
x_371 = 0;
x_372 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set_uint8(x_372, sizeof(void*)*1, x_371);
x_373 = l_Repr_addAppParen(x_372, x_2);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; lean_object* x_377; lean_object* x_378; 
x_374 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_375 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_368);
x_376 = 0;
x_377 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set_uint8(x_377, sizeof(void*)*1, x_376);
x_378 = l_Repr_addAppParen(x_377, x_2);
return x_378;
}
}
}
case 13:
{
uint8_t x_379; 
x_379 = !lean_is_exclusive(x_1);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_380 = lean_ctor_get(x_1, 0);
x_381 = lean_ctor_get(x_1, 1);
x_382 = lean_unsigned_to_nat(1024u);
x_383 = lean_nat_dec_le(x_382, x_2);
x_384 = l_String_quote(x_380);
lean_dec(x_380);
x_385 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_385, 0, x_384);
x_386 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__50;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_385);
lean_ctor_set(x_1, 0, x_386);
x_387 = lean_box(1);
x_388 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_388, 0, x_1);
lean_ctor_set(x_388, 1, x_387);
x_389 = l_Lean_Name_reprPrec(x_381, x_382);
x_390 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
if (x_383 == 0)
{
lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; lean_object* x_395; 
x_391 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_392 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_390);
x_393 = 0;
x_394 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*1, x_393);
x_395 = l_Repr_addAppParen(x_394, x_2);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; lean_object* x_400; 
x_396 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_397 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_390);
x_398 = 0;
x_399 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set_uint8(x_399, sizeof(void*)*1, x_398);
x_400 = l_Repr_addAppParen(x_399, x_2);
return x_400;
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_401 = lean_ctor_get(x_1, 0);
x_402 = lean_ctor_get(x_1, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_1);
x_403 = lean_unsigned_to_nat(1024u);
x_404 = lean_nat_dec_le(x_403, x_2);
x_405 = l_String_quote(x_401);
lean_dec(x_401);
x_406 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_406, 0, x_405);
x_407 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__50;
x_408 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_406);
x_409 = lean_box(1);
x_410 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
x_411 = l_Lean_Name_reprPrec(x_402, x_403);
x_412 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
if (x_404 == 0)
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; lean_object* x_417; 
x_413 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_414 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_412);
x_415 = 0;
x_416 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*1, x_415);
x_417 = l_Repr_addAppParen(x_416, x_2);
return x_417;
}
else
{
lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; lean_object* x_422; 
x_418 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_419 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_412);
x_420 = 0;
x_421 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set_uint8(x_421, sizeof(void*)*1, x_420);
x_422 = l_Repr_addAppParen(x_421, x_2);
return x_422;
}
}
}
case 14:
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_423 = lean_ctor_get(x_1, 0);
lean_inc(x_423);
lean_dec(x_1);
x_424 = lean_unsigned_to_nat(1024u);
x_425 = lean_nat_dec_le(x_424, x_2);
x_426 = l_Lean_Name_reprPrec(x_423, x_424);
x_427 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__53;
x_428 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_426);
if (x_425 == 0)
{
lean_object* x_429; lean_object* x_430; uint8_t x_431; lean_object* x_432; lean_object* x_433; 
x_429 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_430 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
x_431 = 0;
x_432 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*1, x_431);
x_433 = l_Repr_addAppParen(x_432, x_2);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; lean_object* x_438; 
x_434 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_435 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_428);
x_436 = 0;
x_437 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set_uint8(x_437, sizeof(void*)*1, x_436);
x_438 = l_Repr_addAppParen(x_437, x_2);
return x_438;
}
}
case 15:
{
uint8_t x_439; 
x_439 = !lean_is_exclusive(x_1);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_440 = lean_ctor_get(x_1, 0);
x_441 = lean_ctor_get(x_1, 1);
x_442 = lean_unsigned_to_nat(1024u);
x_443 = lean_nat_dec_le(x_442, x_2);
x_444 = l_Lean_Name_reprPrec(x_440, x_442);
x_445 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__56;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_444);
lean_ctor_set(x_1, 0, x_445);
x_446 = lean_box(1);
x_447 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_447, 0, x_1);
lean_ctor_set(x_447, 1, x_446);
x_448 = l_Lean_Name_reprPrec(x_441, x_442);
x_449 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
if (x_443 == 0)
{
lean_object* x_450; lean_object* x_451; uint8_t x_452; lean_object* x_453; lean_object* x_454; 
x_450 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_451 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_449);
x_452 = 0;
x_453 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set_uint8(x_453, sizeof(void*)*1, x_452);
x_454 = l_Repr_addAppParen(x_453, x_2);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; lean_object* x_459; 
x_455 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_456 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_449);
x_457 = 0;
x_458 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*1, x_457);
x_459 = l_Repr_addAppParen(x_458, x_2);
return x_459;
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_460 = lean_ctor_get(x_1, 0);
x_461 = lean_ctor_get(x_1, 1);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_1);
x_462 = lean_unsigned_to_nat(1024u);
x_463 = lean_nat_dec_le(x_462, x_2);
x_464 = l_Lean_Name_reprPrec(x_460, x_462);
x_465 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__56;
x_466 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_464);
x_467 = lean_box(1);
x_468 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
x_469 = l_Lean_Name_reprPrec(x_461, x_462);
x_470 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
if (x_463 == 0)
{
lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; lean_object* x_475; 
x_471 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_472 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_470);
x_473 = 0;
x_474 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set_uint8(x_474, sizeof(void*)*1, x_473);
x_475 = l_Repr_addAppParen(x_474, x_2);
return x_475;
}
else
{
lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; 
x_476 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_477 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_470);
x_478 = 0;
x_479 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set_uint8(x_479, sizeof(void*)*1, x_478);
x_480 = l_Repr_addAppParen(x_479, x_2);
return x_480;
}
}
}
case 16:
{
uint8_t x_481; 
x_481 = !lean_is_exclusive(x_1);
if (x_481 == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_482 = lean_ctor_get(x_1, 0);
x_483 = lean_ctor_get(x_1, 1);
x_484 = lean_unsigned_to_nat(1024u);
x_485 = lean_nat_dec_le(x_484, x_2);
x_486 = l_Lean_Name_reprPrec(x_482, x_484);
x_487 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__59;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_486);
lean_ctor_set(x_1, 0, x_487);
x_488 = lean_box(1);
x_489 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_489, 0, x_1);
lean_ctor_set(x_489, 1, x_488);
x_490 = l_String_quote(x_483);
lean_dec(x_483);
x_491 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_491, 0, x_490);
x_492 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_491);
if (x_485 == 0)
{
lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; lean_object* x_497; 
x_493 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_494 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_492);
x_495 = 0;
x_496 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*1, x_495);
x_497 = l_Repr_addAppParen(x_496, x_2);
return x_497;
}
else
{
lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; 
x_498 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_499 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_492);
x_500 = 0;
x_501 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set_uint8(x_501, sizeof(void*)*1, x_500);
x_502 = l_Repr_addAppParen(x_501, x_2);
return x_502;
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_503 = lean_ctor_get(x_1, 0);
x_504 = lean_ctor_get(x_1, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_1);
x_505 = lean_unsigned_to_nat(1024u);
x_506 = lean_nat_dec_le(x_505, x_2);
x_507 = l_Lean_Name_reprPrec(x_503, x_505);
x_508 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__59;
x_509 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_507);
x_510 = lean_box(1);
x_511 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
x_512 = l_String_quote(x_504);
lean_dec(x_504);
x_513 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_513, 0, x_512);
x_514 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_513);
if (x_506 == 0)
{
lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; lean_object* x_519; 
x_515 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_516 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_514);
x_517 = 0;
x_518 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set_uint8(x_518, sizeof(void*)*1, x_517);
x_519 = l_Repr_addAppParen(x_518, x_2);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; 
x_520 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_521 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_514);
x_522 = 0;
x_523 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set_uint8(x_523, sizeof(void*)*1, x_522);
x_524 = l_Repr_addAppParen(x_523, x_2);
return x_524;
}
}
}
case 17:
{
uint8_t x_525; 
x_525 = !lean_is_exclusive(x_1);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; uint8_t x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_526 = lean_ctor_get(x_1, 0);
x_527 = lean_unsigned_to_nat(1024u);
x_528 = lean_nat_dec_le(x_527, x_2);
x_529 = l_String_quote(x_526);
lean_dec(x_526);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_529);
x_530 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__62;
x_531 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_1);
if (x_528 == 0)
{
lean_object* x_532; lean_object* x_533; uint8_t x_534; lean_object* x_535; lean_object* x_536; 
x_532 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_533 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_531);
x_534 = 0;
x_535 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_535, 0, x_533);
lean_ctor_set_uint8(x_535, sizeof(void*)*1, x_534);
x_536 = l_Repr_addAppParen(x_535, x_2);
return x_536;
}
else
{
lean_object* x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; lean_object* x_541; 
x_537 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_538 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_531);
x_539 = 0;
x_540 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*1, x_539);
x_541 = l_Repr_addAppParen(x_540, x_2);
return x_541;
}
}
else
{
lean_object* x_542; lean_object* x_543; uint8_t x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_542 = lean_ctor_get(x_1, 0);
lean_inc(x_542);
lean_dec(x_1);
x_543 = lean_unsigned_to_nat(1024u);
x_544 = lean_nat_dec_le(x_543, x_2);
x_545 = l_String_quote(x_542);
lean_dec(x_542);
x_546 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_546, 0, x_545);
x_547 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__62;
x_548 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_546);
if (x_544 == 0)
{
lean_object* x_549; lean_object* x_550; uint8_t x_551; lean_object* x_552; lean_object* x_553; 
x_549 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_550 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_548);
x_551 = 0;
x_552 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set_uint8(x_552, sizeof(void*)*1, x_551);
x_553 = l_Repr_addAppParen(x_552, x_2);
return x_553;
}
else
{
lean_object* x_554; lean_object* x_555; uint8_t x_556; lean_object* x_557; lean_object* x_558; 
x_554 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_555 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_548);
x_556 = 0;
x_557 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set_uint8(x_557, sizeof(void*)*1, x_556);
x_558 = l_Repr_addAppParen(x_557, x_2);
return x_558;
}
}
}
case 18:
{
uint8_t x_559; 
x_559 = !lean_is_exclusive(x_1);
if (x_559 == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; uint32_t x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_560 = lean_ctor_get(x_1, 0);
x_561 = lean_ctor_get(x_1, 1);
x_562 = lean_unsigned_to_nat(1024u);
x_563 = lean_nat_dec_le(x_562, x_2);
x_564 = l_String_quote(x_560);
lean_dec(x_560);
x_565 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_565, 0, x_564);
x_566 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__65;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_565);
lean_ctor_set(x_1, 0, x_566);
x_567 = lean_box(1);
x_568 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_568, 0, x_1);
lean_ctor_set(x_568, 1, x_567);
x_569 = lean_unbox_uint32(x_561);
lean_dec(x_561);
x_570 = l_Char_quote(x_569);
x_571 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_571, 0, x_570);
x_572 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_572, 0, x_568);
lean_ctor_set(x_572, 1, x_571);
if (x_563 == 0)
{
lean_object* x_573; lean_object* x_574; uint8_t x_575; lean_object* x_576; lean_object* x_577; 
x_573 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_574 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_572);
x_575 = 0;
x_576 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_576, 0, x_574);
lean_ctor_set_uint8(x_576, sizeof(void*)*1, x_575);
x_577 = l_Repr_addAppParen(x_576, x_2);
return x_577;
}
else
{
lean_object* x_578; lean_object* x_579; uint8_t x_580; lean_object* x_581; lean_object* x_582; 
x_578 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_579 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_572);
x_580 = 0;
x_581 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set_uint8(x_581, sizeof(void*)*1, x_580);
x_582 = l_Repr_addAppParen(x_581, x_2);
return x_582;
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint32_t x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_583 = lean_ctor_get(x_1, 0);
x_584 = lean_ctor_get(x_1, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_1);
x_585 = lean_unsigned_to_nat(1024u);
x_586 = lean_nat_dec_le(x_585, x_2);
x_587 = l_String_quote(x_583);
lean_dec(x_583);
x_588 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_588, 0, x_587);
x_589 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__65;
x_590 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_588);
x_591 = lean_box(1);
x_592 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
x_593 = lean_unbox_uint32(x_584);
lean_dec(x_584);
x_594 = l_Char_quote(x_593);
x_595 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_595, 0, x_594);
x_596 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_596, 0, x_592);
lean_ctor_set(x_596, 1, x_595);
if (x_586 == 0)
{
lean_object* x_597; lean_object* x_598; uint8_t x_599; lean_object* x_600; lean_object* x_601; 
x_597 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_598 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_596);
x_599 = 0;
x_600 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set_uint8(x_600, sizeof(void*)*1, x_599);
x_601 = l_Repr_addAppParen(x_600, x_2);
return x_601;
}
else
{
lean_object* x_602; lean_object* x_603; uint8_t x_604; lean_object* x_605; lean_object* x_606; 
x_602 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_603 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_603, 0, x_602);
lean_ctor_set(x_603, 1, x_596);
x_604 = 0;
x_605 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set_uint8(x_605, sizeof(void*)*1, x_604);
x_606 = l_Repr_addAppParen(x_605, x_2);
return x_606;
}
}
}
case 19:
{
uint8_t x_607; 
x_607 = !lean_is_exclusive(x_1);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_608 = lean_ctor_get(x_1, 0);
x_609 = lean_ctor_get(x_1, 1);
x_610 = lean_unsigned_to_nat(1024u);
x_611 = lean_nat_dec_le(x_610, x_2);
x_612 = l_Lean_Name_reprPrec(x_608, x_610);
x_613 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__68;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_612);
lean_ctor_set(x_1, 0, x_613);
x_614 = lean_box(1);
x_615 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_615, 0, x_1);
lean_ctor_set(x_615, 1, x_614);
x_616 = l_Lean_Name_reprPrec(x_609, x_610);
x_617 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set(x_617, 1, x_616);
if (x_611 == 0)
{
lean_object* x_618; lean_object* x_619; uint8_t x_620; lean_object* x_621; lean_object* x_622; 
x_618 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_619 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_617);
x_620 = 0;
x_621 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set_uint8(x_621, sizeof(void*)*1, x_620);
x_622 = l_Repr_addAppParen(x_621, x_2);
return x_622;
}
else
{
lean_object* x_623; lean_object* x_624; uint8_t x_625; lean_object* x_626; lean_object* x_627; 
x_623 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_624 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_617);
x_625 = 0;
x_626 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_626, 0, x_624);
lean_ctor_set_uint8(x_626, sizeof(void*)*1, x_625);
x_627 = l_Repr_addAppParen(x_626, x_2);
return x_627;
}
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_628 = lean_ctor_get(x_1, 0);
x_629 = lean_ctor_get(x_1, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_1);
x_630 = lean_unsigned_to_nat(1024u);
x_631 = lean_nat_dec_le(x_630, x_2);
x_632 = l_Lean_Name_reprPrec(x_628, x_630);
x_633 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__68;
x_634 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_632);
x_635 = lean_box(1);
x_636 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
x_637 = l_Lean_Name_reprPrec(x_629, x_630);
x_638 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
if (x_631 == 0)
{
lean_object* x_639; lean_object* x_640; uint8_t x_641; lean_object* x_642; lean_object* x_643; 
x_639 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_640 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_640, 1, x_638);
x_641 = 0;
x_642 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set_uint8(x_642, sizeof(void*)*1, x_641);
x_643 = l_Repr_addAppParen(x_642, x_2);
return x_643;
}
else
{
lean_object* x_644; lean_object* x_645; uint8_t x_646; lean_object* x_647; lean_object* x_648; 
x_644 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_645 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_638);
x_646 = 0;
x_647 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_647, 0, x_645);
lean_ctor_set_uint8(x_647, sizeof(void*)*1, x_646);
x_648 = l_Repr_addAppParen(x_647, x_2);
return x_648;
}
}
}
case 20:
{
uint8_t x_649; 
x_649 = !lean_is_exclusive(x_1);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; uint8_t x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_650 = lean_ctor_get(x_1, 0);
x_651 = lean_unsigned_to_nat(1024u);
x_652 = lean_nat_dec_le(x_651, x_2);
x_653 = l_String_quote(x_650);
lean_dec(x_650);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_653);
x_654 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__71;
x_655 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_1);
if (x_652 == 0)
{
lean_object* x_656; lean_object* x_657; uint8_t x_658; lean_object* x_659; lean_object* x_660; 
x_656 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_657 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_655);
x_658 = 0;
x_659 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_659, 0, x_657);
lean_ctor_set_uint8(x_659, sizeof(void*)*1, x_658);
x_660 = l_Repr_addAppParen(x_659, x_2);
return x_660;
}
else
{
lean_object* x_661; lean_object* x_662; uint8_t x_663; lean_object* x_664; lean_object* x_665; 
x_661 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_662 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_662, 0, x_661);
lean_ctor_set(x_662, 1, x_655);
x_663 = 0;
x_664 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_664, 0, x_662);
lean_ctor_set_uint8(x_664, sizeof(void*)*1, x_663);
x_665 = l_Repr_addAppParen(x_664, x_2);
return x_665;
}
}
else
{
lean_object* x_666; lean_object* x_667; uint8_t x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_666 = lean_ctor_get(x_1, 0);
lean_inc(x_666);
lean_dec(x_1);
x_667 = lean_unsigned_to_nat(1024u);
x_668 = lean_nat_dec_le(x_667, x_2);
x_669 = l_String_quote(x_666);
lean_dec(x_666);
x_670 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_670, 0, x_669);
x_671 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__71;
x_672 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_670);
if (x_668 == 0)
{
lean_object* x_673; lean_object* x_674; uint8_t x_675; lean_object* x_676; lean_object* x_677; 
x_673 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_674 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_674, 0, x_673);
lean_ctor_set(x_674, 1, x_672);
x_675 = 0;
x_676 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_676, 0, x_674);
lean_ctor_set_uint8(x_676, sizeof(void*)*1, x_675);
x_677 = l_Repr_addAppParen(x_676, x_2);
return x_677;
}
else
{
lean_object* x_678; lean_object* x_679; uint8_t x_680; lean_object* x_681; lean_object* x_682; 
x_678 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_679 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_679, 0, x_678);
lean_ctor_set(x_679, 1, x_672);
x_680 = 0;
x_681 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_681, 0, x_679);
lean_ctor_set_uint8(x_681, sizeof(void*)*1, x_680);
x_682 = l_Repr_addAppParen(x_681, x_2);
return x_682;
}
}
}
case 21:
{
uint8_t x_683; 
x_683 = !lean_is_exclusive(x_1);
if (x_683 == 0)
{
lean_object* x_684; lean_object* x_685; uint8_t x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_684 = lean_ctor_get(x_1, 0);
x_685 = lean_unsigned_to_nat(1024u);
x_686 = lean_nat_dec_le(x_685, x_2);
x_687 = l_String_quote(x_684);
lean_dec(x_684);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_687);
x_688 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__74;
x_689 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_1);
if (x_686 == 0)
{
lean_object* x_690; lean_object* x_691; uint8_t x_692; lean_object* x_693; lean_object* x_694; 
x_690 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_691 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_689);
x_692 = 0;
x_693 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_693, 0, x_691);
lean_ctor_set_uint8(x_693, sizeof(void*)*1, x_692);
x_694 = l_Repr_addAppParen(x_693, x_2);
return x_694;
}
else
{
lean_object* x_695; lean_object* x_696; uint8_t x_697; lean_object* x_698; lean_object* x_699; 
x_695 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_696 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_696, 0, x_695);
lean_ctor_set(x_696, 1, x_689);
x_697 = 0;
x_698 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set_uint8(x_698, sizeof(void*)*1, x_697);
x_699 = l_Repr_addAppParen(x_698, x_2);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; uint8_t x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_700 = lean_ctor_get(x_1, 0);
lean_inc(x_700);
lean_dec(x_1);
x_701 = lean_unsigned_to_nat(1024u);
x_702 = lean_nat_dec_le(x_701, x_2);
x_703 = l_String_quote(x_700);
lean_dec(x_700);
x_704 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_704, 0, x_703);
x_705 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__74;
x_706 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_704);
if (x_702 == 0)
{
lean_object* x_707; lean_object* x_708; uint8_t x_709; lean_object* x_710; lean_object* x_711; 
x_707 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_708 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_706);
x_709 = 0;
x_710 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_710, 0, x_708);
lean_ctor_set_uint8(x_710, sizeof(void*)*1, x_709);
x_711 = l_Repr_addAppParen(x_710, x_2);
return x_711;
}
else
{
lean_object* x_712; lean_object* x_713; uint8_t x_714; lean_object* x_715; lean_object* x_716; 
x_712 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_713 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_706);
x_714 = 0;
x_715 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set_uint8(x_715, sizeof(void*)*1, x_714);
x_716 = l_Repr_addAppParen(x_715, x_2);
return x_716;
}
}
}
case 22:
{
uint8_t x_717; 
x_717 = !lean_is_exclusive(x_1);
if (x_717 == 0)
{
lean_object* x_718; lean_object* x_719; uint8_t x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_718 = lean_ctor_get(x_1, 0);
x_719 = lean_unsigned_to_nat(1024u);
x_720 = lean_nat_dec_le(x_719, x_2);
x_721 = l_String_quote(x_718);
lean_dec(x_718);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_721);
x_722 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__77;
x_723 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_1);
if (x_720 == 0)
{
lean_object* x_724; lean_object* x_725; uint8_t x_726; lean_object* x_727; lean_object* x_728; 
x_724 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_725 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_725, 0, x_724);
lean_ctor_set(x_725, 1, x_723);
x_726 = 0;
x_727 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_727, 0, x_725);
lean_ctor_set_uint8(x_727, sizeof(void*)*1, x_726);
x_728 = l_Repr_addAppParen(x_727, x_2);
return x_728;
}
else
{
lean_object* x_729; lean_object* x_730; uint8_t x_731; lean_object* x_732; lean_object* x_733; 
x_729 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_730 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_730, 0, x_729);
lean_ctor_set(x_730, 1, x_723);
x_731 = 0;
x_732 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set_uint8(x_732, sizeof(void*)*1, x_731);
x_733 = l_Repr_addAppParen(x_732, x_2);
return x_733;
}
}
else
{
lean_object* x_734; lean_object* x_735; uint8_t x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_734 = lean_ctor_get(x_1, 0);
lean_inc(x_734);
lean_dec(x_1);
x_735 = lean_unsigned_to_nat(1024u);
x_736 = lean_nat_dec_le(x_735, x_2);
x_737 = l_String_quote(x_734);
lean_dec(x_734);
x_738 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_738, 0, x_737);
x_739 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__77;
x_740 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_740, 0, x_739);
lean_ctor_set(x_740, 1, x_738);
if (x_736 == 0)
{
lean_object* x_741; lean_object* x_742; uint8_t x_743; lean_object* x_744; lean_object* x_745; 
x_741 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_742 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_740);
x_743 = 0;
x_744 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_744, 0, x_742);
lean_ctor_set_uint8(x_744, sizeof(void*)*1, x_743);
x_745 = l_Repr_addAppParen(x_744, x_2);
return x_745;
}
else
{
lean_object* x_746; lean_object* x_747; uint8_t x_748; lean_object* x_749; lean_object* x_750; 
x_746 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_747 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_747, 0, x_746);
lean_ctor_set(x_747, 1, x_740);
x_748 = 0;
x_749 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_749, 0, x_747);
lean_ctor_set_uint8(x_749, sizeof(void*)*1, x_748);
x_750 = l_Repr_addAppParen(x_749, x_2);
return x_750;
}
}
}
case 23:
{
uint8_t x_751; 
x_751 = !lean_is_exclusive(x_1);
if (x_751 == 0)
{
lean_object* x_752; lean_object* x_753; uint8_t x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_752 = lean_ctor_get(x_1, 0);
x_753 = lean_unsigned_to_nat(1024u);
x_754 = lean_nat_dec_le(x_753, x_2);
x_755 = l_String_quote(x_752);
lean_dec(x_752);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_755);
x_756 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__80;
x_757 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_757, 1, x_1);
if (x_754 == 0)
{
lean_object* x_758; lean_object* x_759; uint8_t x_760; lean_object* x_761; lean_object* x_762; 
x_758 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_759 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_757);
x_760 = 0;
x_761 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set_uint8(x_761, sizeof(void*)*1, x_760);
x_762 = l_Repr_addAppParen(x_761, x_2);
return x_762;
}
else
{
lean_object* x_763; lean_object* x_764; uint8_t x_765; lean_object* x_766; lean_object* x_767; 
x_763 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_764 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_764, 0, x_763);
lean_ctor_set(x_764, 1, x_757);
x_765 = 0;
x_766 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_766, 0, x_764);
lean_ctor_set_uint8(x_766, sizeof(void*)*1, x_765);
x_767 = l_Repr_addAppParen(x_766, x_2);
return x_767;
}
}
else
{
lean_object* x_768; lean_object* x_769; uint8_t x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_768 = lean_ctor_get(x_1, 0);
lean_inc(x_768);
lean_dec(x_1);
x_769 = lean_unsigned_to_nat(1024u);
x_770 = lean_nat_dec_le(x_769, x_2);
x_771 = l_String_quote(x_768);
lean_dec(x_768);
x_772 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_772, 0, x_771);
x_773 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__80;
x_774 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_772);
if (x_770 == 0)
{
lean_object* x_775; lean_object* x_776; uint8_t x_777; lean_object* x_778; lean_object* x_779; 
x_775 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_776 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_774);
x_777 = 0;
x_778 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_778, 0, x_776);
lean_ctor_set_uint8(x_778, sizeof(void*)*1, x_777);
x_779 = l_Repr_addAppParen(x_778, x_2);
return x_779;
}
else
{
lean_object* x_780; lean_object* x_781; uint8_t x_782; lean_object* x_783; lean_object* x_784; 
x_780 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_781 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_781, 0, x_780);
lean_ctor_set(x_781, 1, x_774);
x_782 = 0;
x_783 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_783, 0, x_781);
lean_ctor_set_uint8(x_783, sizeof(void*)*1, x_782);
x_784 = l_Repr_addAppParen(x_783, x_2);
return x_784;
}
}
}
case 24:
{
uint8_t x_785; 
x_785 = !lean_is_exclusive(x_1);
if (x_785 == 0)
{
lean_object* x_786; lean_object* x_787; uint8_t x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_786 = lean_ctor_get(x_1, 0);
x_787 = lean_unsigned_to_nat(1024u);
x_788 = lean_nat_dec_le(x_787, x_2);
x_789 = l_String_quote(x_786);
lean_dec(x_786);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_789);
x_790 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__85;
x_791 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_791, 0, x_790);
lean_ctor_set(x_791, 1, x_1);
x_792 = l_Repr_addAppParen(x_791, x_787);
x_793 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__83;
x_794 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_794, 0, x_793);
lean_ctor_set(x_794, 1, x_792);
if (x_788 == 0)
{
lean_object* x_795; lean_object* x_796; uint8_t x_797; lean_object* x_798; lean_object* x_799; 
x_795 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_796 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_796, 0, x_795);
lean_ctor_set(x_796, 1, x_794);
x_797 = 0;
x_798 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_798, 0, x_796);
lean_ctor_set_uint8(x_798, sizeof(void*)*1, x_797);
x_799 = l_Repr_addAppParen(x_798, x_2);
return x_799;
}
else
{
lean_object* x_800; lean_object* x_801; uint8_t x_802; lean_object* x_803; lean_object* x_804; 
x_800 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_801 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_801, 0, x_800);
lean_ctor_set(x_801, 1, x_794);
x_802 = 0;
x_803 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_803, 0, x_801);
lean_ctor_set_uint8(x_803, sizeof(void*)*1, x_802);
x_804 = l_Repr_addAppParen(x_803, x_2);
return x_804;
}
}
else
{
lean_object* x_805; lean_object* x_806; uint8_t x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_805 = lean_ctor_get(x_1, 0);
lean_inc(x_805);
lean_dec(x_1);
x_806 = lean_unsigned_to_nat(1024u);
x_807 = lean_nat_dec_le(x_806, x_2);
x_808 = l_String_quote(x_805);
lean_dec(x_805);
x_809 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_809, 0, x_808);
x_810 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__85;
x_811 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_811, 0, x_810);
lean_ctor_set(x_811, 1, x_809);
x_812 = l_Repr_addAppParen(x_811, x_806);
x_813 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__83;
x_814 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_814, 1, x_812);
if (x_807 == 0)
{
lean_object* x_815; lean_object* x_816; uint8_t x_817; lean_object* x_818; lean_object* x_819; 
x_815 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_816 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_816, 0, x_815);
lean_ctor_set(x_816, 1, x_814);
x_817 = 0;
x_818 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_818, 0, x_816);
lean_ctor_set_uint8(x_818, sizeof(void*)*1, x_817);
x_819 = l_Repr_addAppParen(x_818, x_2);
return x_819;
}
else
{
lean_object* x_820; lean_object* x_821; uint8_t x_822; lean_object* x_823; lean_object* x_824; 
x_820 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_821 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_821, 0, x_820);
lean_ctor_set(x_821, 1, x_814);
x_822 = 0;
x_823 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set_uint8(x_823, sizeof(void*)*1, x_822);
x_824 = l_Repr_addAppParen(x_823, x_2);
return x_824;
}
}
}
case 25:
{
lean_object* x_825; uint8_t x_826; 
x_825 = lean_unsigned_to_nat(1024u);
x_826 = lean_nat_dec_le(x_825, x_2);
if (x_826 == 0)
{
lean_object* x_827; lean_object* x_828; 
x_827 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__89;
x_828 = l_Repr_addAppParen(x_827, x_2);
return x_828;
}
else
{
lean_object* x_829; lean_object* x_830; 
x_829 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__91;
x_830 = l_Repr_addAppParen(x_829, x_2);
return x_830;
}
}
case 26:
{
lean_object* x_831; uint8_t x_832; 
x_831 = lean_unsigned_to_nat(1024u);
x_832 = lean_nat_dec_le(x_831, x_2);
if (x_832 == 0)
{
lean_object* x_833; lean_object* x_834; 
x_833 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__95;
x_834 = l_Repr_addAppParen(x_833, x_2);
return x_834;
}
else
{
lean_object* x_835; lean_object* x_836; 
x_835 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__97;
x_836 = l_Repr_addAppParen(x_835, x_2);
return x_836;
}
}
case 27:
{
uint8_t x_837; 
x_837 = !lean_is_exclusive(x_1);
if (x_837 == 0)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; uint8_t x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_838 = lean_ctor_get(x_1, 0);
x_839 = lean_ctor_get(x_1, 1);
x_840 = lean_unsigned_to_nat(1024u);
x_841 = lean_nat_dec_le(x_840, x_2);
x_842 = l_String_quote(x_838);
lean_dec(x_838);
x_843 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_843, 0, x_842);
x_844 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__100;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_843);
lean_ctor_set(x_1, 0, x_844);
x_845 = lean_box(1);
x_846 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_846, 0, x_1);
lean_ctor_set(x_846, 1, x_845);
x_847 = l_String_quote(x_839);
lean_dec(x_839);
x_848 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_848, 0, x_847);
x_849 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_849, 0, x_846);
lean_ctor_set(x_849, 1, x_848);
if (x_841 == 0)
{
lean_object* x_850; lean_object* x_851; uint8_t x_852; lean_object* x_853; lean_object* x_854; 
x_850 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_851 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_851, 0, x_850);
lean_ctor_set(x_851, 1, x_849);
x_852 = 0;
x_853 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_853, 0, x_851);
lean_ctor_set_uint8(x_853, sizeof(void*)*1, x_852);
x_854 = l_Repr_addAppParen(x_853, x_2);
return x_854;
}
else
{
lean_object* x_855; lean_object* x_856; uint8_t x_857; lean_object* x_858; lean_object* x_859; 
x_855 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_856 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_849);
x_857 = 0;
x_858 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_858, 0, x_856);
lean_ctor_set_uint8(x_858, sizeof(void*)*1, x_857);
x_859 = l_Repr_addAppParen(x_858, x_2);
return x_859;
}
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; uint8_t x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_860 = lean_ctor_get(x_1, 0);
x_861 = lean_ctor_get(x_1, 1);
lean_inc(x_861);
lean_inc(x_860);
lean_dec(x_1);
x_862 = lean_unsigned_to_nat(1024u);
x_863 = lean_nat_dec_le(x_862, x_2);
x_864 = l_String_quote(x_860);
lean_dec(x_860);
x_865 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_865, 0, x_864);
x_866 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__100;
x_867 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_867, 0, x_866);
lean_ctor_set(x_867, 1, x_865);
x_868 = lean_box(1);
x_869 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_869, 0, x_867);
lean_ctor_set(x_869, 1, x_868);
x_870 = l_String_quote(x_861);
lean_dec(x_861);
x_871 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_871, 0, x_870);
x_872 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_872, 0, x_869);
lean_ctor_set(x_872, 1, x_871);
if (x_863 == 0)
{
lean_object* x_873; lean_object* x_874; uint8_t x_875; lean_object* x_876; lean_object* x_877; 
x_873 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_874 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_874, 0, x_873);
lean_ctor_set(x_874, 1, x_872);
x_875 = 0;
x_876 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_876, 0, x_874);
lean_ctor_set_uint8(x_876, sizeof(void*)*1, x_875);
x_877 = l_Repr_addAppParen(x_876, x_2);
return x_877;
}
else
{
lean_object* x_878; lean_object* x_879; uint8_t x_880; lean_object* x_881; lean_object* x_882; 
x_878 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_879 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_879, 0, x_878);
lean_ctor_set(x_879, 1, x_872);
x_880 = 0;
x_881 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_881, 0, x_879);
lean_ctor_set_uint8(x_881, sizeof(void*)*1, x_880);
x_882 = l_Repr_addAppParen(x_881, x_2);
return x_882;
}
}
}
default: 
{
uint8_t x_883; 
x_883 = !lean_is_exclusive(x_1);
if (x_883 == 0)
{
lean_object* x_884; lean_object* x_885; uint8_t x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_884 = lean_ctor_get(x_1, 0);
x_885 = lean_unsigned_to_nat(1024u);
x_886 = lean_nat_dec_le(x_885, x_2);
x_887 = l_String_quote(x_884);
lean_dec(x_884);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_887);
x_888 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__103;
x_889 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_889, 0, x_888);
lean_ctor_set(x_889, 1, x_1);
if (x_886 == 0)
{
lean_object* x_890; lean_object* x_891; uint8_t x_892; lean_object* x_893; lean_object* x_894; 
x_890 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_891 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_891, 0, x_890);
lean_ctor_set(x_891, 1, x_889);
x_892 = 0;
x_893 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_893, 0, x_891);
lean_ctor_set_uint8(x_893, sizeof(void*)*1, x_892);
x_894 = l_Repr_addAppParen(x_893, x_2);
return x_894;
}
else
{
lean_object* x_895; lean_object* x_896; uint8_t x_897; lean_object* x_898; lean_object* x_899; 
x_895 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_896 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_896, 0, x_895);
lean_ctor_set(x_896, 1, x_889);
x_897 = 0;
x_898 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_898, 0, x_896);
lean_ctor_set_uint8(x_898, sizeof(void*)*1, x_897);
x_899 = l_Repr_addAppParen(x_898, x_2);
return x_899;
}
}
else
{
lean_object* x_900; lean_object* x_901; uint8_t x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_900 = lean_ctor_get(x_1, 0);
lean_inc(x_900);
lean_dec(x_1);
x_901 = lean_unsigned_to_nat(1024u);
x_902 = lean_nat_dec_le(x_901, x_2);
x_903 = l_String_quote(x_900);
lean_dec(x_900);
x_904 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_904, 0, x_903);
x_905 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__103;
x_906 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_906, 0, x_905);
lean_ctor_set(x_906, 1, x_904);
if (x_902 == 0)
{
lean_object* x_907; lean_object* x_908; uint8_t x_909; lean_object* x_910; lean_object* x_911; 
x_907 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3;
x_908 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_908, 0, x_907);
lean_ctor_set(x_908, 1, x_906);
x_909 = 0;
x_910 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_910, 0, x_908);
lean_ctor_set_uint8(x_910, sizeof(void*)*1, x_909);
x_911 = l_Repr_addAppParen(x_910, x_2);
return x_911;
}
else
{
lean_object* x_912; lean_object* x_913; uint8_t x_914; lean_object* x_915; lean_object* x_916; 
x_912 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6;
x_913 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_913, 0, x_912);
lean_ctor_set(x_913, 1, x_906);
x_914 = 0;
x_915 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_915, 0, x_913);
lean_ctor_set_uint8(x_915, sizeof(void*)*1, x_914);
x_916 = l_Repr_addAppParen(x_915, x_2);
return x_916;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprCliError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprCliError() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprCliError___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_CliError_toString___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("missing command", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown command '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("missing ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" for ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid argument for ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("; expected ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown short option '-", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown long option '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected arguments: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the `+` option is an Elan feature; rerun Lake via Elan and ensure this option comes first.", 90, 90);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown package template `", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown configuration language `", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_CliError_toString___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown module `", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown package `", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" facet `", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown target `", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package '", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has no module '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has no target '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is not a build target (perhaps you meant 'lake query'\?)", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid script spec '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' (too many '", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("')", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid facet `", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`; target ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" has no facets", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown executable ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown script ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no documentation provided for `", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' (too many '/')", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("output configuration file already exists: ", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not detect a Lean installation", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not detect the configuration of the Lake installation", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected Lean commit ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", but got ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_toString___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nothing", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lake_CliError_toString___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_CliError_toString___closed__2;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lake_CliError_toString___closed__3;
x_7 = lean_string_append(x_5, x_6);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lake_CliError_toString___closed__4;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lake_CliError_toString___closed__5;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_CliError_toString___closed__4;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lake_CliError_toString___closed__6;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_13);
lean_dec(x_13);
x_20 = l_Lake_CliError_toString___closed__5;
x_21 = lean_string_append(x_19, x_20);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lake_CliError_toString___closed__7;
x_25 = lean_string_append(x_24, x_22);
lean_dec(x_22);
x_26 = l_Lake_CliError_toString___closed__8;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_23);
lean_dec(x_23);
x_29 = l_Lake_CliError_toString___closed__5;
x_30 = lean_string_append(x_28, x_29);
return x_30;
}
case 5:
{
lean_object* x_31; lean_object* x_32; uint32_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lake_CliError_toString___closed__5;
x_33 = lean_unbox_uint32(x_31);
lean_dec(x_31);
x_34 = lean_string_push(x_32, x_33);
x_35 = l_Lake_CliError_toString___closed__9;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lake_CliError_toString___closed__3;
x_38 = lean_string_append(x_36, x_37);
return x_38;
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l_Lake_CliError_toString___closed__10;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lake_CliError_toString___closed__3;
x_43 = lean_string_append(x_41, x_42);
return x_43;
}
case 7:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lake_CliError_toString___closed__11;
x_46 = l_String_intercalate(x_45, x_44);
x_47 = l_Lake_CliError_toString___closed__12;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lake_CliError_toString___closed__5;
x_50 = lean_string_append(x_48, x_49);
return x_50;
}
case 8:
{
lean_object* x_51; 
x_51 = l_Lake_CliError_toString___closed__13;
return x_51;
}
case 9:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
lean_dec(x_1);
x_53 = l_Lake_CliError_toString___closed__14;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = l_Lake_CliError_toString___closed__15;
x_56 = lean_string_append(x_54, x_55);
return x_56;
}
case 10:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
lean_dec(x_1);
x_58 = l_Lake_CliError_toString___closed__16;
x_59 = lean_string_append(x_58, x_57);
lean_dec(x_57);
x_60 = l_Lake_CliError_toString___closed__15;
x_61 = lean_string_append(x_59, x_60);
return x_61;
}
case 11:
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
lean_dec(x_1);
x_63 = 0;
x_64 = l_Lake_CliError_toString___closed__17;
x_65 = l_Lean_Name_toString(x_62, x_63, x_64);
x_66 = l_Lake_CliError_toString___closed__18;
x_67 = lean_string_append(x_66, x_65);
lean_dec(x_65);
x_68 = l_Lake_CliError_toString___closed__15;
x_69 = lean_string_append(x_67, x_68);
return x_69;
}
case 12:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
x_71 = l_Lake_CliError_toString___closed__19;
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = l_Lake_CliError_toString___closed__15;
x_74 = lean_string_append(x_72, x_73);
return x_74;
}
case 13:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
lean_dec(x_1);
x_77 = l_Lake_CliError_toString___closed__20;
x_78 = lean_string_append(x_77, x_75);
lean_dec(x_75);
x_79 = l_Lake_CliError_toString___closed__21;
x_80 = lean_string_append(x_78, x_79);
x_81 = 0;
x_82 = l_Lake_CliError_toString___closed__17;
x_83 = l_Lean_Name_toString(x_76, x_81, x_82);
x_84 = lean_string_append(x_80, x_83);
lean_dec(x_83);
x_85 = l_Lake_CliError_toString___closed__15;
x_86 = lean_string_append(x_84, x_85);
return x_86;
}
case 14:
{
lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
lean_dec(x_1);
x_88 = 0;
x_89 = l_Lake_CliError_toString___closed__17;
x_90 = l_Lean_Name_toString(x_87, x_88, x_89);
x_91 = l_Lake_CliError_toString___closed__22;
x_92 = lean_string_append(x_91, x_90);
lean_dec(x_90);
x_93 = l_Lake_CliError_toString___closed__15;
x_94 = lean_string_append(x_92, x_93);
return x_94;
}
case 15:
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
lean_dec(x_1);
x_97 = 0;
x_98 = l_Lake_CliError_toString___closed__17;
x_99 = l_Lean_Name_toString(x_95, x_97, x_98);
x_100 = l_Lake_CliError_toString___closed__23;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = l_Lake_CliError_toString___closed__24;
x_103 = lean_string_append(x_101, x_102);
x_104 = l_Lean_Name_toString(x_96, x_97, x_98);
x_105 = lean_string_append(x_103, x_104);
lean_dec(x_104);
x_106 = l_Lake_CliError_toString___closed__3;
x_107 = lean_string_append(x_105, x_106);
return x_107;
}
case 16:
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_108 = lean_ctor_get(x_1, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_1, 1);
lean_inc(x_109);
lean_dec(x_1);
x_110 = 0;
x_111 = l_Lake_CliError_toString___closed__17;
x_112 = l_Lean_Name_toString(x_108, x_110, x_111);
x_113 = l_Lake_CliError_toString___closed__23;
x_114 = lean_string_append(x_113, x_112);
lean_dec(x_112);
x_115 = l_Lake_CliError_toString___closed__25;
x_116 = lean_string_append(x_114, x_115);
x_117 = lean_string_append(x_116, x_109);
lean_dec(x_109);
x_118 = l_Lake_CliError_toString___closed__3;
x_119 = lean_string_append(x_117, x_118);
return x_119;
}
case 17:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
lean_dec(x_1);
x_121 = l_Lake_CliError_toString___closed__3;
x_122 = lean_string_append(x_121, x_120);
lean_dec(x_120);
x_123 = l_Lake_CliError_toString___closed__26;
x_124 = lean_string_append(x_122, x_123);
return x_124;
}
case 18:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint32_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_1, 1);
lean_inc(x_126);
lean_dec(x_1);
x_127 = l_Lake_CliError_toString___closed__27;
x_128 = lean_string_append(x_127, x_125);
lean_dec(x_125);
x_129 = l_Lake_CliError_toString___closed__28;
x_130 = lean_string_append(x_128, x_129);
x_131 = l_Lake_CliError_toString___closed__5;
x_132 = lean_unbox_uint32(x_126);
lean_dec(x_126);
x_133 = lean_string_push(x_131, x_132);
x_134 = lean_string_append(x_130, x_133);
lean_dec(x_133);
x_135 = l_Lake_CliError_toString___closed__29;
x_136 = lean_string_append(x_134, x_135);
return x_136;
}
case 19:
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 1);
lean_inc(x_138);
lean_dec(x_1);
x_139 = 0;
x_140 = l_Lake_CliError_toString___closed__17;
x_141 = l_Lean_Name_toString(x_138, x_139, x_140);
x_142 = l_Lake_CliError_toString___closed__30;
x_143 = lean_string_append(x_142, x_141);
lean_dec(x_141);
x_144 = l_Lake_CliError_toString___closed__31;
x_145 = lean_string_append(x_143, x_144);
x_146 = l_Lean_Name_toString(x_137, x_139, x_140);
x_147 = lean_string_append(x_145, x_146);
lean_dec(x_146);
x_148 = l_Lake_CliError_toString___closed__32;
x_149 = lean_string_append(x_147, x_148);
return x_149;
}
case 20:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_1, 0);
lean_inc(x_150);
lean_dec(x_1);
x_151 = l_Lake_CliError_toString___closed__33;
x_152 = lean_string_append(x_151, x_150);
lean_dec(x_150);
x_153 = l_Lake_CliError_toString___closed__5;
x_154 = lean_string_append(x_152, x_153);
return x_154;
}
case 21:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_1, 0);
lean_inc(x_155);
lean_dec(x_1);
x_156 = l_Lake_CliError_toString___closed__34;
x_157 = lean_string_append(x_156, x_155);
lean_dec(x_155);
x_158 = l_Lake_CliError_toString___closed__5;
x_159 = lean_string_append(x_157, x_158);
return x_159;
}
case 22:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_1, 0);
lean_inc(x_160);
lean_dec(x_1);
x_161 = l_Lake_CliError_toString___closed__35;
x_162 = lean_string_append(x_161, x_160);
lean_dec(x_160);
x_163 = l_Lake_CliError_toString___closed__15;
x_164 = lean_string_append(x_162, x_163);
return x_164;
}
case 23:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_ctor_get(x_1, 0);
lean_inc(x_165);
lean_dec(x_1);
x_166 = l_Lake_CliError_toString___closed__27;
x_167 = lean_string_append(x_166, x_165);
lean_dec(x_165);
x_168 = l_Lake_CliError_toString___closed__36;
x_169 = lean_string_append(x_167, x_168);
return x_169;
}
case 24:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_1, 0);
lean_inc(x_170);
lean_dec(x_1);
x_171 = l_Lake_CliError_toString___closed__37;
x_172 = lean_string_append(x_171, x_170);
lean_dec(x_170);
x_173 = l_Lake_CliError_toString___closed__5;
x_174 = lean_string_append(x_172, x_173);
return x_174;
}
case 25:
{
lean_object* x_175; 
x_175 = l_Lake_CliError_toString___closed__38;
return x_175;
}
case 26:
{
lean_object* x_176; 
x_176 = l_Lake_CliError_toString___closed__39;
return x_176;
}
case 27:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_177 = lean_ctor_get(x_1, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_1, 1);
lean_inc(x_178);
lean_dec(x_1);
x_179 = l_Lake_CliError_toString___closed__40;
x_180 = lean_string_append(x_179, x_177);
lean_dec(x_177);
x_181 = l_Lake_CliError_toString___closed__41;
x_182 = lean_string_append(x_180, x_181);
x_183 = lean_string_utf8_byte_size(x_178);
x_184 = lean_unsigned_to_nat(0u);
x_185 = lean_nat_dec_eq(x_183, x_184);
lean_dec(x_183);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_string_append(x_182, x_178);
lean_dec(x_178);
x_187 = l_Lake_CliError_toString___closed__5;
x_188 = lean_string_append(x_186, x_187);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_178);
x_189 = l_Lake_CliError_toString___closed__42;
x_190 = lean_string_append(x_182, x_189);
x_191 = l_Lake_CliError_toString___closed__5;
x_192 = lean_string_append(x_190, x_191);
return x_192;
}
}
default: 
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_1, 0);
lean_inc(x_193);
lean_dec(x_1);
return x_193;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_CliError_toString___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_CliError_toString___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_CliError_instToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_CliError_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_CliError_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_CliError_instToString___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Error(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedCliError = _init_l_Lake_instInhabitedCliError();
lean_mark_persistent(l_Lake_instInhabitedCliError);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__1 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__1();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__1);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__2 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__2();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__2);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__3);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__4 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__4();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__4);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__5 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__5();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__5);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__6);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__7 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__7();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__7);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__8 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__8();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__8);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__9 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__9();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__9);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__10 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__10();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__10);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__11 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__11();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__11);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__12 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__12();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__12);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__13 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__13();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__13);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__14 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__14();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__14);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__15 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__15();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__15);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__16 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__16();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__16);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__17 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__17();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__17);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__18 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__18();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__18);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__19 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__19();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__19);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__20 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__20();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__20);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__21 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__21();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__21);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__22 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__22();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__22);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__23 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__23();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__23);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__24 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__24();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__24);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__25 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__25();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__25);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__26 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__26();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__26);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__27 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__27();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__27);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__28 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__28();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__28);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__29 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__29();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__29);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__30 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__30();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__30);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__31 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__31();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__31);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__32 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__32();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__32);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__33 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__33();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__33);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__34 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__34();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__34);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__35 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__35();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__35);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__36 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__36();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__36);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__37 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__37();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__37);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__38 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__38();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__38);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__39 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__39();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__39);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__40 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__40();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__40);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__41 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__41();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__41);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__42 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__42();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__42);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__43 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__43();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__43);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__44 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__44();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__44);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__45 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__45();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__45);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__46 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__46();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__46);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__47 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__47();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__47);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__48 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__48();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__48);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__49 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__49();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__49);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__50 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__50();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__50);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__51 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__51();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__51);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__52 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__52();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__52);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__53 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__53();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__53);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__54 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__54();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__54);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__55 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__55();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__55);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__56 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__56();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__56);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__57 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__57();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__57);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__58 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__58();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__58);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__59 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__59();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__59);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__60 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__60();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__60);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__61 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__61();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__61);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__62 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__62();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__62);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__63 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__63();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__63);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__64 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__64();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__64);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__65 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__65();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__65);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__66 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__66();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__66);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__67 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__67();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__67);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__68 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__68();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__68);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__69 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__69();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__69);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__70 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__70();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__70);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__71 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__71();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__71);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__72 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__72();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__72);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__73 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__73();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__73);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__74 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__74();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__74);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__75 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__75();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__75);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__76 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__76();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__76);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__77 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__77();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__77);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__78 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__78();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__78);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__79 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__79();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__79);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__80 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__80();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__80);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__81 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__81();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__81);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__82 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__82();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__82);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__83 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__83();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__83);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__84 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__84();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__84);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__85 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__85();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__85);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__86 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__86();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__86);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__87 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__87();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__87);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__88 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__88();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__88);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__89 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__89();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__89);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__90 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__90();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__90);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__91 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__91();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__91);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__92 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__92();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__92);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__93 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__93();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__93);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__94 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__94();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__94);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__95 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__95();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__95);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__96 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__96();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__96);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__97 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__97();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__97);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__98 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__98();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__98);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__99 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__99();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__99);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__100 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__100();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__100);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__101 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__101();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__101);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__102 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__102();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__102);
l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__103 = _init_l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__103();
lean_mark_persistent(l___private_Lake_CLI_Error_0__Lake_reprCliError____x40_Lake_CLI_Error___hyg_306____closed__103);
l_Lake_instReprCliError___closed__1 = _init_l_Lake_instReprCliError___closed__1();
lean_mark_persistent(l_Lake_instReprCliError___closed__1);
l_Lake_instReprCliError = _init_l_Lake_instReprCliError();
lean_mark_persistent(l_Lake_instReprCliError);
l_Lake_CliError_toString___closed__1 = _init_l_Lake_CliError_toString___closed__1();
lean_mark_persistent(l_Lake_CliError_toString___closed__1);
l_Lake_CliError_toString___closed__2 = _init_l_Lake_CliError_toString___closed__2();
lean_mark_persistent(l_Lake_CliError_toString___closed__2);
l_Lake_CliError_toString___closed__3 = _init_l_Lake_CliError_toString___closed__3();
lean_mark_persistent(l_Lake_CliError_toString___closed__3);
l_Lake_CliError_toString___closed__4 = _init_l_Lake_CliError_toString___closed__4();
lean_mark_persistent(l_Lake_CliError_toString___closed__4);
l_Lake_CliError_toString___closed__5 = _init_l_Lake_CliError_toString___closed__5();
lean_mark_persistent(l_Lake_CliError_toString___closed__5);
l_Lake_CliError_toString___closed__6 = _init_l_Lake_CliError_toString___closed__6();
lean_mark_persistent(l_Lake_CliError_toString___closed__6);
l_Lake_CliError_toString___closed__7 = _init_l_Lake_CliError_toString___closed__7();
lean_mark_persistent(l_Lake_CliError_toString___closed__7);
l_Lake_CliError_toString___closed__8 = _init_l_Lake_CliError_toString___closed__8();
lean_mark_persistent(l_Lake_CliError_toString___closed__8);
l_Lake_CliError_toString___closed__9 = _init_l_Lake_CliError_toString___closed__9();
lean_mark_persistent(l_Lake_CliError_toString___closed__9);
l_Lake_CliError_toString___closed__10 = _init_l_Lake_CliError_toString___closed__10();
lean_mark_persistent(l_Lake_CliError_toString___closed__10);
l_Lake_CliError_toString___closed__11 = _init_l_Lake_CliError_toString___closed__11();
lean_mark_persistent(l_Lake_CliError_toString___closed__11);
l_Lake_CliError_toString___closed__12 = _init_l_Lake_CliError_toString___closed__12();
lean_mark_persistent(l_Lake_CliError_toString___closed__12);
l_Lake_CliError_toString___closed__13 = _init_l_Lake_CliError_toString___closed__13();
lean_mark_persistent(l_Lake_CliError_toString___closed__13);
l_Lake_CliError_toString___closed__14 = _init_l_Lake_CliError_toString___closed__14();
lean_mark_persistent(l_Lake_CliError_toString___closed__14);
l_Lake_CliError_toString___closed__15 = _init_l_Lake_CliError_toString___closed__15();
lean_mark_persistent(l_Lake_CliError_toString___closed__15);
l_Lake_CliError_toString___closed__16 = _init_l_Lake_CliError_toString___closed__16();
lean_mark_persistent(l_Lake_CliError_toString___closed__16);
l_Lake_CliError_toString___closed__17 = _init_l_Lake_CliError_toString___closed__17();
lean_mark_persistent(l_Lake_CliError_toString___closed__17);
l_Lake_CliError_toString___closed__18 = _init_l_Lake_CliError_toString___closed__18();
lean_mark_persistent(l_Lake_CliError_toString___closed__18);
l_Lake_CliError_toString___closed__19 = _init_l_Lake_CliError_toString___closed__19();
lean_mark_persistent(l_Lake_CliError_toString___closed__19);
l_Lake_CliError_toString___closed__20 = _init_l_Lake_CliError_toString___closed__20();
lean_mark_persistent(l_Lake_CliError_toString___closed__20);
l_Lake_CliError_toString___closed__21 = _init_l_Lake_CliError_toString___closed__21();
lean_mark_persistent(l_Lake_CliError_toString___closed__21);
l_Lake_CliError_toString___closed__22 = _init_l_Lake_CliError_toString___closed__22();
lean_mark_persistent(l_Lake_CliError_toString___closed__22);
l_Lake_CliError_toString___closed__23 = _init_l_Lake_CliError_toString___closed__23();
lean_mark_persistent(l_Lake_CliError_toString___closed__23);
l_Lake_CliError_toString___closed__24 = _init_l_Lake_CliError_toString___closed__24();
lean_mark_persistent(l_Lake_CliError_toString___closed__24);
l_Lake_CliError_toString___closed__25 = _init_l_Lake_CliError_toString___closed__25();
lean_mark_persistent(l_Lake_CliError_toString___closed__25);
l_Lake_CliError_toString___closed__26 = _init_l_Lake_CliError_toString___closed__26();
lean_mark_persistent(l_Lake_CliError_toString___closed__26);
l_Lake_CliError_toString___closed__27 = _init_l_Lake_CliError_toString___closed__27();
lean_mark_persistent(l_Lake_CliError_toString___closed__27);
l_Lake_CliError_toString___closed__28 = _init_l_Lake_CliError_toString___closed__28();
lean_mark_persistent(l_Lake_CliError_toString___closed__28);
l_Lake_CliError_toString___closed__29 = _init_l_Lake_CliError_toString___closed__29();
lean_mark_persistent(l_Lake_CliError_toString___closed__29);
l_Lake_CliError_toString___closed__30 = _init_l_Lake_CliError_toString___closed__30();
lean_mark_persistent(l_Lake_CliError_toString___closed__30);
l_Lake_CliError_toString___closed__31 = _init_l_Lake_CliError_toString___closed__31();
lean_mark_persistent(l_Lake_CliError_toString___closed__31);
l_Lake_CliError_toString___closed__32 = _init_l_Lake_CliError_toString___closed__32();
lean_mark_persistent(l_Lake_CliError_toString___closed__32);
l_Lake_CliError_toString___closed__33 = _init_l_Lake_CliError_toString___closed__33();
lean_mark_persistent(l_Lake_CliError_toString___closed__33);
l_Lake_CliError_toString___closed__34 = _init_l_Lake_CliError_toString___closed__34();
lean_mark_persistent(l_Lake_CliError_toString___closed__34);
l_Lake_CliError_toString___closed__35 = _init_l_Lake_CliError_toString___closed__35();
lean_mark_persistent(l_Lake_CliError_toString___closed__35);
l_Lake_CliError_toString___closed__36 = _init_l_Lake_CliError_toString___closed__36();
lean_mark_persistent(l_Lake_CliError_toString___closed__36);
l_Lake_CliError_toString___closed__37 = _init_l_Lake_CliError_toString___closed__37();
lean_mark_persistent(l_Lake_CliError_toString___closed__37);
l_Lake_CliError_toString___closed__38 = _init_l_Lake_CliError_toString___closed__38();
lean_mark_persistent(l_Lake_CliError_toString___closed__38);
l_Lake_CliError_toString___closed__39 = _init_l_Lake_CliError_toString___closed__39();
lean_mark_persistent(l_Lake_CliError_toString___closed__39);
l_Lake_CliError_toString___closed__40 = _init_l_Lake_CliError_toString___closed__40();
lean_mark_persistent(l_Lake_CliError_toString___closed__40);
l_Lake_CliError_toString___closed__41 = _init_l_Lake_CliError_toString___closed__41();
lean_mark_persistent(l_Lake_CliError_toString___closed__41);
l_Lake_CliError_toString___closed__42 = _init_l_Lake_CliError_toString___closed__42();
lean_mark_persistent(l_Lake_CliError_toString___closed__42);
l_Lake_CliError_instToString___closed__1 = _init_l_Lake_CliError_instToString___closed__1();
lean_mark_persistent(l_Lake_CliError_instToString___closed__1);
l_Lake_CliError_instToString = _init_l_Lake_CliError_instToString();
lean_mark_persistent(l_Lake_CliError_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
