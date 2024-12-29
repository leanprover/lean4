// Lean compiler output
// Module: Init.Grind.Tactics
// Imports: Init.Tactics
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
static lean_object* l_Lean_Parser_Tactic_grind___closed__7;
static lean_object* l_Lean_Parser_Tactic_grind___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_grind;
static lean_object* l_Lean_Grind_instBEqConfig___closed__1;
static lean_object* l_Lean_Parser_Tactic_grind___closed__2;
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig;
LEAN_EXPORT lean_object* l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_18____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_grind___closed__1;
LEAN_EXPORT uint8_t l_Lean_Grind_instInhabitedConfig;
static lean_object* l_Lean_Parser_Tactic_grind___closed__5;
static lean_object* l_Lean_Parser_Tactic_grind___closed__3;
static lean_object* l_Lean_Parser_Tactic_grind___closed__4;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_18_(uint8_t, uint8_t);
static uint8_t _init_l_Lean_Grind_instInhabitedConfig() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_18_(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_18____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_18_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Grind_instBEqConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Grind_Tactics_0__Lean_Grind_beqConfig____x40_Init_Grind_Tactics___hyg_18____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Grind_instBEqConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instBEqConfig___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Parser_Tactic_grind___closed__1;
x_2 = l_Lean_Parser_Tactic_grind___closed__2;
x_3 = l_Lean_Parser_Tactic_grind___closed__3;
x_4 = l_Lean_Parser_Tactic_grind___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Tactic_grind___closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Parser_Tactic_grind___closed__5;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_Lean_Parser_Tactic_grind___closed__6;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_grind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Tactic_grind___closed__7;
return x_1;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instInhabitedConfig = _init_l_Lean_Grind_instInhabitedConfig();
l_Lean_Grind_instBEqConfig___closed__1 = _init_l_Lean_Grind_instBEqConfig___closed__1();
lean_mark_persistent(l_Lean_Grind_instBEqConfig___closed__1);
l_Lean_Grind_instBEqConfig = _init_l_Lean_Grind_instBEqConfig();
lean_mark_persistent(l_Lean_Grind_instBEqConfig);
l_Lean_Parser_Tactic_grind___closed__1 = _init_l_Lean_Parser_Tactic_grind___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__1);
l_Lean_Parser_Tactic_grind___closed__2 = _init_l_Lean_Parser_Tactic_grind___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__2);
l_Lean_Parser_Tactic_grind___closed__3 = _init_l_Lean_Parser_Tactic_grind___closed__3();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__3);
l_Lean_Parser_Tactic_grind___closed__4 = _init_l_Lean_Parser_Tactic_grind___closed__4();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__4);
l_Lean_Parser_Tactic_grind___closed__5 = _init_l_Lean_Parser_Tactic_grind___closed__5();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__5);
l_Lean_Parser_Tactic_grind___closed__6 = _init_l_Lean_Parser_Tactic_grind___closed__6();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__6);
l_Lean_Parser_Tactic_grind___closed__7 = _init_l_Lean_Parser_Tactic_grind___closed__7();
lean_mark_persistent(l_Lean_Parser_Tactic_grind___closed__7);
l_Lean_Parser_Tactic_grind = _init_l_Lean_Parser_Tactic_grind();
lean_mark_persistent(l_Lean_Parser_Tactic_grind);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
