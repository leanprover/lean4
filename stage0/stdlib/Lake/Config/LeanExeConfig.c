// Lean compiler output
// Module: Lake.Config.LeanExeConfig
// Imports: Init Lake.Build.Facets Lake.Config.LeanConfig
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
static lean_object* l_Lake_LeanExeConfig_exeName___default___closed__1;
static lean_object* l_Lake_instInhabitedLeanExeConfig___closed__3;
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanExeConfig___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_LeanExeConfig_nativeFacets___default___closed__3;
static lean_object* l_Lake_LeanExeConfig_nativeFacets___default___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_srcDir___default;
LEAN_EXPORT uint8_t l_Lake_LeanExeConfig_exeName___default___lambda__1(lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanExeConfig_supportInterpreter___default;
static lean_object* l_Lake_LeanExeConfig_nativeFacets___default___closed__6;
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_root___default(lean_object*);
static lean_object* l_Lake_LeanExeConfig_extraDepTargets___default___closed__1;
static lean_object* l_Lake_instInhabitedLeanExeConfig___closed__2;
static lean_object* l_Lake_LeanExeConfig_nativeFacets___default___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_root___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanExeConfig___lambda__1(uint8_t);
static lean_object* l_Lake_instInhabitedLeanExeConfig___closed__4;
static lean_object* l_Lake_instInhabitedLeanExeConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_extraDepTargets___default;
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_exeName___default___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_LeanExeConfig_nativeFacets___default___closed__7;
static lean_object* l_Lake_LeanExeConfig_exeName___default___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_nativeFacets___default(uint8_t);
static lean_object* l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_LeanExeConfig_nativeFacets___default___closed__8;
static lean_object* l_Lake_LeanExeConfig_srcDir___default___closed__1;
static lean_object* l_Lake_LeanExeConfig_nativeFacets___default___closed__4;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_nativeFacets___default___boxed(lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanExeConfig;
static lean_object* l_Lake_LeanExeConfig_nativeFacets___default___closed__5;
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_exeName___default(lean_object*);
static lean_object* _init_l_Lake_LeanExeConfig_srcDir___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_srcDir___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanExeConfig_srcDir___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_root___default(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_root___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LeanExeConfig_root___default(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanExeConfig_exeName___default___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_exeName___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_exeName___default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanExeConfig_exeName___default___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_exeName___default(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_LeanExeConfig_exeName___default___closed__1;
x_3 = 0;
x_4 = l_Lake_LeanExeConfig_exeName___default___closed__2;
x_5 = l_Lean_Name_toStringWithSep(x_2, x_3, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_exeName___default___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_LeanExeConfig_exeName___default___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_extraDepTargets___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_extraDepTargets___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_LeanExeConfig_extraDepTargets___default___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lake_LeanExeConfig_supportInterpreter___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("o", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_nativeFacets___default___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_nativeFacets___default___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanExeConfig_nativeFacets___default___closed__3;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("export", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanExeConfig_nativeFacets___default___closed__1;
x_2 = l_Lake_LeanExeConfig_nativeFacets___default___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_nativeFacets___default___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanExeConfig_nativeFacets___default___closed__7;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_nativeFacets___default(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lake_LeanExeConfig_nativeFacets___default___closed__4;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lake_LeanExeConfig_nativeFacets___default___closed__8;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_nativeFacets___default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_LeanExeConfig_nativeFacets___default(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanExeConfig___lambda__1(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1;
x_4 = 2;
x_5 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_3);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*9, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*9 + 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instInhabitedLeanExeConfig___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lake_instInhabitedLeanExeConfig___closed__1;
x_2 = lean_box(0);
x_3 = l_Lake_instInhabitedLeanExeConfig___closed__2;
x_4 = l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1;
x_5 = 0;
x_6 = l_Lake_instInhabitedLeanExeConfig___closed__3;
x_7 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_2);
lean_ctor_set(x_7, 4, x_3);
lean_ctor_set(x_7, 5, x_4);
lean_ctor_set(x_7, 6, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*7, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_instInhabitedLeanExeConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instInhabitedLeanExeConfig___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedLeanExeConfig___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_instInhabitedLeanExeConfig___lambda__1(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Facets(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_LeanConfig(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_LeanExeConfig(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Facets(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanConfig(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_LeanExeConfig_srcDir___default___closed__1 = _init_l_Lake_LeanExeConfig_srcDir___default___closed__1();
lean_mark_persistent(l_Lake_LeanExeConfig_srcDir___default___closed__1);
l_Lake_LeanExeConfig_srcDir___default = _init_l_Lake_LeanExeConfig_srcDir___default();
lean_mark_persistent(l_Lake_LeanExeConfig_srcDir___default);
l_Lake_LeanExeConfig_exeName___default___closed__1 = _init_l_Lake_LeanExeConfig_exeName___default___closed__1();
lean_mark_persistent(l_Lake_LeanExeConfig_exeName___default___closed__1);
l_Lake_LeanExeConfig_exeName___default___closed__2 = _init_l_Lake_LeanExeConfig_exeName___default___closed__2();
lean_mark_persistent(l_Lake_LeanExeConfig_exeName___default___closed__2);
l_Lake_LeanExeConfig_extraDepTargets___default___closed__1 = _init_l_Lake_LeanExeConfig_extraDepTargets___default___closed__1();
lean_mark_persistent(l_Lake_LeanExeConfig_extraDepTargets___default___closed__1);
l_Lake_LeanExeConfig_extraDepTargets___default = _init_l_Lake_LeanExeConfig_extraDepTargets___default();
lean_mark_persistent(l_Lake_LeanExeConfig_extraDepTargets___default);
l_Lake_LeanExeConfig_supportInterpreter___default = _init_l_Lake_LeanExeConfig_supportInterpreter___default();
l_Lake_LeanExeConfig_nativeFacets___default___closed__1 = _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__1();
lean_mark_persistent(l_Lake_LeanExeConfig_nativeFacets___default___closed__1);
l_Lake_LeanExeConfig_nativeFacets___default___closed__2 = _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__2();
lean_mark_persistent(l_Lake_LeanExeConfig_nativeFacets___default___closed__2);
l_Lake_LeanExeConfig_nativeFacets___default___closed__3 = _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__3();
lean_mark_persistent(l_Lake_LeanExeConfig_nativeFacets___default___closed__3);
l_Lake_LeanExeConfig_nativeFacets___default___closed__4 = _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__4();
lean_mark_persistent(l_Lake_LeanExeConfig_nativeFacets___default___closed__4);
l_Lake_LeanExeConfig_nativeFacets___default___closed__5 = _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__5();
lean_mark_persistent(l_Lake_LeanExeConfig_nativeFacets___default___closed__5);
l_Lake_LeanExeConfig_nativeFacets___default___closed__6 = _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__6();
lean_mark_persistent(l_Lake_LeanExeConfig_nativeFacets___default___closed__6);
l_Lake_LeanExeConfig_nativeFacets___default___closed__7 = _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__7();
lean_mark_persistent(l_Lake_LeanExeConfig_nativeFacets___default___closed__7);
l_Lake_LeanExeConfig_nativeFacets___default___closed__8 = _init_l_Lake_LeanExeConfig_nativeFacets___default___closed__8();
lean_mark_persistent(l_Lake_LeanExeConfig_nativeFacets___default___closed__8);
l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1 = _init_l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig___lambda__1___closed__1);
l_Lake_instInhabitedLeanExeConfig___closed__1 = _init_l_Lake_instInhabitedLeanExeConfig___closed__1();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig___closed__1);
l_Lake_instInhabitedLeanExeConfig___closed__2 = _init_l_Lake_instInhabitedLeanExeConfig___closed__2();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig___closed__2);
l_Lake_instInhabitedLeanExeConfig___closed__3 = _init_l_Lake_instInhabitedLeanExeConfig___closed__3();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig___closed__3);
l_Lake_instInhabitedLeanExeConfig___closed__4 = _init_l_Lake_instInhabitedLeanExeConfig___closed__4();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig___closed__4);
l_Lake_instInhabitedLeanExeConfig = _init_l_Lake_instInhabitedLeanExeConfig();
lean_mark_persistent(l_Lake_instInhabitedLeanExeConfig);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
