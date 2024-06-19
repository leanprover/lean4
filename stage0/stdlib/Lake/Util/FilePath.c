// Lean compiler output
// Module: Lake.Util.FilePath
// Imports: Init Lean.ToExpr Lean.Data.Json
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lake_instToExprFilePath__lake___lambda__1___closed__3;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_instToExprFilePath__lake___closed__1;
static lean_object* l_Lake_instToExprFilePath__lake___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_instToExprFilePath__lake___closed__4;
static lean_object* l_Lake_instToExprFilePath__lake___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_String_mapAux___at_Lake_mkRelPathString___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_instToExprFilePath__lake___closed__2;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToExprFilePath__lake;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_instToExprFilePath__lake___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_instToExprFilePath__lake___lambda__1___closed__1;
static lean_object* l_Lake_instToExprFilePath__lake___closed__3;
LEAN_EXPORT lean_object* l_Lake_instToExprFilePath__lake___lambda__1(lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_String_mapAux___at_Lake_mkRelPathString___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_4 = lean_string_utf8_get(x_2, x_1);
x_5 = 92;
x_6 = lean_uint32_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_string_utf8_set(x_2, x_1, x_4);
x_8 = lean_string_utf8_next(x_7, x_1);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_7;
goto _start;
}
else
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 47;
x_11 = lean_string_utf8_set(x_2, x_1, x_10);
x_12 = lean_string_utf8_next(x_11, x_1);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_11;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkRelPathString(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux___at_Lake_mkRelPathString___spec__1(x_3, x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_mkRelPathString(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToExprFilePath__lake___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("System", 6);
return x_1;
}
}
static lean_object* _init_l_Lake_instToExprFilePath__lake___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("FilePath", 8);
return x_1;
}
}
static lean_object* _init_l_Lake_instToExprFilePath__lake___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_instToExprFilePath__lake___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_instToExprFilePath__lake___lambda__1___closed__1;
x_2 = l_Lake_instToExprFilePath__lake___lambda__1___closed__2;
x_3 = l_Lake_instToExprFilePath__lake___lambda__1___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instToExprFilePath__lake___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_instToExprFilePath__lake___lambda__1___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToExprFilePath__lake___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_mkStrLit(x_1);
x_3 = l_Lake_instToExprFilePath__lake___lambda__1___closed__5;
x_4 = l_Lean_Expr_app___override(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instToExprFilePath__lake___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instToExprFilePath__lake___lambda__1___closed__1;
x_2 = l_Lake_instToExprFilePath__lake___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToExprFilePath__lake___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_instToExprFilePath__lake___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instToExprFilePath__lake___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToExprFilePath__lake___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instToExprFilePath__lake___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instToExprFilePath__lake___closed__3;
x_2 = l_Lake_instToExprFilePath__lake___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToExprFilePath__lake() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instToExprFilePath__lake___closed__4;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_FilePath(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instToExprFilePath__lake___lambda__1___closed__1 = _init_l_Lake_instToExprFilePath__lake___lambda__1___closed__1();
lean_mark_persistent(l_Lake_instToExprFilePath__lake___lambda__1___closed__1);
l_Lake_instToExprFilePath__lake___lambda__1___closed__2 = _init_l_Lake_instToExprFilePath__lake___lambda__1___closed__2();
lean_mark_persistent(l_Lake_instToExprFilePath__lake___lambda__1___closed__2);
l_Lake_instToExprFilePath__lake___lambda__1___closed__3 = _init_l_Lake_instToExprFilePath__lake___lambda__1___closed__3();
lean_mark_persistent(l_Lake_instToExprFilePath__lake___lambda__1___closed__3);
l_Lake_instToExprFilePath__lake___lambda__1___closed__4 = _init_l_Lake_instToExprFilePath__lake___lambda__1___closed__4();
lean_mark_persistent(l_Lake_instToExprFilePath__lake___lambda__1___closed__4);
l_Lake_instToExprFilePath__lake___lambda__1___closed__5 = _init_l_Lake_instToExprFilePath__lake___lambda__1___closed__5();
lean_mark_persistent(l_Lake_instToExprFilePath__lake___lambda__1___closed__5);
l_Lake_instToExprFilePath__lake___closed__1 = _init_l_Lake_instToExprFilePath__lake___closed__1();
lean_mark_persistent(l_Lake_instToExprFilePath__lake___closed__1);
l_Lake_instToExprFilePath__lake___closed__2 = _init_l_Lake_instToExprFilePath__lake___closed__2();
lean_mark_persistent(l_Lake_instToExprFilePath__lake___closed__2);
l_Lake_instToExprFilePath__lake___closed__3 = _init_l_Lake_instToExprFilePath__lake___closed__3();
lean_mark_persistent(l_Lake_instToExprFilePath__lake___closed__3);
l_Lake_instToExprFilePath__lake___closed__4 = _init_l_Lake_instToExprFilePath__lake___closed__4();
lean_mark_persistent(l_Lake_instToExprFilePath__lake___closed__4);
l_Lake_instToExprFilePath__lake = _init_l_Lake_instToExprFilePath__lake();
lean_mark_persistent(l_Lake_instToExprFilePath__lake);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
