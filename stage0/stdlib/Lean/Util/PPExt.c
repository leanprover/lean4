// Lean compiler output
// Module: Lean.Util.PPExt
// Imports: Init Lean.Environment Lean.MetavarContext Lean.Data.OpenDecl
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
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__5;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__1;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Lean_MetavarContext___instance__4___closed__1;
lean_object* l_Lean_PPContext_mctx___default;
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__7;
lean_object* l_Lean_PPContext_opts___default;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__3;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PPContext_lctx___default;
lean_object* l_Lean_PPContext_openDecls___default;
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129____lambda__1(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__2;
lean_object* l_Lean_Lean_Util_PPExt___instance__1___closed__1;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__4;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__9;
lean_object* l_Lean_getSyntaxMaxDepth___boxed(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__6;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_LocalContext_Lean_LocalContext___instance__2___closed__1;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129____closed__1;
lean_object* l_Lean_ppFnsRef;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__1;
lean_object* l_Lean_PPContext_currNamespace___default;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__10;
uint8_t l_Lean_getPPRaw(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_getNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lean_Util_PPExt___instance__1;
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__3;
extern lean_object* l_Lean_sanitizeNamesOption___closed__1;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPRaw___boxed(lean_object*);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppExt;
extern lean_object* l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
lean_object* l_Lean_getSyntaxMaxDepth(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__2;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Lean_Environment___instance__10___closed__1;
extern lean_object* l_Lean_sanitizeNamesOption___closed__2;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntaxMaxDepth");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum depth when displaying syntax objects in messages");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("raw");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_sanitizeNamesOption___closed__2;
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) print raw expression/syntax tree");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
x_2 = l_Lean_sanitizeNamesOption___closed__1;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__5;
x_4 = lean_register_option(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__7;
x_7 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__10;
x_8 = lean_register_option(x_6, x_7, x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_getSyntaxMaxDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_KVMap_getNat(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getSyntaxMaxDepth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getSyntaxMaxDepth(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_getPPRaw(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__7;
x_3 = 0;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPRaw___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPRaw(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_mctx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MetavarContext_Lean_MetavarContext___instance__4___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_lctx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Lean_LocalContext___instance__2___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_opts___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_currNamespace___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_openDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_Util_PPExt___instance__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lean_Environment___instance__10___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lean_Util_PPExt___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lean_Util_PPExt___instance__1___closed__1;
return x_1;
}
}
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_expr_dbg_to_string(x_2);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_getSyntaxMaxDepth(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = 0;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_formatStxAux(x_6, x_7, x_8, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__1;
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__3;
x_3 = l_IO_mkRef___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____lambda__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_ppFnsRef;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129____lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129____closed__1;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_MetavarContext_instantiateMVars(x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = l_Lean_getPPRaw(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = l_Lean_ppExt;
x_11 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_10, x_9);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_3(x_12, x_1, x_6, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
lean_object* l_Lean_ppTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = l_Lean_getPPRaw(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_ppExt;
x_8 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_3(x_9, x_1, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_11 = l_Lean_getSyntaxMaxDepth(x_4);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 0;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_formatStxAux(x_12, x_13, x_14, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_MetavarContext(lean_object*);
lean_object* initialize_Lean_Data_OpenDecl(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_PPExt(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_OpenDecl(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__1);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__2);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__3);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__4 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__4);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__5 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__5);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__6 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__6);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__7 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__7);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__9 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__9();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__9);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__10 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__10();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__10);
res = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PPContext_mctx___default = _init_l_Lean_PPContext_mctx___default();
lean_mark_persistent(l_Lean_PPContext_mctx___default);
l_Lean_PPContext_lctx___default = _init_l_Lean_PPContext_lctx___default();
lean_mark_persistent(l_Lean_PPContext_lctx___default);
l_Lean_PPContext_opts___default = _init_l_Lean_PPContext_opts___default();
lean_mark_persistent(l_Lean_PPContext_opts___default);
l_Lean_PPContext_currNamespace___default = _init_l_Lean_PPContext_currNamespace___default();
lean_mark_persistent(l_Lean_PPContext_currNamespace___default);
l_Lean_PPContext_openDecls___default = _init_l_Lean_PPContext_openDecls___default();
lean_mark_persistent(l_Lean_PPContext_openDecls___default);
l_Lean_Lean_Util_PPExt___instance__1___closed__1 = _init_l_Lean_Lean_Util_PPExt___instance__1___closed__1();
lean_mark_persistent(l_Lean_Lean_Util_PPExt___instance__1___closed__1);
l_Lean_Lean_Util_PPExt___instance__1 = _init_l_Lean_Lean_Util_PPExt___instance__1();
lean_mark_persistent(l_Lean_Lean_Util_PPExt___instance__1);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__1);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__2 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__2);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__3 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94____closed__3);
res = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_94_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_ppFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppFnsRef);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129____closed__1 = _init_l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129____closed__1);
res = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_129_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_ppExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
