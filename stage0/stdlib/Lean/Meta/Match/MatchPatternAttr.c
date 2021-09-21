// Lean compiler output
// Module: Lean.Meta.Match.MatchPatternAttr
// Imports: Init Lean.Attributes
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
static lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_matchPatternAttr___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasMatchPatternAttribute___boxed(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_matchPatternAttr___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_object*);
static lean_object* l_Lean_matchPatternAttr___closed__2;
static lean_object* l_Lean_matchPatternAttr___closed__1;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__5___boxed(lean_object*);
static lean_object* l_Lean_matchPatternAttr___lambda__5___closed__1;
static lean_object* l_Lean_matchPatternAttr___closed__9;
static lean_object* l_Lean_matchPatternAttr___closed__4;
static lean_object* l_Lean_matchPatternAttr___closed__8;
static lean_object* l_Lean_matchPatternAttr___closed__3;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__6___boxed(lean_object*);
static lean_object* l_Lean_matchPatternAttr___closed__7;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_matchPatternAttr___closed__5;
static lean_object* l_Lean_matchPatternAttr___closed__11;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__5(lean_object*);
static lean_object* l_Lean_matchPatternAttr___closed__12;
LEAN_EXPORT uint8_t lean_has_match_pattern_attribute(lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_matchPatternAttr___closed__6;
static lean_object* l_Lean_matchPatternAttr___closed__10;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_matchPatternAttr___lambda__3___closed__2;
static uint32_t l_Lean_matchPatternAttr___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1;
static lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4;
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3;
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__4(lean_object*, lean_object*);
static lean_object* l_Lean_matchPatternAttr___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchPattern");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mark that a definition can be used in a pattern (remark: the dependent pattern matching compiler will unfold the definition)");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3;
x_4 = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_matchPatternAttr___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_matchPatternAttr___lambda__1___closed__2;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_matchPatternAttr___lambda__1___closed__2;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static uint32_t _init_l_Lean_matchPatternAttr___lambda__3___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___lambda__3___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_matchPatternAttr___lambda__3___closed__1;
x_3 = l_Lean_matchPatternAttr___lambda__3___closed__2;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_matchPatternAttr___lambda__3___closed__3;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___lambda__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_matchPatternAttr___lambda__5___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_matchPatternAttr___lambda__3___closed__2;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_matchPatternAttr___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_matchPatternAttr___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_matchPatternAttr___closed__1;
x_2 = l_Lean_matchPatternAttr___closed__2;
x_3 = l_Lean_matchPatternAttr___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_matchPatternAttr___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_matchPatternAttr___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_matchPatternAttr___lambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_matchPatternAttr___lambda__5___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_matchPatternAttr___lambda__6___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_matchPatternAttr___closed__6;
x_2 = lean_box(0);
x_3 = l_Lean_matchPatternAttr___closed__7;
x_4 = l_Lean_matchPatternAttr___closed__8;
x_5 = l_Lean_matchPatternAttr___closed__9;
x_6 = l_Lean_matchPatternAttr___closed__10;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_matchPatternAttr___closed__4;
x_2 = l_Lean_matchPatternAttr___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_matchPatternAttr___lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_matchPatternAttr___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_matchPatternAttr___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_matchPatternAttr___lambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_matchPatternAttr___lambda__5(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___lambda__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_matchPatternAttr___lambda__6(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lean_has_match_pattern_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_matchPatternAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_hasMatchPatternAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_match_pattern_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MatchPatternAttr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1 = _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__1);
l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2 = _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__2);
l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3 = _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__3);
l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4 = _init_l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____closed__4);
l_Lean_matchPatternAttr___lambda__1___closed__1 = _init_l_Lean_matchPatternAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_matchPatternAttr___lambda__1___closed__1);
l_Lean_matchPatternAttr___lambda__1___closed__2 = _init_l_Lean_matchPatternAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_matchPatternAttr___lambda__1___closed__2);
l_Lean_matchPatternAttr___lambda__3___closed__1 = _init_l_Lean_matchPatternAttr___lambda__3___closed__1();
l_Lean_matchPatternAttr___lambda__3___closed__2 = _init_l_Lean_matchPatternAttr___lambda__3___closed__2();
lean_mark_persistent(l_Lean_matchPatternAttr___lambda__3___closed__2);
l_Lean_matchPatternAttr___lambda__3___closed__3 = _init_l_Lean_matchPatternAttr___lambda__3___closed__3();
lean_mark_persistent(l_Lean_matchPatternAttr___lambda__3___closed__3);
l_Lean_matchPatternAttr___lambda__5___closed__1 = _init_l_Lean_matchPatternAttr___lambda__5___closed__1();
lean_mark_persistent(l_Lean_matchPatternAttr___lambda__5___closed__1);
l_Lean_matchPatternAttr___closed__1 = _init_l_Lean_matchPatternAttr___closed__1();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__1);
l_Lean_matchPatternAttr___closed__2 = _init_l_Lean_matchPatternAttr___closed__2();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__2);
l_Lean_matchPatternAttr___closed__3 = _init_l_Lean_matchPatternAttr___closed__3();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__3);
l_Lean_matchPatternAttr___closed__4 = _init_l_Lean_matchPatternAttr___closed__4();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__4);
l_Lean_matchPatternAttr___closed__5 = _init_l_Lean_matchPatternAttr___closed__5();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__5);
l_Lean_matchPatternAttr___closed__6 = _init_l_Lean_matchPatternAttr___closed__6();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__6);
l_Lean_matchPatternAttr___closed__7 = _init_l_Lean_matchPatternAttr___closed__7();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__7);
l_Lean_matchPatternAttr___closed__8 = _init_l_Lean_matchPatternAttr___closed__8();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__8);
l_Lean_matchPatternAttr___closed__9 = _init_l_Lean_matchPatternAttr___closed__9();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__9);
l_Lean_matchPatternAttr___closed__10 = _init_l_Lean_matchPatternAttr___closed__10();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__10);
l_Lean_matchPatternAttr___closed__11 = _init_l_Lean_matchPatternAttr___closed__11();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__11);
l_Lean_matchPatternAttr___closed__12 = _init_l_Lean_matchPatternAttr___closed__12();
lean_mark_persistent(l_Lean_matchPatternAttr___closed__12);
res = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_matchPatternAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_matchPatternAttr);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
