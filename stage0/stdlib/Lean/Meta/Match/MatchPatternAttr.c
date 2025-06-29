// Lean compiler output
// Module: Lean.Meta.Match.MatchPatternAttr
// Imports: Lean.Attributes
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
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_object*);
static lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__6;
static lean_object* l_Lean_hasMatchPatternAttribute___closed__0;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
static lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__4;
static lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___closed__0;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3(lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
static lean_object* l_Lean_initFn___closed__4____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
static lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_has_match_pattern_attribute(lean_object*, lean_object*);
static lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__0;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
static lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__3;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasMatchPatternAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("match_pattern", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mark that a definition can be used in a pattern (remark: the dependent pattern matching compiler will unfold the definition)", 124, 124);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("matchPatternAttr", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__4____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
x_2 = l_Lean_initFn___closed__3____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_2 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____boxed), 4, 0);
x_3 = l_Lean_initFn___closed__1____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
x_4 = l_Lean_initFn___closed__2____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
x_5 = l_Lean_initFn___closed__5____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
x_6 = lean_box(0);
x_7 = lean_box(2);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_registerTagAttribute(x_3, x_4, x_2, x_5, x_8, x_9, x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initFn___lam__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Instructs the pattern matcher to unfold occurrences of this definition.\n\nBy default, only constructors and literals can be used for pattern matching. Using\n`@[match_pattern]` allows using other definitions, as long as they eventually reduce to\nconstructors and literals.\n\nExample:\n```\n@[match_pattern]\ndef yellowString : String := \"yellow\"\n\ndef isYellow (color : String) : Bool :=\n  match color with\n  | yellowString => true\n  | _ => false\n```\n", 444, 444);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn___closed__5____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
x_3 = l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___closed__0;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(164u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(164u);
x_2 = l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(19u);
x_4 = l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__5;
x_2 = l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn___closed__5____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_;
x_3 = l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_hasMatchPatternAttribute___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_matchPatternAttr;
return x_1;
}
}
LEAN_EXPORT uint8_t lean_has_match_pattern_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_hasMatchPatternAttribute___closed__0;
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
lean_object* initialize_Lean_Attributes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MatchPatternAttr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_ = _init_l_Lean_initFn___closed__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_);
l_Lean_initFn___closed__1____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_ = _init_l_Lean_initFn___closed__1____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_);
l_Lean_initFn___closed__2____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_ = _init_l_Lean_initFn___closed__2____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_);
l_Lean_initFn___closed__3____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_ = _init_l_Lean_initFn___closed__3____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_);
l_Lean_initFn___closed__4____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_ = _init_l_Lean_initFn___closed__4____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_);
l_Lean_initFn___closed__5____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_ = _init_l_Lean_initFn___closed__5____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_);
l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___closed__0 = _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___closed__0();
lean_mark_persistent(l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1___closed__0);
if (builtin) {res = l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__0 = _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__0();
lean_mark_persistent(l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__0);
l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__1 = _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__1();
lean_mark_persistent(l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__1);
l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__2 = _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__2();
lean_mark_persistent(l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__2);
l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__3 = _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__3();
lean_mark_persistent(l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__3);
l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__4 = _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__4();
lean_mark_persistent(l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__4);
l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__5 = _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__5();
lean_mark_persistent(l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__5);
l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__6 = _init_l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__6();
lean_mark_persistent(l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3___closed__6);
if (builtin) {res = l_Lean_matchPatternAttr___regBuiltin_Lean_matchPatternAttr_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Match_MatchPatternAttr___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_matchPatternAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_matchPatternAttr);
lean_dec_ref(res);
}l_Lean_hasMatchPatternAttribute___closed__0 = _init_l_Lean_hasMatchPatternAttribute___closed__0();
lean_mark_persistent(l_Lean_hasMatchPatternAttribute___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
