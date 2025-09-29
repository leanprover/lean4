// Lean compiler output
// Module: Lean.Meta.CompletionName
// Imports: Lean.Meta.Basic Lean.Meta.Match.MatcherInfo
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
uint8_t lean_is_matcher(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_allowCompletion___boxed(lean_object*, lean_object*);
uint8_t lean_is_no_confusion(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addToCompletionBlackList___closed__0;
extern lean_object* l_Lean_privateHeader;
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_completionBlackListExt;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("completionBlackListExt", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
x_3 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
x_3 = lean_box(2);
x_4 = l_Lean_mkTagDeclarationExtension(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_addToCompletionBlackList___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_completionBlackListExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_addToCompletionBlackList___closed__0;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_privateHeader;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_get(x_4, x_8);
x_10 = 95;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
x_5 = x_11;
goto block_7;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___closed__0;
x_13 = lean_name_eq(x_1, x_12);
if (x_13 == 0)
{
x_5 = x_11;
goto block_7;
}
else
{
x_1 = x_3;
goto _start;
}
}
block_7:
{
if (x_5 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
return x_5;
}
}
}
default: 
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
x_1 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_12; 
x_12 = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(x_2);
if (x_12 == 0)
{
uint8_t x_13; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_13 = lean_is_aux_recursor(x_1, x_2);
x_3 = x_13;
goto block_11;
}
else
{
x_3 = x_12;
goto block_11;
}
block_11:
{
if (x_3 == 0)
{
uint8_t x_4; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_4 = lean_is_no_confusion(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Lean_isRecCore(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Meta_addToCompletionBlackList___closed__0;
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_inc(x_2);
lean_inc_ref(x_1);
x_9 = l_Lean_TagDeclarationExtension_isTagged(x_6, x_1, x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_is_matcher(x_1, x_2);
return x_10;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_allowCompletion(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_allowCompletion___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_allowCompletion(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_completionBlackListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_completionBlackListExt);
lean_dec_ref(res);
}l_Lean_Meta_addToCompletionBlackList___closed__0 = _init_l_Lean_Meta_addToCompletionBlackList___closed__0();
lean_mark_persistent(l_Lean_Meta_addToCompletionBlackList___closed__0);
l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___closed__0 = _init_l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___closed__0();
lean_mark_persistent(l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
