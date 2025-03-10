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
static lean_object* l_Lean_Meta_addToCompletionBlackList___closed__1;
uint8_t lean_is_matcher(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__4;
static lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__3;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_allowCompletion___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4_(lean_object*);
extern lean_object* l_Lean_privateHeader;
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_completionBlackListExt;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
extern lean_object* l_Lean_noConfusionExt;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__1;
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__2;
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("completionBlackListExt", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__4;
x_3 = l_Lean_mkTagDeclarationExtension(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_addToCompletionBlackList___closed__1() {
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
x_3 = l_Lean_Meta_addToCompletionBlackList___closed__1;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_get(x_4, x_5);
x_7 = 95;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_privateHeader;
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
else
{
x_1 = x_3;
goto _start;
}
}
}
default: 
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 0);
x_1 = x_14;
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
static lean_object* _init_l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noConfusionExt;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_is_aux_recursor(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_TagDeclarationExtension_isTagged(x_5, x_1, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_isRecCore(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_addToCompletionBlackList___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_TagDeclarationExtension_isTagged(x_8, x_1, x_2);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_is_matcher(x_1, x_2);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = 1;
return x_15;
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
l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4____closed__4);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_completionBlackListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_completionBlackListExt);
lean_dec_ref(res);
}l_Lean_Meta_addToCompletionBlackList___closed__1 = _init_l_Lean_Meta_addToCompletionBlackList___closed__1();
lean_mark_persistent(l_Lean_Meta_addToCompletionBlackList___closed__1);
l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___closed__1 = _init_l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___closed__1();
lean_mark_persistent(l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
