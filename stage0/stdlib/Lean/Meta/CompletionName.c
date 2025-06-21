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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_allowCompletion___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName___hyg_4_;
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4_(lean_object*);
uint8_t lean_is_no_confusion(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addToCompletionBlackList___closed__0;
extern lean_object* l_Lean_privateHeader;
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName___hyg_4_;
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_completionBlackListExt;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, uint8_t, lean_object*);
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("completionBlackListExt", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName___hyg_4_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName___hyg_4_;
x_3 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName___hyg_4_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName___hyg_4_;
x_3 = lean_box(2);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_mkTagDeclarationExtension(x_2, x_4, x_1);
return x_5;
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_get(x_5, x_9);
x_11 = 95;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
x_6 = x_12;
goto block_8;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_privateHeader;
x_14 = lean_name_eq(x_1, x_13);
if (x_14 == 0)
{
x_6 = x_12;
goto block_8;
}
else
{
x_1 = x_4;
goto _start;
}
}
block_8:
{
if (x_6 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
return x_6;
}
}
}
default: 
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 0);
x_1 = x_16;
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
uint8_t x_3; uint8_t x_10; 
x_10 = l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(x_2);
if (x_10 == 0)
{
uint8_t x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_is_aux_recursor(x_1, x_2);
x_3 = x_11;
goto block_9;
}
else
{
x_3 = x_10;
goto block_9;
}
block_9:
{
if (x_3 == 0)
{
uint8_t x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_is_no_confusion(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_isRecCore(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Meta_addToCompletionBlackList___closed__0;
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_TagDeclarationExtension_isTagged(x_6, x_1, x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_is_matcher(x_1, x_2);
return x_8;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
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
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName___hyg_4_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName___hyg_4_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_CompletionName___hyg_4_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName___hyg_4_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName___hyg_4_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_CompletionName___hyg_4_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName___hyg_4_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName___hyg_4_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_CompletionName___hyg_4_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName___hyg_4_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName___hyg_4_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_CompletionName___hyg_4_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_CompletionName___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_completionBlackListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_completionBlackListExt);
lean_dec_ref(res);
}l_Lean_Meta_addToCompletionBlackList___closed__0 = _init_l_Lean_Meta_addToCompletionBlackList___closed__0();
lean_mark_persistent(l_Lean_Meta_addToCompletionBlackList___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
