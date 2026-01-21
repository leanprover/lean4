// Lean compiler output
// Module: Lean.Meta.CompletionName
// Imports: public import Lean.Meta.Match.MatcherInfo
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_allowCompletion___boxed(lean_object*, lean_object*);
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
extern lean_object* l_Lean_privateHeader;
static lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isBlacklisted(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_completionBlackListExt;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("completionBlackListExt", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
x_2 = l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
x_3 = l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_;
x_3 = lean_box(2);
x_4 = l_Lean_mkTagDeclarationExtension(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_completionBlackListExt;
x_4 = l_Lean_TagDeclarationExtension_tag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_CompletionName_0__Lean_Meta_isInternalNameModuloPrivate(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint32_t x_7; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_string_utf8_byte_size(x_3);
lean_inc_ref(x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_String_Slice_Pos_get_x3f(x_16, x_14);
lean_dec_ref(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint32_t x_18; 
x_18 = 65;
x_7 = x_18;
goto block_13;
}
else
{
lean_object* x_19; uint32_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_unbox_uint32(x_19);
lean_dec(x_19);
x_7 = x_20;
goto block_13;
}
block_6:
{
if (x_4 == 0)
{
x_1 = x_2;
goto _start;
}
else
{
return x_4;
}
}
block_13:
{
uint32_t x_8; uint8_t x_9; 
x_8 = 95;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
x_4 = x_9;
goto block_6;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_privateHeader;
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
x_4 = x_9;
goto block_6;
}
else
{
x_1 = x_2;
goto _start;
}
}
}
}
case 2:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 0);
x_1 = x_21;
goto _start;
}
default: 
{
uint8_t x_23; 
x_23 = 0;
return x_23;
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
x_13 = l_Lean_isAuxRecursor(x_1, x_2);
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
x_4 = l_Lean_isNoConfusion(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_5 = l_Lean_isRecCore(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Meta_completionBlackListExt;
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
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = _init_l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_);
l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = _init_l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_);
l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = _init_l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_);
l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_ = _init_l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_Meta_initFn_00___x40_Lean_Meta_CompletionName_3302084676____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_completionBlackListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_completionBlackListExt);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
