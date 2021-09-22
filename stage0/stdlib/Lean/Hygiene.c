// Lean compiler output
// Module: Lean.Hygiene
// Imports: Init Lean.Data.Name Lean.Data.Options Lean.Data.Format
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
LEAN_EXPORT lean_object* l_Lean_sanitizeSyntax(lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSanitizerState_userName2Sanitized___default;
static lean_object* l_Lean_getSanitizeNames___closed__4;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__1(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(uint8_t, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__1;
LEAN_EXPORT uint8_t l_Lean_getSanitizeNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_sanitizeName(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__2;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__11;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_run(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(uint8_t, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__1(size_t, size_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__3___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Format_getUnicode(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__3;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__3;
LEAN_EXPORT lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
static lean_object* l_Lean_getSanitizeNames___closed__3;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_sanitizeName___spec__1(lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__10;
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__8;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Hygiene___hyg_271_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_sanitizeName___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Nat_toSuperscriptString(lean_object*);
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__3;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__7;
extern lean_object* l_Lean_firstFrontendMacroScope;
static lean_object* l_Lean_Unhygienic_run___rarg___closed__2;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSanitizeNames___boxed(lean_object*);
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__5;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_getSanitizeNames___closed__2;
static lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getSanitizeNames___closed__1;
static lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__12;
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__6;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameSanitizerState_nameStem2Idx___default;
LEAN_EXPORT uint8_t l_Lean_sanitizeNamesDefault;
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__9;
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Unhygienic_run___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___boxed__const__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__1;
static lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__2;
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic;
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_2);
x_8 = lean_apply_2(x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_2(x_3, x_10, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
lean_ctor_set(x_3, 1, x_4);
x_9 = lean_apply_2(x_2, x_3, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_apply_2(x_2, x_11, x_6);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__1;
x_2 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__3;
x_2 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__1;
x_2 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("UnhygienicMain");
return x_1;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__9;
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__3___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__4), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__5;
x_2 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__7;
x_3 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__10;
x_4 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__11;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__12;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_pure___at_Lean_Unhygienic_instMonadQuotationUnhygienic___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Unhygienic_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_firstFrontendMacroScope;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Unhygienic_run___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_run___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Unhygienic_run___rarg___closed__1;
x_3 = l_Lean_Unhygienic_run___rarg___closed__2;
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Unhygienic_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Unhygienic_run___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_inaccessible");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("✝");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2;
x_5 = lean_name_mk_numeral(x_4, x_3);
x_6 = l_Lean_Name_append(x_2, x_5);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Nat_toSuperscriptString(x_3);
x_10 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__3;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = lean_name_append_after(x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__3;
x_14 = lean_name_append_after(x_2, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("⁻");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(x_1, x_5, x_4);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux(x_1, x_3, x_7);
return x_8;
}
default: 
{
if (x_1 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(x_1, x_3);
x_11 = lean_name_mk_numeral(x_10, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(x_1, x_3);
x_14 = l_Nat_toSuperscriptString(x_12);
x_15 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = lean_name_append_after(x_13, x_16);
return x_17;
}
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(x_3, x_2);
return x_4;
}
}
static uint8_t _init_l_Lean_sanitizeNamesDefault() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_getSanitizeNames___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pp");
return x_1;
}
}
static lean_object* _init_l_Lean_getSanitizeNames___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getSanitizeNames___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sanitizeNames");
return x_1;
}
}
static lean_object* _init_l_Lean_getSanitizeNames___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_getSanitizeNames___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getSanitizeNames(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_getSanitizeNames___closed__4;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = l_Lean_sanitizeNamesDefault;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = l_Lean_sanitizeNamesDefault;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSanitizeNames___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getSanitizeNames(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Lean_sanitizeNamesDefault;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("add suffix '_{<idx>}' to shadowed/inaccessible variables when pretty printing");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__1;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Hygiene___hyg_271_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getSanitizeNames___closed__4;
x_3 = l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__3;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_NameSanitizerState_nameStem2Idx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_NameSanitizerState_userName2Sanitized___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = l_Std_Format_getUnicode(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_name_mk_numeral(x_1, x_2);
x_9 = l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName(x_7, x_8);
x_10 = l_Lean_NameMap_contains___rarg(x_5, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_1, x_16);
lean_ctor_set(x_3, 1, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_21 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_1, x_20);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_sanitizeName___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_sanitizeName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_erase_macro_scopes(x_1);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Std_RBNode_find___at_Lean_sanitizeName___spec__1(x_4, x_3);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(x_3, x_6, x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_13 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_12, x_1, x_11);
lean_ctor_set(x_9, 2, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
lean_inc(x_14);
x_18 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_17, x_1, x_14);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_7, 1, x_19);
return x_7;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_24);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_25 = x_20;
} else {
 lean_dec_ref(x_20);
 x_25 = lean_box(0);
}
lean_inc(x_21);
x_26 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_24, x_1, x_21);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 3, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_30 = l___private_Lean_Hygiene_0__Lean_mkFreshInaccessibleUserName(x_3, x_29, x_2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
x_36 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_35, x_1, x_34);
lean_ctor_set(x_32, 2, x_36);
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
x_40 = lean_ctor_get(x_32, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
lean_inc(x_37);
x_41 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_40, x_1, x_37);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_30, 1, x_42);
return x_30;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_30, 1);
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_inc(x_44);
lean_dec(x_30);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 2);
lean_inc(x_47);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 x_48 = x_43;
} else {
 lean_dec_ref(x_43);
 x_48 = lean_box(0);
}
lean_inc(x_44);
x_49 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_47, x_1, x_44);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 3, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_sanitizeName___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_sanitizeName___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 < x_1;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = x_3;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
x_11 = x_8;
x_12 = l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(x_11, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = x_2 + x_15;
x_17 = x_13;
x_18 = lean_array_uset(x_10, x_2, x_17);
x_2 = x_16;
x_3 = x_18;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = x_4;
x_8 = lean_box_usize(x_6);
x_9 = l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___boxed__const__1;
x_10 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_7);
x_11 = x_10;
x_12 = lean_apply_1(x_11, x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = lean_array_get_size(x_19);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = x_19;
x_23 = lean_box_usize(x_21);
x_24 = l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___boxed__const__1;
x_25 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__1___boxed), 4, 3);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_22);
x_26 = x_25;
x_27 = lean_apply_1(x_26, x_2);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
case 3:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 2);
lean_inc(x_34);
x_35 = l_Std_RBNode_find___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__2(x_34, x_33);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Name_hasMacroScopes(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_mkIdentFrom(x_1, x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_sanitizeName(x_33, x_2);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = l_Lean_mkIdentFrom(x_1, x_41);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = l_Lean_mkIdentFrom(x_1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_33);
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec(x_35);
x_48 = l_Lean_mkIdentFrom(x_1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_2);
return x_49;
}
}
default: 
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__1(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_sanitizeSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_getSanitizeNames(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux(x_1, x_2);
return x_6;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Name(lean_object*);
lean_object* initialize_Lean_Data_Options(lean_object*);
lean_object* initialize_Lean_Data_Format(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Hygiene(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__1 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__1();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__1);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__2 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__2();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__2);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__3 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__3();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__3);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__5 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__5();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__5);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__6 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__6();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__6);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__7 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__7();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__7);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__8 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__8();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__8);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__9 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__9();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__9);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__10 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__10();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__10);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__11 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__11();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__11);
l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__12 = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__12();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__12);
l_Lean_Unhygienic_instMonadQuotationUnhygienic = _init_l_Lean_Unhygienic_instMonadQuotationUnhygienic();
lean_mark_persistent(l_Lean_Unhygienic_instMonadQuotationUnhygienic);
l_Lean_Unhygienic_run___rarg___closed__1 = _init_l_Lean_Unhygienic_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Unhygienic_run___rarg___closed__1);
l_Lean_Unhygienic_run___rarg___closed__2 = _init_l_Lean_Unhygienic_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Unhygienic_run___rarg___closed__2);
l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1 = _init_l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1();
lean_mark_persistent(l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__1);
l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2 = _init_l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2();
lean_mark_persistent(l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__2);
l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__3 = _init_l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__3();
lean_mark_persistent(l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserNameAux___closed__3);
l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__1 = _init_l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__1();
lean_mark_persistent(l___private_Lean_Hygiene_0__Lean_mkInaccessibleUserName___closed__1);
l_Lean_sanitizeNamesDefault = _init_l_Lean_sanitizeNamesDefault();
l_Lean_getSanitizeNames___closed__1 = _init_l_Lean_getSanitizeNames___closed__1();
lean_mark_persistent(l_Lean_getSanitizeNames___closed__1);
l_Lean_getSanitizeNames___closed__2 = _init_l_Lean_getSanitizeNames___closed__2();
lean_mark_persistent(l_Lean_getSanitizeNames___closed__2);
l_Lean_getSanitizeNames___closed__3 = _init_l_Lean_getSanitizeNames___closed__3();
lean_mark_persistent(l_Lean_getSanitizeNames___closed__3);
l_Lean_getSanitizeNames___closed__4 = _init_l_Lean_getSanitizeNames___closed__4();
lean_mark_persistent(l_Lean_getSanitizeNames___closed__4);
l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__1 = _init_l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__1);
l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__2 = _init_l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__2);
l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__3 = _init_l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Hygiene___hyg_271____closed__3);
res = l_Lean_initFn____x40_Lean_Hygiene___hyg_271_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_NameSanitizerState_nameStem2Idx___default = _init_l_Lean_NameSanitizerState_nameStem2Idx___default();
lean_mark_persistent(l_Lean_NameSanitizerState_nameStem2Idx___default);
l_Lean_NameSanitizerState_userName2Sanitized___default = _init_l_Lean_NameSanitizerState_userName2Sanitized___default();
lean_mark_persistent(l_Lean_NameSanitizerState_userName2Sanitized___default);
l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___boxed__const__1 = _init_l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___boxed__const__1();
lean_mark_persistent(l___private_Lean_Hygiene_0__Lean_sanitizeSyntaxAux___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
