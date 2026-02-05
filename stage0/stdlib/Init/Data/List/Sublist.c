// Lean compiler output
// Module: Init.Data.List.Sublist
// Imports: public import Init.Data.List.TakeDrop
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
LEAN_EXPORT lean_object* l_List_instTransSubsetMem(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSubset(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSublist(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSublistSubset(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSublistMem(lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isSublist___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isPrefixOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isSuffixOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransSubsetMem(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_List_instTransSubset(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_List_instTransSublist(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistSubset(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_List_instTransSubsetSublist(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_List_instTransSublistMem(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_List_isSublist___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_instDecidableSublistOfDecidableEq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableSublistOfDecidableEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_List_instDecidableSublistOfDecidableEq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableSublistOfDecidableEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_instDecidableSublistOfDecidableEq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_List_isPrefixOf___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_instDecidableIsPrefixOfDecidableEq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsPrefixOfDecidableEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_List_instDecidableIsPrefixOfDecidableEq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsPrefixOfDecidableEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_instDecidableIsPrefixOfDecidableEq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_List_isSuffixOf___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_instDecidableIsSuffixOfDecidableEq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_instDecidableIsSuffixOfDecidableEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_List_instDecidableIsSuffixOfDecidableEq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_instDecidableIsSuffixOfDecidableEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_List_instDecidableIsSuffixOfDecidableEq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
