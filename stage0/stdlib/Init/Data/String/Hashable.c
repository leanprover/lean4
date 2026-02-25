// Lean compiler output
// Module: Init.Data.String.Hashable
// Imports: public import Init.Data.Hashable public import Init.Data.String.Defs
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
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_String_instHashableRaw_hash(lean_object*);
LEAN_EXPORT lean_object* l_String_instHashableRaw_hash___boxed(lean_object*);
static const lean_closure_object l_String_instHashableRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHashableRaw_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHashableRaw___closed__0 = (const lean_object*)&l_String_instHashableRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHashableRaw = (const lean_object*)&l_String_instHashableRaw___closed__0_value;
LEAN_EXPORT uint64_t l_String_instHashablePos_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_String_instHashablePos_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos(lean_object*);
LEAN_EXPORT uint64_t l_String_instHashablePos__1_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos__1_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_String_instHashablePos__1_hash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos__1_hash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHashablePos__1(lean_object*);
LEAN_EXPORT uint64_t l_String_instHashableRaw_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = lean_uint64_of_nat(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHashableRaw_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_String_instHashableRaw_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_String_instHashablePos_hash___redArg(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = 0;
x_3 = l_String_instHashableRaw_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = lean_uint64_mix_hash(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos_hash___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_String_instHashablePos_hash___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_String_instHashablePos_hash(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
x_3 = l_String_instHashablePos_hash___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos_hash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_String_instHashablePos_hash(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_instHashablePos_hash___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_String_instHashablePos__1_hash___redArg(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = 0;
x_3 = l_String_instHashableRaw_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = lean_uint64_mix_hash(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos__1_hash___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_String_instHashablePos__1_hash___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_String_instHashablePos__1_hash(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; 
x_3 = l_String_instHashablePos__1_hash___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos__1_hash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_String_instHashablePos__1_hash(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHashablePos__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_instHashablePos__1_hash___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
