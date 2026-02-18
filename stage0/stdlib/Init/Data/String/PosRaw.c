// Lean compiler output
// Module: Init.Data.String.PosRaw
// Imports: public import Init.Data.ByteArray.Basic import Init.Data.Nat.Simproc import Init.Omega
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHSubRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHSubRaw___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHSubRaw___closed__0 = (const lean_object*)&l_String_instHSubRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHSubRaw = (const lean_object*)&l_String_instHSubRaw___closed__0_value;
lean_object* l_Char_utf8Size(uint32_t);
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHSubRawChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHSubRawChar___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHSubRawChar___closed__0 = (const lean_object*)&l_String_instHSubRawChar___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHSubRawChar = (const lean_object*)&l_String_instHSubRawChar___closed__0_value;
LEAN_EXPORT lean_object* lean_string_pos_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHAddRawChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHAddRawChar___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHAddRawChar___closed__0 = (const lean_object*)&l_String_instHAddRawChar___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHAddRawChar = (const lean_object*)&l_String_instHAddRawChar___closed__0_value;
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHAddCharRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHAddCharRaw___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHAddCharRaw___closed__0 = (const lean_object*)&l_String_instHAddCharRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHAddCharRaw = (const lean_object*)&l_String_instHAddCharRaw___closed__0_value;
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHAddRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHAddRaw___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHAddRaw___closed__0 = (const lean_object*)&l_String_instHAddRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHAddRaw = (const lean_object*)&l_String_instHAddRaw___closed__0_value;
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instHAddRaw__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instHAddRaw__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instHAddRaw__1___closed__0 = (const lean_object*)&l_String_instHAddRaw__1___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instHAddRaw__1 = (const lean_object*)&l_String_instHAddRaw__1___closed__0_value;
LEAN_EXPORT lean_object* l_String_instLERaw;
LEAN_EXPORT lean_object* l_String_instLTRaw;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLeRaw(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLeRaw___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instDecidableLtRaw(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instDecidableLtRaw___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instMinRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instMinRaw___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instMinRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instMinRaw___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instMinRaw___closed__0 = (const lean_object*)&l_String_instMinRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instMinRaw = (const lean_object*)&l_String_instMinRaw___closed__0_value;
LEAN_EXPORT lean_object* l_String_instMaxRaw___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instMaxRaw___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instMaxRaw___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instMaxRaw___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instMaxRaw___closed__0 = (const lean_object*)&l_String_instMaxRaw___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instMaxRaw = (const lean_object*)&l_String_instMaxRaw___closed__0_value;
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance___boxed(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_getUTF8Byte___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_getUtf8Byte___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_min(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_min___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_pos_min(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_nat_sub(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHSubRaw___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Char_utf8Size(x_2);
x_4 = lean_nat_sub(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHSubRawChar___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_instHSubRawChar___lam__0(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_string_pos_sub(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Char_utf8Size(x_2);
x_4 = lean_nat_add(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRawChar___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_String_instHAddRawChar___lam__0(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Char_utf8Size(x_1);
x_4 = lean_nat_add(x_3, x_2);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHAddCharRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_String_instHAddCharRaw___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_nat_add(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHAddRaw___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_string_utf8_byte_size(x_2);
x_4 = lean_nat_add(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instHAddRaw__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instHAddRaw__1___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_String_instLERaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_String_instLTRaw() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLeRaw(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLeRaw___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLeRaw(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_String_instDecidableLtRaw(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instDecidableLtRaw___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_String_instDecidableLtRaw(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_instMinRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_String_instMinRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instMinRaw___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_instMaxRaw___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_String_instMaxRaw___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_instMaxRaw___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_byteDistance___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_byteDistance(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_getUTF8Byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_string_get_byte_fast(x_1, x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_getUtf8Byte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_string_get_byte_fast(x_1, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_offsetBy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_offsetBy(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_unoffsetBy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_unoffsetBy(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_increaseBy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_increaseBy(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_decreaseBy___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_decreaseBy(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_inc___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Pos_Raw_inc(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_dec___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Pos_Raw_dec(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_min(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_min___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Pos_Raw_min(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_string_pos_min(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_PosRaw(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_instLERaw = _init_l_String_instLERaw();
lean_mark_persistent(l_String_instLERaw);
l_String_instLTRaw = _init_l_String_instLTRaw();
lean_mark_persistent(l_String_instLTRaw);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
