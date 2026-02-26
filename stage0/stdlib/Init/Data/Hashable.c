// Lean compiler output
// Module: Init.Data.Hashable
// Imports: public import Init.Data.String.PosRaw public import Init.Data.UInt.Basic
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
lean_object* l_UInt64_ofNat___boxed(lean_object*);
static const lean_closure_object l_instHashableNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableNat___closed__0 = (const lean_object*)&l_instHashableNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableNat = (const lean_object*)&l_instHashableNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableRaw = (const lean_object*)&l_instHashableNat___closed__0_value;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_instHashableProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instHashableBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashableBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableBool___closed__0 = (const lean_object*)&l_instHashableBool___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableBool = (const lean_object*)&l_instHashableBool___closed__0_value;
LEAN_EXPORT uint64_t l_instHashablePEmpty___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instHashablePEmpty___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashablePEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashablePEmpty___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashablePEmpty___closed__0 = (const lean_object*)&l_instHashablePEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashablePEmpty = (const lean_object*)&l_instHashablePEmpty___closed__0_value;
LEAN_EXPORT uint64_t l_instHashablePUnit___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instHashablePUnit___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashablePUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashablePUnit___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashablePUnit___closed__0 = (const lean_object*)&l_instHashablePUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashablePUnit = (const lean_object*)&l_instHashablePUnit___closed__0_value;
LEAN_EXPORT uint64_t l_instHashableOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableOption___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instHashableOption(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableList___redArg___lam__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__1___boxed__const__1;
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableList___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instHashableList(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableArray___redArg___lam__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_instHashableArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__0 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__1 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__2 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__3 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__4 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__5 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__6 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_instHashableArray___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instHashableArray___redArg___lam__1___closed__0_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__1_value)}};
static const lean_object* l_instHashableArray___redArg___lam__1___closed__7 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_instHashableArray___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_instHashableArray___redArg___lam__1___closed__7_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__2_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__3_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__4_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__5_value)}};
static const lean_object* l_instHashableArray___redArg___lam__1___closed__8 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_instHashableArray___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instHashableArray___redArg___lam__1___closed__8_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__6_value)}};
static const lean_object* l_instHashableArray___redArg___lam__1___closed__9 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__9_value;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint64_t l_instHashableArray___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableArray___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instHashableArray(lean_object*, lean_object*);
lean_object* l_UInt8_toUInt64___boxed(lean_object*);
static const lean_closure_object l_instHashableUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableUInt8___closed__0 = (const lean_object*)&l_instHashableUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableUInt8 = (const lean_object*)&l_instHashableUInt8___closed__0_value;
lean_object* l_UInt16_toUInt64___boxed(lean_object*);
static const lean_closure_object l_instHashableUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableUInt16___closed__0 = (const lean_object*)&l_instHashableUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableUInt16 = (const lean_object*)&l_instHashableUInt16___closed__0_value;
lean_object* l_UInt32_toUInt64___boxed(lean_object*);
static const lean_closure_object l_instHashableUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableUInt32___closed__0 = (const lean_object*)&l_instHashableUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableUInt32 = (const lean_object*)&l_instHashableUInt32___closed__0_value;
LEAN_EXPORT uint64_t l_instHashableUInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_instHashableUInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashableUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableUInt64___closed__0 = (const lean_object*)&l_instHashableUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableUInt64 = (const lean_object*)&l_instHashableUInt64___closed__0_value;
lean_object* l_USize_toUInt64___boxed(lean_object*);
static const lean_closure_object l_instHashableUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableUSize___closed__0 = (const lean_object*)&l_instHashableUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableUSize = (const lean_object*)&l_instHashableUSize___closed__0_value;
LEAN_EXPORT lean_object* l_instHashableFin(lean_object*);
LEAN_EXPORT lean_object* l_instHashableFin___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_instHashableChar = (const lean_object*)&l_instHashableUInt32___closed__0_value;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_instHashableInt___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instHashableInt___lam__0___closed__0;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instHashableInt___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashableInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableInt___closed__0 = (const lean_object*)&l_instHashableInt___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableInt = (const lean_object*)&l_instHashableInt___closed__0_value;
LEAN_EXPORT uint64_t l_instHashable___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instHashable___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashable___closed__0 = (const lean_object*)&l_instHashable___closed__0_value;
LEAN_EXPORT lean_object* l_instHashable(lean_object*);
LEAN_EXPORT uint64_t l_hash64(uint64_t);
LEAN_EXPORT lean_object* l_hash64___boxed(lean_object*);
LEAN_EXPORT uint64_t l_instHashableProd___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_unbox_uint64(x_6);
lean_dec_ref(x_6);
x_9 = lean_unbox_uint64(x_7);
lean_dec_ref(x_7);
x_10 = lean_uint64_mix_hash(x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = l_instHashableProd___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instHashableProd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instHashableProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l_instHashableBool___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint64_t x_2; 
x_2 = 13;
return x_2;
}
else
{
uint64_t x_3; 
x_3 = 11;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_instHashableBool___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_instHashableBool___lam__0(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_instHashablePEmpty___lam__0(uint8_t x_1) {
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instHashablePEmpty___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_instHashablePEmpty___lam__0(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_instHashablePUnit___lam__0(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = 11;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHashablePUnit___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_instHashablePUnit___lam__0(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_instHashableOption___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_3; 
lean_dec_ref(x_1);
x_3 = 11;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = 13;
x_7 = lean_unbox_uint64(x_5);
lean_dec_ref(x_5);
x_8 = lean_uint64_mix_hash(x_7, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_instHashableOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_instHashableOption___redArg___lam__0(x_1, x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instHashableOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHashableOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_instHashableList___redArg___lam__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox_uint64(x_4);
lean_dec_ref(x_4);
x_6 = lean_uint64_mix_hash(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_instHashableList___redArg___lam__0(x_1, x_4, x_3);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
static lean_object* _init_l_instHashableList___redArg___lam__1___boxed__const__1(void) {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 7;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_instHashableList___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = l_instHashableList___redArg___lam__1___boxed__const__1;
x_4 = l_List_foldl___redArg(x_1, x_3, x_2);
x_5 = lean_unbox_uint64(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_instHashableList___redArg___lam__1(x_1, x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instHashableList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_instHashableList___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_instHashableList___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instHashableList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instHashableList___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_instHashableArray___redArg___lam__0(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox_uint64(x_4);
lean_dec_ref(x_4);
x_6 = lean_uint64_mix_hash(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_instHashableArray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_instHashableArray___redArg___lam__0(x_1, x_4, x_3);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_instHashableArray___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = 7;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_2);
x_6 = ((lean_object*)(l_instHashableArray___redArg___lam__1___closed__9));
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
if (x_7 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
x_11 = l_instHashableList___redArg___lam__1___boxed__const__1;
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_1, x_2, x_9, x_10, x_11);
x_13 = lean_unbox_uint64(x_12);
lean_dec(x_12);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_5);
x_16 = l_instHashableList___redArg___lam__1___boxed__const__1;
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_6, x_1, x_2, x_14, x_15, x_16);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_instHashableArray___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_instHashableArray___redArg___lam__1(x_1, x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instHashableArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_instHashableArray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_instHashableArray___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instHashableArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instHashableArray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_instHashableUInt64___lam__0(uint64_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_instHashableUInt64___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = l_instHashableUInt64___lam__0(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instHashableFin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instHashableNat___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHashableFin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instHashableFin(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_instHashableInt___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_instHashableInt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&l_instHashableInt___lam__0___closed__0, &l_instHashableInt___lam__0___closed__0_once, _init_l_instHashableInt___lam__0___closed__0);
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; 
x_4 = lean_nat_abs(x_1);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_mul(x_5, x_4);
lean_dec(x_4);
x_7 = lean_uint64_of_nat(x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; 
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_mul(x_11, x_10);
lean_dec(x_10);
x_13 = lean_nat_add(x_12, x_9);
lean_dec(x_12);
x_14 = lean_uint64_of_nat(x_13);
lean_dec(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_instHashableInt___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_instHashableInt___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_instHashable___lam__0(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHashable___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_instHashable___lam__0(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instHashable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_instHashable___closed__0));
return x_2;
}
}
LEAN_EXPORT uint64_t l_hash64(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; 
x_2 = 11;
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_hash64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = l_hash64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_String_PosRaw(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_PosRaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instHashableList___redArg___lam__1___boxed__const__1 = _init_l_instHashableList___redArg___lam__1___boxed__const__1();
lean_mark_persistent(l_instHashableList___redArg___lam__1___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
