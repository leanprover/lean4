// Lean compiler output
// Module: Init.GrindInstances.ToInt
// Imports: import all Init.Grind.ToInt public import Init.Grind.Ring.ToInt public import Init.Data.SInt.Lemmas
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
lean_object* l_id___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntIntIi___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Grind_instToIntIntIi___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntIntIi___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntIntIi = (const lean_object*)&l_Lean_Grind_instToIntIntIi___closed__0_value;
lean_object* l_instNatCastInt___lam__0(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntNatCiOfNatInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instNatCastInt___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntNatCiOfNatInt___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntNatCiOfNatInt___closed__0_value;
lean_object* l_Nat_cast(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntNatCiOfNatInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_cast, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Grind_instToIntNatCiOfNatInt___closed__0_value)} };
static const lean_object* l_Lean_Grind_instToIntNatCiOfNatInt___closed__1 = (const lean_object*)&l_Lean_Grind_instToIntNatCiOfNatInt___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntNatCiOfNatInt = (const lean_object*)&l_Lean_Grind_instToIntNatCiOfNatInt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntUInt8UintOfNatNat___closed__0_value;
lean_object* lean_uint16_to_nat(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntUInt16UintOfNatNat___closed__0_value;
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntUInt32UintOfNatNat___closed__0_value;
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntUInt64UintOfNatNat___closed__0_value;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntUSizeUintNumBits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instToIntUSizeUintNumBits___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntUSizeUintNumBits___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntUSizeUintNumBits = (const lean_object*)&l_Lean_Grind_instToIntUSizeUintNumBits___closed__0_value;
lean_object* l_Int8_toInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_toInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntInt8SintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntInt8SintOfNatNat___closed__0_value;
lean_object* l_Int16_toInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_toInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntInt16SintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntInt16SintOfNatNat___closed__0_value;
lean_object* l_Int32_toInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_toInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntInt32SintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntInt32SintOfNatNat___closed__0_value;
lean_object* l_Int64_toInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_toInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntInt64SintOfNatNat = (const lean_object*)&l_Lean_Grind_instToIntInt64SintOfNatNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntBitVecUint(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntBitVecUint___boxed(lean_object*);
lean_object* l_ISize_toInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instToIntISizeSintNumBits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_toInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instToIntISizeSintNumBits___closed__0 = (const lean_object*)&l_Lean_Grind_instToIntISizeSintNumBits___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instToIntISizeSintNumBits = (const lean_object*)&l_Lean_Grind_instToIntISizeSintNumBits___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Grind_instToIntNatCiOfNatInt___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_instToIntFinCoOfNatIntCast(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint8_to_nat(x_1);
x_3 = l_instNatCastInt___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Grind_instToIntUInt8UintOfNatNat___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint16_to_nat(x_1);
x_3 = l_instNatCastInt___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Grind_instToIntUInt16UintOfNatNat___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l_instNatCastInt___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_Grind_instToIntUInt32UintOfNatNat___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_instNatCastInt___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___lam__0(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l_instNatCastInt___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_Lean_Grind_instToIntUSizeUintNumBits___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntBitVecUint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Grind_instToIntNatCiOfNatInt___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntBitVecUint___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Grind_instToIntBitVecUint(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
