// Lean compiler output
// Module: Init.GrindInstances.ToInt
// Imports: import all Init.Grind.ToInt public import Init.Data.SInt.Basic public import Init.Grind.ToInt import Init.Data.BitVec.Bootstrap import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.SInt.Lemmas import Init.Data.UInt.Lemmas import Init.System.Platform
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
lean_object* l_Int_ofNat___boxed(lean_object*);
lean_object* l_Nat_cast(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_instToIntNatCiOfNatInt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntNatCiOfNatInt;
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_nat_to_int(lean_object*);
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
static lean_object* _init_l_Lean_Grind_instToIntNatCiOfNatInt___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Int_ofNat___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Nat_cast), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Grind_instToIntNatCiOfNatInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Grind_instToIntNatCiOfNatInt___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntFinCoOfNatIntCast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_ofNat___boxed), 1, 0);
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
x_3 = lean_nat_to_int(x_2);
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
x_3 = lean_nat_to_int(x_2);
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
x_3 = lean_nat_to_int(x_2);
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
x_3 = lean_nat_to_int(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = l_Lean_Grind_instToIntUInt64UintOfNatNat___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instToIntUSizeUintNumBits___lam__0(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_usize_to_nat(x_1);
x_3 = lean_nat_to_int(x_2);
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
x_2 = lean_alloc_closure((void*)(l_Int_ofNat___boxed), 1, 0);
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
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instToIntNatCiOfNatInt___closed__0 = _init_l_Lean_Grind_instToIntNatCiOfNatInt___closed__0();
lean_mark_persistent(l_Lean_Grind_instToIntNatCiOfNatInt___closed__0);
l_Lean_Grind_instToIntNatCiOfNatInt = _init_l_Lean_Grind_instToIntNatCiOfNatInt();
lean_mark_persistent(l_Lean_Grind_instToIntNatCiOfNatInt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
