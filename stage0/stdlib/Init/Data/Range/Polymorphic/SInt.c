// Lean compiler output
// Module: Init.Data.Range.Polymorphic.SInt
// Imports: public import Init.Data.Range.Polymorphic.Instances public import Init.Data.SInt import all Init.Data.SInt.Basic import all Init.Data.Range.Polymorphic.Internal.SignedBitVec import Init.ByCases import Init.Data.Int.LemmasAux import Init.System.Platform
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
uint8_t lean_int8_of_nat(lean_object*);
uint8_t lean_int8_neg(uint8_t);
uint8_t lean_int8_add(uint8_t, uint8_t);
uint8_t lean_int8_dec_eq(uint8_t, uint8_t);
lean_object* lean_int8_to_int(uint8_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_isize_to_int(size_t);
lean_object* l_USize_toBitVec___boxed(lean_object*);
lean_object* lean_int64_to_int_sint(uint64_t);
uint64_t lean_int64_of_nat(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint64_t lean_int64_of_int(lean_object*);
lean_object* lean_int16_to_int(uint16_t);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
size_t lean_isize_of_int(lean_object*);
lean_object* l_USize_ofBitVec___boxed(lean_object*);
lean_object* lean_int32_to_int(uint32_t);
uint64_t lean_int64_neg(uint64_t);
lean_object* lean_int_neg(lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
uint32_t lean_int32_neg(uint32_t);
size_t lean_isize_of_nat(lean_object*);
size_t lean_isize_add(size_t, size_t);
uint8_t lean_isize_dec_eq(size_t, size_t);
uint16_t lean_int16_of_nat(lean_object*);
uint16_t lean_int16_neg(uint16_t);
uint32_t lean_int32_add(uint32_t, uint32_t);
uint8_t lean_int32_dec_eq(uint32_t, uint32_t);
lean_object* l_UInt16_toBitVec___boxed(lean_object*);
uint16_t lean_int16_add(uint16_t, uint16_t);
uint8_t lean_int16_dec_eq(uint16_t, uint16_t);
uint8_t lean_int8_of_int(lean_object*);
uint64_t lean_int64_add(uint64_t, uint64_t);
uint8_t lean_int64_dec_eq(uint64_t, uint64_t);
lean_object* l_UInt64_ofBitVec___boxed(lean_object*);
lean_object* l_UInt64_toBitVec___boxed(lean_object*);
uint32_t lean_int32_of_int(lean_object*);
lean_object* l_UInt8_ofBitVec___boxed(lean_object*);
lean_object* l_UInt8_toBitVec___boxed(lean_object*);
lean_object* l_UInt32_ofBitVec___boxed(lean_object*);
lean_object* l_UInt32_toBitVec___boxed(lean_object*);
lean_object* l_UInt16_ofBitVec___boxed(lean_object*);
uint16_t lean_int16_of_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8 = (const lean_object*)&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1;
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0;
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed;
static lean_once_cell_t l_Int8_instUpwardEnumerable___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Int8_instUpwardEnumerable___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Int8_instUpwardEnumerable___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Int8_instUpwardEnumerable___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Int8_instUpwardEnumerable___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int8_instUpwardEnumerable___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Int8_instUpwardEnumerable___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Int8_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int8_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int8_instUpwardEnumerable___closed__0 = (const lean_object*)&l_Int8_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_Int8_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int8_instUpwardEnumerable___closed__1 = (const lean_object*)&l_Int8_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_Int8_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Int8_instUpwardEnumerable___closed__0_value),((lean_object*)&l_Int8_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_Int8_instUpwardEnumerable___closed__2 = (const lean_object*)&l_Int8_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_Int8_instUpwardEnumerable = (const lean_object*)&l_Int8_instUpwardEnumerable___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f;
static const lean_closure_object l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_toBitVec___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat;
LEAN_EXPORT const lean_object* l_Int8_instRxcHasSize = (const lean_object*)&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___closed__0_value;
LEAN_EXPORT lean_object* l_Int8_instRxoHasSize___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_instRxoHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int8_instRxoHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_instRxoHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int8_instRxoHasSize___closed__0 = (const lean_object*)&l_Int8_instRxoHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int8_instRxoHasSize = (const lean_object*)&l_Int8_instRxoHasSize___closed__0_value;
static lean_once_cell_t l_Int8_instRxiHasSize___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int8_instRxiHasSize___lam__0___closed__0;
static lean_once_cell_t l_Int8_instRxiHasSize___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int8_instRxiHasSize___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Int8_instRxiHasSize___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Int8_instRxiHasSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_Int8_instRxiHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_instRxiHasSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int8_instRxiHasSize___closed__0 = (const lean_object*)&l_Int8_instRxiHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int8_instRxiHasSize = (const lean_object*)&l_Int8_instRxiHasSize___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1;
LEAN_EXPORT uint16_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0;
LEAN_EXPORT uint16_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed;
static lean_once_cell_t l_Int16_instUpwardEnumerable___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Int16_instUpwardEnumerable___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Int16_instUpwardEnumerable___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_Int16_instUpwardEnumerable___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Int16_instUpwardEnumerable___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int16_instUpwardEnumerable___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Int16_instUpwardEnumerable___lam__1(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Int16_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int16_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int16_instUpwardEnumerable___closed__0 = (const lean_object*)&l_Int16_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_Int16_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int16_instUpwardEnumerable___closed__1 = (const lean_object*)&l_Int16_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_Int16_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Int16_instUpwardEnumerable___closed__0_value),((lean_object*)&l_Int16_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_Int16_instUpwardEnumerable___closed__2 = (const lean_object*)&l_Int16_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_Int16_instUpwardEnumerable = (const lean_object*)&l_Int16_instUpwardEnumerable___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f;
static const lean_closure_object l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_toBitVec___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat;
LEAN_EXPORT lean_object* l_Int16_instRxcHasSize___lam__0(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_instRxcHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int16_instRxcHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_instRxcHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int16_instRxcHasSize___closed__0 = (const lean_object*)&l_Int16_instRxcHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int16_instRxcHasSize = (const lean_object*)&l_Int16_instRxcHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_Int16_instRxoHasSize___lam__0(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_instRxoHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int16_instRxoHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_instRxoHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int16_instRxoHasSize___closed__0 = (const lean_object*)&l_Int16_instRxoHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int16_instRxoHasSize = (const lean_object*)&l_Int16_instRxoHasSize___closed__0_value;
static lean_once_cell_t l_Int16_instRxiHasSize___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int16_instRxiHasSize___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Int16_instRxiHasSize___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_Int16_instRxiHasSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_Int16_instRxiHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_instRxiHasSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int16_instRxiHasSize___closed__0 = (const lean_object*)&l_Int16_instRxiHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int16_instRxiHasSize = (const lean_object*)&l_Int16_instRxiHasSize___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1;
LEAN_EXPORT uint32_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0;
LEAN_EXPORT uint32_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed;
static lean_once_cell_t l_Int32_instUpwardEnumerable___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Int32_instUpwardEnumerable___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Int32_instUpwardEnumerable___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Int32_instUpwardEnumerable___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Int32_instUpwardEnumerable___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int32_instUpwardEnumerable___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Int32_instUpwardEnumerable___lam__1(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Int32_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int32_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int32_instUpwardEnumerable___closed__0 = (const lean_object*)&l_Int32_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_Int32_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int32_instUpwardEnumerable___closed__1 = (const lean_object*)&l_Int32_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_Int32_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Int32_instUpwardEnumerable___closed__0_value),((lean_object*)&l_Int32_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_Int32_instUpwardEnumerable___closed__2 = (const lean_object*)&l_Int32_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_Int32_instUpwardEnumerable = (const lean_object*)&l_Int32_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f;
static const lean_closure_object l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_toBitVec___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat;
LEAN_EXPORT lean_object* l_Int32_instRxcHasSize___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_instRxcHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int32_instRxcHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_instRxcHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int32_instRxcHasSize___closed__0 = (const lean_object*)&l_Int32_instRxcHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int32_instRxcHasSize = (const lean_object*)&l_Int32_instRxcHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_Int32_instRxoHasSize___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_instRxoHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int32_instRxoHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_instRxoHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int32_instRxoHasSize___closed__0 = (const lean_object*)&l_Int32_instRxoHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int32_instRxoHasSize = (const lean_object*)&l_Int32_instRxoHasSize___closed__0_value;
static lean_once_cell_t l_Int32_instRxiHasSize___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int32_instRxiHasSize___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Int32_instRxiHasSize___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Int32_instRxiHasSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_Int32_instRxiHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_instRxiHasSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int32_instRxiHasSize___closed__0 = (const lean_object*)&l_Int32_instRxiHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int32_instRxiHasSize = (const lean_object*)&l_Int32_instRxiHasSize___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2;
LEAN_EXPORT uint64_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0;
LEAN_EXPORT uint64_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed;
static lean_once_cell_t l_Int64_instUpwardEnumerable___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Int64_instUpwardEnumerable___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Int64_instUpwardEnumerable___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Int64_instUpwardEnumerable___lam__0___boxed(lean_object*);
static lean_once_cell_t l_Int64_instUpwardEnumerable___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int64_instUpwardEnumerable___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Int64_instUpwardEnumerable___lam__1(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Int64_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int64_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int64_instUpwardEnumerable___closed__0 = (const lean_object*)&l_Int64_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_Int64_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int64_instUpwardEnumerable___closed__1 = (const lean_object*)&l_Int64_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_Int64_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Int64_instUpwardEnumerable___closed__0_value),((lean_object*)&l_Int64_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_Int64_instUpwardEnumerable___closed__2 = (const lean_object*)&l_Int64_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_Int64_instUpwardEnumerable = (const lean_object*)&l_Int64_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f;
static const lean_closure_object l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_toBitVec___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat;
LEAN_EXPORT lean_object* l_Int64_instRxcHasSize___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_instRxcHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int64_instRxcHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_instRxcHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int64_instRxcHasSize___closed__0 = (const lean_object*)&l_Int64_instRxcHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int64_instRxcHasSize = (const lean_object*)&l_Int64_instRxcHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_Int64_instRxoHasSize___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_instRxoHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int64_instRxoHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_instRxoHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int64_instRxoHasSize___closed__0 = (const lean_object*)&l_Int64_instRxoHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int64_instRxoHasSize = (const lean_object*)&l_Int64_instRxoHasSize___closed__0_value;
static lean_once_cell_t l_Int64_instRxiHasSize___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int64_instRxiHasSize___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Int64_instRxiHasSize___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Int64_instRxiHasSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_Int64_instRxiHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_instRxiHasSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int64_instRxiHasSize___closed__0 = (const lean_object*)&l_Int64_instRxiHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_Int64_instRxiHasSize = (const lean_object*)&l_Int64_instRxiHasSize___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3;
LEAN_EXPORT size_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1;
LEAN_EXPORT size_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed;
static lean_once_cell_t l_ISize_instUpwardEnumerable___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_ISize_instUpwardEnumerable___lam__0___closed__0;
LEAN_EXPORT lean_object* l_ISize_instUpwardEnumerable___lam__0(size_t);
LEAN_EXPORT lean_object* l_ISize_instUpwardEnumerable___lam__0___boxed(lean_object*);
static lean_once_cell_t l_ISize_instUpwardEnumerable___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_instUpwardEnumerable___lam__1___closed__0;
LEAN_EXPORT lean_object* l_ISize_instUpwardEnumerable___lam__1(lean_object*, size_t);
LEAN_EXPORT lean_object* l_ISize_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ISize_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ISize_instUpwardEnumerable___closed__0 = (const lean_object*)&l_ISize_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_ISize_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ISize_instUpwardEnumerable___closed__1 = (const lean_object*)&l_ISize_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_ISize_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_ISize_instUpwardEnumerable___closed__0_value),((lean_object*)&l_ISize_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_ISize_instUpwardEnumerable___closed__2 = (const lean_object*)&l_ISize_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_ISize_instUpwardEnumerable = (const lean_object*)&l_ISize_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f;
static const lean_closure_object l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_toBitVec___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits;
LEAN_EXPORT lean_object* l_ISize_instRxcHasSize___lam__0(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_instRxcHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ISize_instRxcHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_instRxcHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ISize_instRxcHasSize___closed__0 = (const lean_object*)&l_ISize_instRxcHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_ISize_instRxcHasSize = (const lean_object*)&l_ISize_instRxcHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_ISize_instRxoHasSize___lam__0(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_instRxoHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ISize_instRxoHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_instRxoHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ISize_instRxoHasSize___closed__0 = (const lean_object*)&l_ISize_instRxoHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_ISize_instRxoHasSize = (const lean_object*)&l_ISize_instRxoHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_ISize_instRxiHasSize___lam__0(size_t);
LEAN_EXPORT lean_object* l_ISize_instRxiHasSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_ISize_instRxiHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_instRxiHasSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ISize_instRxiHasSize___closed__0 = (const lean_object*)&l_ISize_instRxiHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_ISize_instRxiHasSize = (const lean_object*)&l_ISize_instRxiHasSize___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg___lam__0(lean_object* v_m_1_, lean_object* v_inst_2_, lean_object* v_a_3_){
_start:
{
lean_object* v_encode_4_; lean_object* v_decode_5_; lean_object* v_succ_x3f_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_encode_4_ = lean_ctor_get(v_m_1_, 0);
lean_inc(v_encode_4_);
v_decode_5_ = lean_ctor_get(v_m_1_, 1);
lean_inc(v_decode_5_);
lean_dec_ref(v_m_1_);
v_succ_x3f_6_ = lean_ctor_get(v_inst_2_, 0);
lean_inc_ref(v_succ_x3f_6_);
lean_dec_ref(v_inst_2_);
v___x_7_ = lean_apply_1(v_encode_4_, v_a_3_);
v___x_8_ = lean_apply_1(v_succ_x3f_6_, v___x_7_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v___x_9_; 
lean_dec(v_decode_5_);
v___x_9_ = lean_box(0);
return v___x_9_;
}
else
{
lean_object* v_val_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_18_; 
v_val_10_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_18_ == 0)
{
v___x_12_ = v___x_8_;
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_val_10_);
lean_dec(v___x_8_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_14_ = lean_apply_1(v_decode_5_, v_val_10_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_14_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg___lam__1(lean_object* v_m_19_, lean_object* v_inst_20_, lean_object* v_n_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_encode_23_; lean_object* v_decode_24_; lean_object* v_succMany_x3f_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v_encode_23_ = lean_ctor_get(v_m_19_, 0);
lean_inc(v_encode_23_);
v_decode_24_ = lean_ctor_get(v_m_19_, 1);
lean_inc(v_decode_24_);
lean_dec_ref(v_m_19_);
v_succMany_x3f_25_ = lean_ctor_get(v_inst_20_, 1);
lean_inc_ref(v_succMany_x3f_25_);
lean_dec_ref(v_inst_20_);
v___x_26_ = lean_apply_1(v_encode_23_, v_a_22_);
v___x_27_ = lean_apply_2(v_succMany_x3f_25_, v_n_21_, v___x_26_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v___x_28_; 
lean_dec(v_decode_24_);
v___x_28_ = lean_box(0);
return v___x_28_;
}
else
{
lean_object* v_val_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_37_; 
v_val_29_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_37_ == 0)
{
v___x_31_ = v___x_27_;
v_isShared_32_ = v_isSharedCheck_37_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_val_29_);
lean_dec(v___x_27_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_37_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = lean_apply_1(v_decode_24_, v_val_29_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 0, v___x_33_);
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg(lean_object* v_inst_38_, lean_object* v_m_39_){
_start:
{
lean_object* v___f_40_; lean_object* v___f_41_; lean_object* v___x_42_; 
lean_inc_ref(v_inst_38_);
lean_inc_ref(v_m_39_);
v___f_40_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_40_, 0, v_m_39_);
lean_closure_set(v___f_40_, 1, v_inst_38_);
v___f_41_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_41_, 0, v_m_39_);
lean_closure_set(v___f_41_, 1, v_inst_38_);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___f_40_);
lean_ctor_set(v___x_42_, 1, v___f_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_00_u03b2_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_inst_49_, lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_m_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instUpwardEnumerable___redArg(v_inst_49_, v_m_53_);
return v___x_54_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_to_int(v___x_55_);
return v___x_56_;
}
}
lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0(uint8_t v_lo_57_, uint8_t v_hi_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_59_ = lean_int8_to_int(v_hi_58_);
v___x_60_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_61_ = lean_int_add(v___x_59_, v___x_60_);
v___x_62_ = lean_int8_to_int(v_lo_57_);
v___x_63_ = lean_int_sub(v___x_61_, v___x_62_);
lean_dec(v___x_61_);
v___x_64_ = l_Int_toNat(v___x_63_);
lean_dec(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_lo_57_ = stack[0].m_num;
uint8_t v_hi_58_ = stack[1].m_num;
lean_object* v_res_65_;
v_res_65_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0(v_lo_57_, v_hi_58_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___boxed(lean_object* v_lo_66_, lean_object* v_hi_67_){
_start:
{
uint8_t v_lo_boxed_68_; uint8_t v_hi_boxed_69_; lean_object* v_res_70_; 
v_lo_boxed_68_ = lean_unbox(v_lo_66_);
v_hi_boxed_69_ = lean_unbox(v_hi_67_);
v_res_70_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0(v_lo_boxed_68_, v_hi_boxed_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg___lam__0(lean_object* v_m_73_, lean_object* v_inst_74_, lean_object* v_lo_75_, lean_object* v_hi_76_){
_start:
{
lean_object* v_encode_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_encode_77_ = lean_ctor_get(v_m_73_, 0);
lean_inc_n(v_encode_77_, 2);
lean_dec_ref(v_m_73_);
v___x_78_ = lean_apply_1(v_encode_77_, v_lo_75_);
v___x_79_ = lean_apply_1(v_encode_77_, v_hi_76_);
v___x_80_ = lean_apply_2(v_inst_74_, v___x_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg(lean_object* v_m_81_, lean_object* v_inst_82_){
_start:
{
lean_object* v___f_83_; 
v___f_83_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg___lam__0), 4, 2);
lean_closure_set(v___f_83_, 0, v_m_81_);
lean_closure_set(v___f_83_, 1, v_inst_82_);
return v___f_83_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize(lean_object* v_00_u03b1_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_00_u03b2_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_m_94_, lean_object* v_inst_95_){
_start:
{
lean_object* v___f_96_; 
v___f_96_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg___lam__0), 4, 2);
lean_closure_set(v___f_96_, 0, v_m_94_);
lean_closure_set(v___f_96_, 1, v_inst_95_);
return v___f_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___boxed(lean_object* v_00_u03b1_97_, lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_00_u03b2_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_m_107_, lean_object* v_inst_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize(v_00_u03b1_97_, v_inst_98_, v_inst_99_, v_00_u03b2_100_, v_inst_101_, v_inst_102_, v_inst_103_, v_inst_104_, v_inst_105_, v_inst_106_, v_m_107_, v_inst_108_);
lean_dec_ref(v_inst_103_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg___lam__0(lean_object* v_m_110_, lean_object* v_inst_111_, lean_object* v_lo_112_){
_start:
{
lean_object* v_encode_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_encode_113_ = lean_ctor_get(v_m_110_, 0);
lean_inc(v_encode_113_);
lean_dec_ref(v_m_110_);
v___x_114_ = lean_apply_1(v_encode_113_, v_lo_112_);
v___x_115_ = lean_apply_1(v_inst_111_, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg(lean_object* v_m_116_, lean_object* v_inst_117_){
_start:
{
lean_object* v___f_118_; 
v___f_118_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg___lam__0), 3, 2);
lean_closure_set(v___f_118_, 0, v_m_116_);
lean_closure_set(v___f_118_, 1, v_inst_117_);
return v___f_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize(lean_object* v_00_u03b1_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_00_u03b2_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_m_129_, lean_object* v_inst_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg___lam__0), 3, 2);
lean_closure_set(v___f_131_, 0, v_m_129_);
lean_closure_set(v___f_131_, 1, v_inst_130_);
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___boxed(lean_object* v_00_u03b1_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_00_u03b2_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_m_142_, lean_object* v_inst_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize(v_00_u03b1_132_, v_inst_133_, v_inst_134_, v_00_u03b2_135_, v_inst_136_, v_inst_137_, v_inst_138_, v_inst_139_, v_inst_140_, v_inst_141_, v_m_142_, v_inst_143_);
lean_dec_ref(v_inst_138_);
return v_res_144_;
}
}
static uint8_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0(void){
_start:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(128u);
v___x_146_ = lean_int8_of_nat(v___x_145_);
return v___x_146_;
}
}
static uint8_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1(void){
_start:
{
uint8_t v___x_147_; uint8_t v___x_148_; 
v___x_147_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0);
v___x_148_ = lean_int8_neg(v___x_147_);
return v___x_148_;
}
}
static uint8_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed(void){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1);
return v___x_149_;
}
}
static uint8_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0(void){
_start:
{
lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(127u);
v___x_151_ = lean_int8_of_nat(v___x_150_);
return v___x_151_;
}
}
static uint8_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed(void){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0);
return v___x_152_;
}
}
static uint8_t _init_l_Int8_instUpwardEnumerable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_int8_of_nat(v___x_153_);
return v___x_154_;
}
}
lean_object* l_Int8_instUpwardEnumerable___lam__0(uint8_t v_i_155_){
_start:
{
uint8_t v___x_156_; uint8_t v___x_157_; uint8_t v___x_158_; uint8_t v___x_159_; 
v___x_156_ = lean_uint8_once(&l_Int8_instUpwardEnumerable___lam__0___closed__0, &l_Int8_instUpwardEnumerable___lam__0___closed__0_once, _init_l_Int8_instUpwardEnumerable___lam__0___closed__0);
v___x_157_ = lean_int8_add(v_i_155_, v___x_156_);
v___x_158_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1);
v___x_159_ = lean_int8_dec_eq(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_box(v___x_157_);
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = lean_box(0);
return v___x_162_;
}
}
}
LEAN_EXPORT void l_Int8_instUpwardEnumerable___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_i_155_ = stack[0].m_num;
lean_object* v_res_163_;
v_res_163_ = l_Int8_instUpwardEnumerable___lam__0(v_i_155_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l_Int8_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_164_){
_start:
{
uint8_t v_i_boxed_165_; lean_object* v_res_166_; 
v_i_boxed_165_ = lean_unbox(v_i_164_);
v_res_166_ = l_Int8_instUpwardEnumerable___lam__0(v_i_boxed_165_);
return v_res_166_;
}
}
static lean_object* _init_l_Int8_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
uint8_t v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0);
v___x_168_ = lean_int8_to_int(v___x_167_);
return v___x_168_;
}
}
lean_object* l_Int8_instUpwardEnumerable___lam__1(lean_object* v_n_169_, uint8_t v_i_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_171_ = lean_int8_to_int(v_i_170_);
v___x_172_ = lean_nat_to_int(v_n_169_);
v___x_173_ = lean_int_add(v___x_171_, v___x_172_);
lean_dec(v___x_172_);
v___x_174_ = lean_obj_once(&l_Int8_instUpwardEnumerable___lam__1___closed__0, &l_Int8_instUpwardEnumerable___lam__1___closed__0_once, _init_l_Int8_instUpwardEnumerable___lam__1___closed__0);
v___x_175_ = lean_int_dec_le(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_int8_of_int(v___x_173_);
lean_dec(v___x_173_);
v___x_178_ = lean_box(v___x_177_);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
}
}
LEAN_EXPORT void l_Int8_instUpwardEnumerable___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_169_ = stack[0].m_obj;
uint8_t v_i_170_ = stack[1].m_num;
lean_object* v_res_180_;
v_res_180_ = l_Int8_instUpwardEnumerable___lam__1(v_n_169_, v_i_170_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Int8_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_181_, lean_object* v_i_182_){
_start:
{
uint8_t v_i_boxed_183_; lean_object* v_res_184_; 
v_i_boxed_183_ = lean_unbox(v_i_182_);
v_res_184_ = l_Int8_instUpwardEnumerable___lam__1(v_n_181_, v_i_boxed_183_);
return v_res_184_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0(void){
_start:
{
uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1);
v___x_192_ = lean_box(v___x_191_);
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0);
return v___x_194_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1(void){
_start:
{
lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v___f_196_ = lean_alloc_closure((void*)(l_UInt8_ofBitVec___boxed), 1, 0);
v___f_197_ = ((lean_object*)(l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__0));
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___f_197_);
lean_ctor_set(v___x_198_, 1, v___f_196_);
return v___x_198_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1);
return v___x_199_;
}
}
lean_object* l_Int8_instRxoHasSize___lam__0(uint8_t v_lo_201_, uint8_t v_hi_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_203_ = lean_int8_to_int(v_hi_202_);
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_206_ = lean_int_add(v___x_203_, v___x_205_);
v___x_207_ = lean_int8_to_int(v_lo_201_);
v___x_208_ = lean_int_sub(v___x_206_, v___x_207_);
lean_dec(v___x_206_);
v___x_209_ = l_Int_toNat(v___x_208_);
lean_dec(v___x_208_);
v___x_210_ = lean_nat_sub(v___x_209_, v___x_204_);
lean_dec(v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT void l_Int8_instRxoHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_lo_201_ = stack[0].m_num;
uint8_t v_hi_202_ = stack[1].m_num;
lean_object* v_res_211_;
v_res_211_ = l_Int8_instRxoHasSize___lam__0(v_lo_201_, v_hi_202_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Int8_instRxoHasSize___lam__0___boxed(lean_object* v_lo_212_, lean_object* v_hi_213_){
_start:
{
uint8_t v_lo_boxed_214_; uint8_t v_hi_boxed_215_; lean_object* v_res_216_; 
v_lo_boxed_214_ = lean_unbox(v_lo_212_);
v_hi_boxed_215_ = lean_unbox(v_hi_213_);
v_res_216_ = l_Int8_instRxoHasSize___lam__0(v_lo_boxed_214_, v_hi_boxed_215_);
return v_res_216_;
}
}
static lean_object* _init_l_Int8_instRxiHasSize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(2u);
v___x_220_ = lean_nat_to_int(v___x_219_);
return v___x_220_;
}
}
static lean_object* _init_l_Int8_instRxiHasSize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_unsigned_to_nat(7u);
v___x_222_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__0, &l_Int8_instRxiHasSize___lam__0___closed__0_once, _init_l_Int8_instRxiHasSize___lam__0___closed__0);
v___x_223_ = l_Int_pow(v___x_222_, v___x_221_);
return v___x_223_;
}
}
lean_object* l_Int8_instRxiHasSize___lam__0(uint8_t v_lo_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_225_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__1, &l_Int8_instRxiHasSize___lam__0___closed__1_once, _init_l_Int8_instRxiHasSize___lam__0___closed__1);
v___x_226_ = lean_int8_to_int(v_lo_224_);
v___x_227_ = lean_int_sub(v___x_225_, v___x_226_);
v___x_228_ = l_Int_toNat(v___x_227_);
lean_dec(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT void l_Int8_instRxiHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_lo_224_ = stack[0].m_num;
lean_object* v_res_229_;
v_res_229_ = l_Int8_instRxiHasSize___lam__0(v_lo_224_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Int8_instRxiHasSize___lam__0___boxed(lean_object* v_lo_230_){
_start:
{
uint8_t v_lo_boxed_231_; lean_object* v_res_232_; 
v_lo_boxed_231_ = lean_unbox(v_lo_230_);
v_res_232_ = l_Int8_instRxiHasSize___lam__0(v_lo_boxed_231_);
return v_res_232_;
}
}
static uint16_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0(void){
_start:
{
lean_object* v___x_235_; uint16_t v___x_236_; 
v___x_235_ = lean_unsigned_to_nat(32768u);
v___x_236_ = lean_int16_of_nat(v___x_235_);
return v___x_236_;
}
}
static uint16_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1(void){
_start:
{
uint16_t v___x_237_; uint16_t v___x_238_; 
v___x_237_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0);
v___x_238_ = lean_int16_neg(v___x_237_);
return v___x_238_;
}
}
static uint16_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed(void){
_start:
{
uint16_t v___x_239_; 
v___x_239_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1);
return v___x_239_;
}
}
static uint16_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0(void){
_start:
{
lean_object* v___x_240_; uint16_t v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(32767u);
v___x_241_ = lean_int16_of_nat(v___x_240_);
return v___x_241_;
}
}
static uint16_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed(void){
_start:
{
uint16_t v___x_242_; 
v___x_242_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0);
return v___x_242_;
}
}
static uint16_t _init_l_Int16_instUpwardEnumerable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_243_; uint16_t v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_int16_of_nat(v___x_243_);
return v___x_244_;
}
}
lean_object* l_Int16_instUpwardEnumerable___lam__0(uint16_t v_i_245_){
_start:
{
uint16_t v___x_246_; uint16_t v___x_247_; uint16_t v___x_248_; uint8_t v___x_249_; 
v___x_246_ = lean_uint16_once(&l_Int16_instUpwardEnumerable___lam__0___closed__0, &l_Int16_instUpwardEnumerable___lam__0___closed__0_once, _init_l_Int16_instUpwardEnumerable___lam__0___closed__0);
v___x_247_ = lean_int16_add(v_i_245_, v___x_246_);
v___x_248_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1);
v___x_249_ = lean_int16_dec_eq(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_box(v___x_247_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_box(0);
return v___x_252_;
}
}
}
LEAN_EXPORT void l_Int16_instUpwardEnumerable___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_i_245_ = stack[0].m_num;
lean_object* v_res_253_;
v_res_253_ = l_Int16_instUpwardEnumerable___lam__0(v_i_245_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l_Int16_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_254_){
_start:
{
uint16_t v_i_boxed_255_; lean_object* v_res_256_; 
v_i_boxed_255_ = lean_unbox(v_i_254_);
v_res_256_ = l_Int16_instUpwardEnumerable___lam__0(v_i_boxed_255_);
return v_res_256_;
}
}
static lean_object* _init_l_Int16_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
uint16_t v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0);
v___x_258_ = lean_int16_to_int(v___x_257_);
return v___x_258_;
}
}
lean_object* l_Int16_instUpwardEnumerable___lam__1(lean_object* v_n_259_, uint16_t v_i_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_261_ = lean_int16_to_int(v_i_260_);
v___x_262_ = lean_nat_to_int(v_n_259_);
v___x_263_ = lean_int_add(v___x_261_, v___x_262_);
lean_dec(v___x_262_);
v___x_264_ = lean_obj_once(&l_Int16_instUpwardEnumerable___lam__1___closed__0, &l_Int16_instUpwardEnumerable___lam__1___closed__0_once, _init_l_Int16_instUpwardEnumerable___lam__1___closed__0);
v___x_265_ = lean_int_dec_le(v___x_263_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
return v___x_266_;
}
else
{
uint16_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_int16_of_int(v___x_263_);
lean_dec(v___x_263_);
v___x_268_ = lean_box(v___x_267_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
return v___x_269_;
}
}
}
LEAN_EXPORT void l_Int16_instUpwardEnumerable___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_259_ = stack[0].m_obj;
uint16_t v_i_260_ = stack[1].m_num;
lean_object* v_res_270_;
v_res_270_ = l_Int16_instUpwardEnumerable___lam__1(v_n_259_, v_i_260_);
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l_Int16_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_271_, lean_object* v_i_272_){
_start:
{
uint16_t v_i_boxed_273_; lean_object* v_res_274_; 
v_i_boxed_273_ = lean_unbox(v_i_272_);
v_res_274_ = l_Int16_instUpwardEnumerable___lam__1(v_n_271_, v_i_boxed_273_);
return v_res_274_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0(void){
_start:
{
uint16_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1);
v___x_282_ = lean_box(v___x_281_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f(void){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0);
return v___x_284_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1(void){
_start:
{
lean_object* v___f_286_; lean_object* v___f_287_; lean_object* v___x_288_; 
v___f_286_ = lean_alloc_closure((void*)(l_UInt16_ofBitVec___boxed), 1, 0);
v___f_287_ = ((lean_object*)(l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__0));
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___f_287_);
lean_ctor_set(v___x_288_, 1, v___f_286_);
return v___x_288_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat(void){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1);
return v___x_289_;
}
}
lean_object* l_Int16_instRxcHasSize___lam__0(uint16_t v_lo_290_, uint16_t v_hi_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_292_ = lean_int16_to_int(v_hi_291_);
v___x_293_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_294_ = lean_int_add(v___x_292_, v___x_293_);
v___x_295_ = lean_int16_to_int(v_lo_290_);
v___x_296_ = lean_int_sub(v___x_294_, v___x_295_);
lean_dec(v___x_294_);
v___x_297_ = l_Int_toNat(v___x_296_);
lean_dec(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT void l_Int16_instRxcHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_lo_290_ = stack[0].m_num;
uint16_t v_hi_291_ = stack[1].m_num;
lean_object* v_res_298_;
v_res_298_ = l_Int16_instRxcHasSize___lam__0(v_lo_290_, v_hi_291_);
stack->m_obj
 = v_res_298_;
}
LEAN_EXPORT lean_object* l_Int16_instRxcHasSize___lam__0___boxed(lean_object* v_lo_299_, lean_object* v_hi_300_){
_start:
{
uint16_t v_lo_boxed_301_; uint16_t v_hi_boxed_302_; lean_object* v_res_303_; 
v_lo_boxed_301_ = lean_unbox(v_lo_299_);
v_hi_boxed_302_ = lean_unbox(v_hi_300_);
v_res_303_ = l_Int16_instRxcHasSize___lam__0(v_lo_boxed_301_, v_hi_boxed_302_);
return v_res_303_;
}
}
lean_object* l_Int16_instRxoHasSize___lam__0(uint16_t v_lo_306_, uint16_t v_hi_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_308_ = lean_int16_to_int(v_hi_307_);
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_311_ = lean_int_add(v___x_308_, v___x_310_);
v___x_312_ = lean_int16_to_int(v_lo_306_);
v___x_313_ = lean_int_sub(v___x_311_, v___x_312_);
lean_dec(v___x_311_);
v___x_314_ = l_Int_toNat(v___x_313_);
lean_dec(v___x_313_);
v___x_315_ = lean_nat_sub(v___x_314_, v___x_309_);
lean_dec(v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT void l_Int16_instRxoHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_lo_306_ = stack[0].m_num;
uint16_t v_hi_307_ = stack[1].m_num;
lean_object* v_res_316_;
v_res_316_ = l_Int16_instRxoHasSize___lam__0(v_lo_306_, v_hi_307_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_Int16_instRxoHasSize___lam__0___boxed(lean_object* v_lo_317_, lean_object* v_hi_318_){
_start:
{
uint16_t v_lo_boxed_319_; uint16_t v_hi_boxed_320_; lean_object* v_res_321_; 
v_lo_boxed_319_ = lean_unbox(v_lo_317_);
v_hi_boxed_320_ = lean_unbox(v_hi_318_);
v_res_321_ = l_Int16_instRxoHasSize___lam__0(v_lo_boxed_319_, v_hi_boxed_320_);
return v_res_321_;
}
}
static lean_object* _init_l_Int16_instRxiHasSize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_unsigned_to_nat(15u);
v___x_325_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__0, &l_Int8_instRxiHasSize___lam__0___closed__0_once, _init_l_Int8_instRxiHasSize___lam__0___closed__0);
v___x_326_ = l_Int_pow(v___x_325_, v___x_324_);
return v___x_326_;
}
}
lean_object* l_Int16_instRxiHasSize___lam__0(uint16_t v_lo_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = lean_obj_once(&l_Int16_instRxiHasSize___lam__0___closed__0, &l_Int16_instRxiHasSize___lam__0___closed__0_once, _init_l_Int16_instRxiHasSize___lam__0___closed__0);
v___x_329_ = lean_int16_to_int(v_lo_327_);
v___x_330_ = lean_int_sub(v___x_328_, v___x_329_);
v___x_331_ = l_Int_toNat(v___x_330_);
lean_dec(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT void l_Int16_instRxiHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_lo_327_ = stack[0].m_num;
lean_object* v_res_332_;
v_res_332_ = l_Int16_instRxiHasSize___lam__0(v_lo_327_);
stack->m_obj
 = v_res_332_;
}
LEAN_EXPORT lean_object* l_Int16_instRxiHasSize___lam__0___boxed(lean_object* v_lo_333_){
_start:
{
uint16_t v_lo_boxed_334_; lean_object* v_res_335_; 
v_lo_boxed_334_ = lean_unbox(v_lo_333_);
v_res_335_ = l_Int16_instRxiHasSize___lam__0(v_lo_boxed_334_);
return v_res_335_;
}
}
static uint32_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0(void){
_start:
{
lean_object* v___x_338_; uint32_t v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(2147483648u);
v___x_339_ = lean_int32_of_nat(v___x_338_);
return v___x_339_;
}
}
static uint32_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1(void){
_start:
{
uint32_t v___x_340_; uint32_t v___x_341_; 
v___x_340_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0);
v___x_341_ = lean_int32_neg(v___x_340_);
return v___x_341_;
}
}
static uint32_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed(void){
_start:
{
uint32_t v___x_342_; 
v___x_342_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1);
return v___x_342_;
}
}
static uint32_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0(void){
_start:
{
lean_object* v___x_343_; uint32_t v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(2147483647u);
v___x_344_ = lean_int32_of_nat(v___x_343_);
return v___x_344_;
}
}
static uint32_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed(void){
_start:
{
uint32_t v___x_345_; 
v___x_345_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0);
return v___x_345_;
}
}
static uint32_t _init_l_Int32_instUpwardEnumerable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_346_; uint32_t v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_int32_of_nat(v___x_346_);
return v___x_347_;
}
}
lean_object* l_Int32_instUpwardEnumerable___lam__0(uint32_t v_i_348_){
_start:
{
uint32_t v___x_349_; uint32_t v___x_350_; uint32_t v___x_351_; uint8_t v___x_352_; 
v___x_349_ = lean_uint32_once(&l_Int32_instUpwardEnumerable___lam__0___closed__0, &l_Int32_instUpwardEnumerable___lam__0___closed__0_once, _init_l_Int32_instUpwardEnumerable___lam__0___closed__0);
v___x_350_ = lean_int32_add(v_i_348_, v___x_349_);
v___x_351_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1);
v___x_352_ = lean_int32_dec_eq(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_box_uint32(v___x_350_);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_box(0);
return v___x_355_;
}
}
}
LEAN_EXPORT void l_Int32_instUpwardEnumerable___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_i_348_ = stack[0].m_num;
lean_object* v_res_356_;
v_res_356_ = l_Int32_instUpwardEnumerable___lam__0(v_i_348_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l_Int32_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_357_){
_start:
{
uint32_t v_i_boxed_358_; lean_object* v_res_359_; 
v_i_boxed_358_ = lean_unbox_uint32(v_i_357_);
lean_dec(v_i_357_);
v_res_359_ = l_Int32_instUpwardEnumerable___lam__0(v_i_boxed_358_);
return v_res_359_;
}
}
static lean_object* _init_l_Int32_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
uint32_t v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0);
v___x_361_ = lean_int32_to_int(v___x_360_);
return v___x_361_;
}
}
lean_object* l_Int32_instUpwardEnumerable___lam__1(lean_object* v_n_362_, uint32_t v_i_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v___x_364_ = lean_int32_to_int(v_i_363_);
v___x_365_ = lean_nat_to_int(v_n_362_);
v___x_366_ = lean_int_add(v___x_364_, v___x_365_);
lean_dec(v___x_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_obj_once(&l_Int32_instUpwardEnumerable___lam__1___closed__0, &l_Int32_instUpwardEnumerable___lam__1___closed__0_once, _init_l_Int32_instUpwardEnumerable___lam__1___closed__0);
v___x_368_ = lean_int_dec_le(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
return v___x_369_;
}
else
{
uint32_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_int32_of_int(v___x_366_);
lean_dec(v___x_366_);
v___x_371_ = lean_box_uint32(v___x_370_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
}
LEAN_EXPORT void l_Int32_instUpwardEnumerable___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_362_ = stack[0].m_obj;
uint32_t v_i_363_ = stack[1].m_num;
lean_object* v_res_373_;
v_res_373_ = l_Int32_instUpwardEnumerable___lam__1(v_n_362_, v_i_363_);
stack->m_obj
 = v_res_373_;
}
LEAN_EXPORT lean_object* l_Int32_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_374_, lean_object* v_i_375_){
_start:
{
uint32_t v_i_boxed_376_; lean_object* v_res_377_; 
v_i_boxed_376_ = lean_unbox_uint32(v_i_375_);
lean_dec(v_i_375_);
v_res_377_ = l_Int32_instUpwardEnumerable___lam__1(v_n_374_, v_i_boxed_376_);
return v_res_377_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1);
v___x_385_ = lean_box_uint32(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1;
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f(void){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0);
return v___x_388_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1(void){
_start:
{
lean_object* v___f_390_; lean_object* v___f_391_; lean_object* v___x_392_; 
v___f_390_ = lean_alloc_closure((void*)(l_UInt32_ofBitVec___boxed), 1, 0);
v___f_391_ = ((lean_object*)(l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__0));
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v___f_391_);
lean_ctor_set(v___x_392_, 1, v___f_390_);
return v___x_392_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat(void){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1);
return v___x_393_;
}
}
lean_object* l_Int32_instRxcHasSize___lam__0(uint32_t v_lo_394_, uint32_t v_hi_395_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = lean_int32_to_int(v_hi_395_);
v___x_397_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_398_ = lean_int_add(v___x_396_, v___x_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_int32_to_int(v_lo_394_);
v___x_400_ = lean_int_sub(v___x_398_, v___x_399_);
lean_dec(v___x_399_);
lean_dec(v___x_398_);
v___x_401_ = l_Int_toNat(v___x_400_);
lean_dec(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT void l_Int32_instRxcHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_lo_394_ = stack[0].m_num;
uint32_t v_hi_395_ = stack[1].m_num;
lean_object* v_res_402_;
v_res_402_ = l_Int32_instRxcHasSize___lam__0(v_lo_394_, v_hi_395_);
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l_Int32_instRxcHasSize___lam__0___boxed(lean_object* v_lo_403_, lean_object* v_hi_404_){
_start:
{
uint32_t v_lo_boxed_405_; uint32_t v_hi_boxed_406_; lean_object* v_res_407_; 
v_lo_boxed_405_ = lean_unbox_uint32(v_lo_403_);
lean_dec(v_lo_403_);
v_hi_boxed_406_ = lean_unbox_uint32(v_hi_404_);
lean_dec(v_hi_404_);
v_res_407_ = l_Int32_instRxcHasSize___lam__0(v_lo_boxed_405_, v_hi_boxed_406_);
return v_res_407_;
}
}
lean_object* l_Int32_instRxoHasSize___lam__0(uint32_t v_lo_410_, uint32_t v_hi_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_412_ = lean_int32_to_int(v_hi_411_);
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_415_ = lean_int_add(v___x_412_, v___x_414_);
lean_dec(v___x_412_);
v___x_416_ = lean_int32_to_int(v_lo_410_);
v___x_417_ = lean_int_sub(v___x_415_, v___x_416_);
lean_dec(v___x_416_);
lean_dec(v___x_415_);
v___x_418_ = l_Int_toNat(v___x_417_);
lean_dec(v___x_417_);
v___x_419_ = lean_nat_sub(v___x_418_, v___x_413_);
lean_dec(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT void l_Int32_instRxoHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_lo_410_ = stack[0].m_num;
uint32_t v_hi_411_ = stack[1].m_num;
lean_object* v_res_420_;
v_res_420_ = l_Int32_instRxoHasSize___lam__0(v_lo_410_, v_hi_411_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l_Int32_instRxoHasSize___lam__0___boxed(lean_object* v_lo_421_, lean_object* v_hi_422_){
_start:
{
uint32_t v_lo_boxed_423_; uint32_t v_hi_boxed_424_; lean_object* v_res_425_; 
v_lo_boxed_423_ = lean_unbox_uint32(v_lo_421_);
lean_dec(v_lo_421_);
v_hi_boxed_424_ = lean_unbox_uint32(v_hi_422_);
lean_dec(v_hi_422_);
v_res_425_ = l_Int32_instRxoHasSize___lam__0(v_lo_boxed_423_, v_hi_boxed_424_);
return v_res_425_;
}
}
static lean_object* _init_l_Int32_instRxiHasSize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_unsigned_to_nat(31u);
v___x_429_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__0, &l_Int8_instRxiHasSize___lam__0___closed__0_once, _init_l_Int8_instRxiHasSize___lam__0___closed__0);
v___x_430_ = l_Int_pow(v___x_429_, v___x_428_);
return v___x_430_;
}
}
lean_object* l_Int32_instRxiHasSize___lam__0(uint32_t v_lo_431_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_432_ = lean_obj_once(&l_Int32_instRxiHasSize___lam__0___closed__0, &l_Int32_instRxiHasSize___lam__0___closed__0_once, _init_l_Int32_instRxiHasSize___lam__0___closed__0);
v___x_433_ = lean_int32_to_int(v_lo_431_);
v___x_434_ = lean_int_sub(v___x_432_, v___x_433_);
lean_dec(v___x_433_);
v___x_435_ = l_Int_toNat(v___x_434_);
lean_dec(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT void l_Int32_instRxiHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_lo_431_ = stack[0].m_num;
lean_object* v_res_436_;
v_res_436_ = l_Int32_instRxiHasSize___lam__0(v_lo_431_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Int32_instRxiHasSize___lam__0___boxed(lean_object* v_lo_437_){
_start:
{
uint32_t v_lo_boxed_438_; lean_object* v_res_439_; 
v_lo_boxed_438_ = lean_unbox_uint32(v_lo_437_);
lean_dec(v_lo_437_);
v_res_439_ = l_Int32_instRxiHasSize___lam__0(v_lo_boxed_438_);
return v_res_439_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0(void){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = lean_cstr_to_nat("9223372036854775808");
return v___x_442_;
}
}
static uint64_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1(void){
_start:
{
lean_object* v___x_443_; uint64_t v___x_444_; 
v___x_443_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0);
v___x_444_ = lean_int64_of_nat(v___x_443_);
return v___x_444_;
}
}
static uint64_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2(void){
_start:
{
uint64_t v___x_445_; uint64_t v___x_446_; 
v___x_445_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1);
v___x_446_ = lean_int64_neg(v___x_445_);
return v___x_446_;
}
}
static uint64_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed(void){
_start:
{
uint64_t v___x_447_; 
v___x_447_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2);
return v___x_447_;
}
}
static uint64_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0(void){
_start:
{
lean_object* v___x_448_; uint64_t v___x_449_; 
v___x_448_ = lean_cstr_to_nat("9223372036854775807");
v___x_449_ = lean_int64_of_nat(v___x_448_);
return v___x_449_;
}
}
static uint64_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed(void){
_start:
{
uint64_t v___x_450_; 
v___x_450_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0);
return v___x_450_;
}
}
static uint64_t _init_l_Int64_instUpwardEnumerable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_451_; uint64_t v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_int64_of_nat(v___x_451_);
return v___x_452_;
}
}
lean_object* l_Int64_instUpwardEnumerable___lam__0(uint64_t v_i_453_){
_start:
{
uint64_t v___x_454_; uint64_t v___x_455_; uint64_t v___x_456_; uint8_t v___x_457_; 
v___x_454_ = lean_uint64_once(&l_Int64_instUpwardEnumerable___lam__0___closed__0, &l_Int64_instUpwardEnumerable___lam__0___closed__0_once, _init_l_Int64_instUpwardEnumerable___lam__0___closed__0);
v___x_455_ = lean_int64_add(v_i_453_, v___x_454_);
v___x_456_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2);
v___x_457_ = lean_int64_dec_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_box_uint64(v___x_455_);
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = lean_box(0);
return v___x_460_;
}
}
}
LEAN_EXPORT void l_Int64_instUpwardEnumerable___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_i_453_ = stack[0].m_num;
lean_object* v_res_461_;
v_res_461_ = l_Int64_instUpwardEnumerable___lam__0(v_i_453_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l_Int64_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_462_){
_start:
{
uint64_t v_i_boxed_463_; lean_object* v_res_464_; 
v_i_boxed_463_ = lean_unbox_uint64(v_i_462_);
lean_dec_ref(v_i_462_);
v_res_464_ = l_Int64_instUpwardEnumerable___lam__0(v_i_boxed_463_);
return v_res_464_;
}
}
static lean_object* _init_l_Int64_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
uint64_t v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0);
v___x_466_ = lean_int64_to_int_sint(v___x_465_);
return v___x_466_;
}
}
lean_object* l_Int64_instUpwardEnumerable___lam__1(lean_object* v_n_467_, uint64_t v_i_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_469_ = lean_int64_to_int_sint(v_i_468_);
v___x_470_ = lean_nat_to_int(v_n_467_);
v___x_471_ = lean_int_add(v___x_469_, v___x_470_);
lean_dec(v___x_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_obj_once(&l_Int64_instUpwardEnumerable___lam__1___closed__0, &l_Int64_instUpwardEnumerable___lam__1___closed__0_once, _init_l_Int64_instUpwardEnumerable___lam__1___closed__0);
v___x_473_ = lean_int_dec_le(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
return v___x_474_;
}
else
{
uint64_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_int64_of_int(v___x_471_);
lean_dec(v___x_471_);
v___x_476_ = lean_box_uint64(v___x_475_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
}
LEAN_EXPORT void l_Int64_instUpwardEnumerable___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_467_ = stack[0].m_obj;
uint64_t v_i_468_ = stack[1].m_num;
lean_object* v_res_478_;
v_res_478_ = l_Int64_instUpwardEnumerable___lam__1(v_n_467_, v_i_468_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l_Int64_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_479_, lean_object* v_i_480_){
_start:
{
uint64_t v_i_boxed_481_; lean_object* v_res_482_; 
v_i_boxed_481_ = lean_unbox_uint64(v_i_480_);
lean_dec_ref(v_i_480_);
v_res_482_ = l_Int64_instUpwardEnumerable___lam__1(v_n_479_, v_i_boxed_481_);
return v_res_482_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1(void){
_start:
{
uint64_t v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2);
v___x_490_ = lean_box_uint64(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1;
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f(void){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0);
return v___x_493_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1(void){
_start:
{
lean_object* v___f_495_; lean_object* v___f_496_; lean_object* v___x_497_; 
v___f_495_ = lean_alloc_closure((void*)(l_UInt64_ofBitVec___boxed), 1, 0);
v___f_496_ = ((lean_object*)(l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__0));
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v___f_496_);
lean_ctor_set(v___x_497_, 1, v___f_495_);
return v___x_497_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat(void){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1);
return v___x_498_;
}
}
lean_object* l_Int64_instRxcHasSize___lam__0(uint64_t v_lo_499_, uint64_t v_hi_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_501_ = lean_int64_to_int_sint(v_hi_500_);
v___x_502_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_503_ = lean_int_add(v___x_501_, v___x_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_int64_to_int_sint(v_lo_499_);
v___x_505_ = lean_int_sub(v___x_503_, v___x_504_);
lean_dec(v___x_504_);
lean_dec(v___x_503_);
v___x_506_ = l_Int_toNat(v___x_505_);
lean_dec(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT void l_Int64_instRxcHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_lo_499_ = stack[0].m_num;
uint64_t v_hi_500_ = stack[1].m_num;
lean_object* v_res_507_;
v_res_507_ = l_Int64_instRxcHasSize___lam__0(v_lo_499_, v_hi_500_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l_Int64_instRxcHasSize___lam__0___boxed(lean_object* v_lo_508_, lean_object* v_hi_509_){
_start:
{
uint64_t v_lo_boxed_510_; uint64_t v_hi_boxed_511_; lean_object* v_res_512_; 
v_lo_boxed_510_ = lean_unbox_uint64(v_lo_508_);
lean_dec_ref(v_lo_508_);
v_hi_boxed_511_ = lean_unbox_uint64(v_hi_509_);
lean_dec_ref(v_hi_509_);
v_res_512_ = l_Int64_instRxcHasSize___lam__0(v_lo_boxed_510_, v_hi_boxed_511_);
return v_res_512_;
}
}
lean_object* l_Int64_instRxoHasSize___lam__0(uint64_t v_lo_515_, uint64_t v_hi_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_517_ = lean_int64_to_int_sint(v_hi_516_);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_520_ = lean_int_add(v___x_517_, v___x_519_);
lean_dec(v___x_517_);
v___x_521_ = lean_int64_to_int_sint(v_lo_515_);
v___x_522_ = lean_int_sub(v___x_520_, v___x_521_);
lean_dec(v___x_521_);
lean_dec(v___x_520_);
v___x_523_ = l_Int_toNat(v___x_522_);
lean_dec(v___x_522_);
v___x_524_ = lean_nat_sub(v___x_523_, v___x_518_);
lean_dec(v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT void l_Int64_instRxoHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_lo_515_ = stack[0].m_num;
uint64_t v_hi_516_ = stack[1].m_num;
lean_object* v_res_525_;
v_res_525_ = l_Int64_instRxoHasSize___lam__0(v_lo_515_, v_hi_516_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l_Int64_instRxoHasSize___lam__0___boxed(lean_object* v_lo_526_, lean_object* v_hi_527_){
_start:
{
uint64_t v_lo_boxed_528_; uint64_t v_hi_boxed_529_; lean_object* v_res_530_; 
v_lo_boxed_528_ = lean_unbox_uint64(v_lo_526_);
lean_dec_ref(v_lo_526_);
v_hi_boxed_529_ = lean_unbox_uint64(v_hi_527_);
lean_dec_ref(v_hi_527_);
v_res_530_ = l_Int64_instRxoHasSize___lam__0(v_lo_boxed_528_, v_hi_boxed_529_);
return v_res_530_;
}
}
static lean_object* _init_l_Int64_instRxiHasSize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_unsigned_to_nat(63u);
v___x_534_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__0, &l_Int8_instRxiHasSize___lam__0___closed__0_once, _init_l_Int8_instRxiHasSize___lam__0___closed__0);
v___x_535_ = l_Int_pow(v___x_534_, v___x_533_);
return v___x_535_;
}
}
lean_object* l_Int64_instRxiHasSize___lam__0(uint64_t v_lo_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = lean_obj_once(&l_Int64_instRxiHasSize___lam__0___closed__0, &l_Int64_instRxiHasSize___lam__0___closed__0_once, _init_l_Int64_instRxiHasSize___lam__0___closed__0);
v___x_538_ = lean_int64_to_int_sint(v_lo_536_);
v___x_539_ = lean_int_sub(v___x_537_, v___x_538_);
lean_dec(v___x_538_);
v___x_540_ = l_Int_toNat(v___x_539_);
lean_dec(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT void l_Int64_instRxiHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_lo_536_ = stack[0].m_num;
lean_object* v_res_541_;
v_res_541_ = l_Int64_instRxiHasSize___lam__0(v_lo_536_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l_Int64_instRxiHasSize___lam__0___boxed(lean_object* v_lo_542_){
_start:
{
uint64_t v_lo_boxed_543_; lean_object* v_res_544_; 
v_lo_boxed_543_ = lean_unbox_uint64(v_lo_542_);
lean_dec_ref(v_lo_542_);
v_res_544_ = l_Int64_instRxiHasSize___lam__0(v_lo_boxed_543_);
return v_res_544_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = l_System_Platform_numBits;
v___x_549_ = lean_nat_sub(v___x_548_, v___x_547_);
return v___x_549_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0);
v___x_551_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__0, &l_Int8_instRxiHasSize___lam__0___closed__0_once, _init_l_Int8_instRxiHasSize___lam__0___closed__0);
v___x_552_ = l_Int_pow(v___x_551_, v___x_550_);
return v___x_552_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1);
v___x_554_ = lean_int_neg(v___x_553_);
return v___x_554_;
}
}
static size_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3(void){
_start:
{
lean_object* v___x_555_; size_t v___x_556_; 
v___x_555_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2);
v___x_556_ = lean_isize_of_int(v___x_555_);
return v___x_556_;
}
}
static size_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed(void){
_start:
{
size_t v___x_557_; 
v___x_557_ = lean_usize_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3);
return v___x_557_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_559_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1);
v___x_560_ = lean_int_sub(v___x_559_, v___x_558_);
return v___x_560_;
}
}
static size_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1(void){
_start:
{
lean_object* v___x_561_; size_t v___x_562_; 
v___x_561_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0);
v___x_562_ = lean_isize_of_int(v___x_561_);
return v___x_562_;
}
}
static size_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed(void){
_start:
{
size_t v___x_563_; 
v___x_563_ = lean_usize_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1);
return v___x_563_;
}
}
static size_t _init_l_ISize_instUpwardEnumerable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_564_; size_t v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = lean_isize_of_nat(v___x_564_);
return v___x_565_;
}
}
lean_object* l_ISize_instUpwardEnumerable___lam__0(size_t v_i_566_){
_start:
{
size_t v___x_567_; size_t v___x_568_; size_t v___x_569_; uint8_t v___x_570_; 
v___x_567_ = lean_usize_once(&l_ISize_instUpwardEnumerable___lam__0___closed__0, &l_ISize_instUpwardEnumerable___lam__0___closed__0_once, _init_l_ISize_instUpwardEnumerable___lam__0___closed__0);
v___x_568_ = lean_isize_add(v_i_566_, v___x_567_);
v___x_569_ = lean_usize_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3);
v___x_570_ = lean_isize_dec_eq(v___x_568_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_box_usize(v___x_568_);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = lean_box(0);
return v___x_573_;
}
}
}
LEAN_EXPORT void l_ISize_instUpwardEnumerable___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_566_ = stack[0].m_num;
lean_object* v_res_574_;
v_res_574_ = l_ISize_instUpwardEnumerable___lam__0(v_i_566_);
stack->m_obj
 = v_res_574_;
}
LEAN_EXPORT lean_object* l_ISize_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_575_){
_start:
{
size_t v_i_boxed_576_; lean_object* v_res_577_; 
v_i_boxed_576_ = lean_unbox_usize(v_i_575_);
lean_dec(v_i_575_);
v_res_577_ = l_ISize_instUpwardEnumerable___lam__0(v_i_boxed_576_);
return v_res_577_;
}
}
static lean_object* _init_l_ISize_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
size_t v___x_578_; lean_object* v___x_579_; 
v___x_578_ = lean_usize_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1);
v___x_579_ = lean_isize_to_int(v___x_578_);
return v___x_579_;
}
}
lean_object* l_ISize_instUpwardEnumerable___lam__1(lean_object* v_n_580_, size_t v_i_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_582_ = lean_isize_to_int(v_i_581_);
v___x_583_ = lean_nat_to_int(v_n_580_);
v___x_584_ = lean_int_add(v___x_582_, v___x_583_);
lean_dec(v___x_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_obj_once(&l_ISize_instUpwardEnumerable___lam__1___closed__0, &l_ISize_instUpwardEnumerable___lam__1___closed__0_once, _init_l_ISize_instUpwardEnumerable___lam__1___closed__0);
v___x_586_ = lean_int_dec_le(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
return v___x_587_;
}
else
{
size_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_isize_of_int(v___x_584_);
lean_dec(v___x_584_);
v___x_589_ = lean_box_usize(v___x_588_);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
}
LEAN_EXPORT void l_ISize_instUpwardEnumerable___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_580_ = stack[0].m_obj;
size_t v_i_581_ = stack[1].m_num;
lean_object* v_res_591_;
v_res_591_ = l_ISize_instUpwardEnumerable___lam__1(v_n_580_, v_i_581_);
stack->m_obj
 = v_res_591_;
}
LEAN_EXPORT lean_object* l_ISize_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_592_, lean_object* v_i_593_){
_start:
{
size_t v_i_boxed_594_; lean_object* v_res_595_; 
v_i_boxed_594_ = lean_unbox_usize(v_i_593_);
lean_dec(v_i_593_);
v_res_595_ = l_ISize_instUpwardEnumerable___lam__1(v_n_592_, v_i_boxed_594_);
return v_res_595_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1(void){
_start:
{
size_t v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_usize_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3);
v___x_603_ = lean_box_usize(v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1;
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f(void){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0);
return v___x_606_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1(void){
_start:
{
lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___x_610_; 
v___f_608_ = lean_alloc_closure((void*)(l_USize_ofBitVec___boxed), 1, 0);
v___f_609_ = ((lean_object*)(l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__0));
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___f_609_);
lean_ctor_set(v___x_610_, 1, v___f_608_);
return v___x_610_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits(void){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1);
return v___x_611_;
}
}
lean_object* l_ISize_instRxcHasSize___lam__0(size_t v_lo_612_, size_t v_hi_613_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_614_ = lean_isize_to_int(v_hi_613_);
v___x_615_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_616_ = lean_int_add(v___x_614_, v___x_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_isize_to_int(v_lo_612_);
v___x_618_ = lean_int_sub(v___x_616_, v___x_617_);
lean_dec(v___x_617_);
lean_dec(v___x_616_);
v___x_619_ = l_Int_toNat(v___x_618_);
lean_dec(v___x_618_);
return v___x_619_;
}
}
LEAN_EXPORT void l_ISize_instRxcHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_lo_612_ = stack[0].m_num;
size_t v_hi_613_ = stack[1].m_num;
lean_object* v_res_620_;
v_res_620_ = l_ISize_instRxcHasSize___lam__0(v_lo_612_, v_hi_613_);
stack->m_obj
 = v_res_620_;
}
LEAN_EXPORT lean_object* l_ISize_instRxcHasSize___lam__0___boxed(lean_object* v_lo_621_, lean_object* v_hi_622_){
_start:
{
size_t v_lo_boxed_623_; size_t v_hi_boxed_624_; lean_object* v_res_625_; 
v_lo_boxed_623_ = lean_unbox_usize(v_lo_621_);
lean_dec(v_lo_621_);
v_hi_boxed_624_ = lean_unbox_usize(v_hi_622_);
lean_dec(v_hi_622_);
v_res_625_ = l_ISize_instRxcHasSize___lam__0(v_lo_boxed_623_, v_hi_boxed_624_);
return v_res_625_;
}
}
lean_object* l_ISize_instRxoHasSize___lam__0(size_t v_lo_628_, size_t v_hi_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_630_ = lean_isize_to_int(v_hi_629_);
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_633_ = lean_int_add(v___x_630_, v___x_632_);
lean_dec(v___x_630_);
v___x_634_ = lean_isize_to_int(v_lo_628_);
v___x_635_ = lean_int_sub(v___x_633_, v___x_634_);
lean_dec(v___x_634_);
lean_dec(v___x_633_);
v___x_636_ = l_Int_toNat(v___x_635_);
lean_dec(v___x_635_);
v___x_637_ = lean_nat_sub(v___x_636_, v___x_631_);
lean_dec(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT void l_ISize_instRxoHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_lo_628_ = stack[0].m_num;
size_t v_hi_629_ = stack[1].m_num;
lean_object* v_res_638_;
v_res_638_ = l_ISize_instRxoHasSize___lam__0(v_lo_628_, v_hi_629_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l_ISize_instRxoHasSize___lam__0___boxed(lean_object* v_lo_639_, lean_object* v_hi_640_){
_start:
{
size_t v_lo_boxed_641_; size_t v_hi_boxed_642_; lean_object* v_res_643_; 
v_lo_boxed_641_ = lean_unbox_usize(v_lo_639_);
lean_dec(v_lo_639_);
v_hi_boxed_642_ = lean_unbox_usize(v_hi_640_);
lean_dec(v_hi_640_);
v_res_643_ = l_ISize_instRxoHasSize___lam__0(v_lo_boxed_641_, v_hi_boxed_642_);
return v_res_643_;
}
}
lean_object* l_ISize_instRxiHasSize___lam__0(size_t v_lo_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_647_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1);
v___x_648_ = lean_isize_to_int(v_lo_646_);
v___x_649_ = lean_int_sub(v___x_647_, v___x_648_);
lean_dec(v___x_648_);
v___x_650_ = l_Int_toNat(v___x_649_);
lean_dec(v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT void l_ISize_instRxiHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_lo_646_ = stack[0].m_num;
lean_object* v_res_651_;
v_res_651_ = l_ISize_instRxiHasSize___lam__0(v_lo_646_);
stack->m_obj
 = v_res_651_;
}
LEAN_EXPORT lean_object* l_ISize_instRxiHasSize___lam__0___boxed(lean_object* v_lo_652_){
_start:
{
size_t v_lo_boxed_653_; lean_object* v_res_654_; 
v_lo_boxed_653_ = lean_unbox_usize(v_lo_652_);
lean_dec(v_lo_652_);
v_res_654_ = l_ISize_instRxiHasSize___lam__0(v_lo_boxed_653_);
return v_res_654_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_SInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed();
l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed();
l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f);
l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat);
l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed();
l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed();
l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f);
l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat);
l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed();
l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed();
l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1 = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1);
l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f);
l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat);
l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed();
l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed();
l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1 = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1);
l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f);
l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat);
l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed();
l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed();
l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1 = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1);
l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f);
l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits = _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits();
lean_mark_persistent(l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_SInt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_SInt(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_SInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_SInt(builtin);
}
#ifdef __cplusplus
}
#endif
