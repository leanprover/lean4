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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0(uint8_t v_lo_57_, uint8_t v_hi_58_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___boxed(lean_object* v_lo_65_, lean_object* v_hi_66_){
_start:
{
uint8_t v_lo_boxed_67_; uint8_t v_hi_boxed_68_; lean_object* v_res_69_; 
v_lo_boxed_67_ = lean_unbox(v_lo_65_);
v_hi_boxed_68_ = lean_unbox(v_hi_66_);
v_res_69_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0(v_lo_boxed_67_, v_hi_boxed_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg___lam__0(lean_object* v_m_72_, lean_object* v_inst_73_, lean_object* v_lo_74_, lean_object* v_hi_75_){
_start:
{
lean_object* v_encode_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_encode_76_ = lean_ctor_get(v_m_72_, 0);
lean_inc(v_encode_76_);
lean_dec_ref(v_m_72_);
lean_inc(v_encode_76_);
v___x_77_ = lean_apply_1(v_encode_76_, v_lo_74_);
v___x_78_ = lean_apply_1(v_encode_76_, v_hi_75_);
v___x_79_ = lean_apply_2(v_inst_73_, v___x_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg(lean_object* v_m_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v___f_82_; 
v___f_82_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg___lam__0), 4, 2);
lean_closure_set(v___f_82_, 0, v_m_80_);
lean_closure_set(v___f_82_, 1, v_inst_81_);
return v___f_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize(lean_object* v_00_u03b1_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_00_u03b2_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_m_93_, lean_object* v_inst_94_){
_start:
{
lean_object* v___f_95_; 
v___f_95_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___redArg___lam__0), 4, 2);
lean_closure_set(v___f_95_, 0, v_m_93_);
lean_closure_set(v___f_95_, 1, v_inst_94_);
return v___f_95_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize___boxed(lean_object* v_00_u03b1_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_00_u03b2_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_m_106_, lean_object* v_inst_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxcHasSize(v_00_u03b1_96_, v_inst_97_, v_inst_98_, v_00_u03b2_99_, v_inst_100_, v_inst_101_, v_inst_102_, v_inst_103_, v_inst_104_, v_inst_105_, v_m_106_, v_inst_107_);
lean_dec_ref(v_inst_102_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg___lam__0(lean_object* v_m_109_, lean_object* v_inst_110_, lean_object* v_lo_111_){
_start:
{
lean_object* v_encode_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_encode_112_ = lean_ctor_get(v_m_109_, 0);
lean_inc(v_encode_112_);
lean_dec_ref(v_m_109_);
v___x_113_ = lean_apply_1(v_encode_112_, v_lo_111_);
v___x_114_ = lean_apply_1(v_inst_110_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg(lean_object* v_m_115_, lean_object* v_inst_116_){
_start:
{
lean_object* v___f_117_; 
v___f_117_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg___lam__0), 3, 2);
lean_closure_set(v___f_117_, 0, v_m_115_);
lean_closure_set(v___f_117_, 1, v_inst_116_);
return v___f_117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize(lean_object* v_00_u03b1_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_00_u03b2_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_m_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v___f_130_; 
v___f_130_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___redArg___lam__0), 3, 2);
lean_closure_set(v___f_130_, 0, v_m_128_);
lean_closure_set(v___f_130_, 1, v_inst_129_);
return v___f_130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize___boxed(lean_object* v_00_u03b1_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_00_u03b2_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_m_141_, lean_object* v_inst_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instRxiHasSize(v_00_u03b1_131_, v_inst_132_, v_inst_133_, v_00_u03b2_134_, v_inst_135_, v_inst_136_, v_inst_137_, v_inst_138_, v_inst_139_, v_inst_140_, v_m_141_, v_inst_142_);
lean_dec_ref(v_inst_137_);
return v_res_143_;
}
}
static uint8_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0(void){
_start:
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(128u);
v___x_145_ = lean_int8_of_nat(v___x_144_);
return v___x_145_;
}
}
static uint8_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1(void){
_start:
{
uint8_t v___x_146_; uint8_t v___x_147_; 
v___x_146_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__0);
v___x_147_ = lean_int8_neg(v___x_146_);
return v___x_147_;
}
}
static uint8_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed(void){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1);
return v___x_148_;
}
}
static uint8_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0(void){
_start:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(127u);
v___x_150_ = lean_int8_of_nat(v___x_149_);
return v___x_150_;
}
}
static uint8_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed(void){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0);
return v___x_151_;
}
}
static uint8_t _init_l_Int8_instUpwardEnumerable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_int8_of_nat(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Int8_instUpwardEnumerable___lam__0(uint8_t v_i_154_){
_start:
{
uint8_t v___x_155_; uint8_t v___x_156_; uint8_t v___x_157_; uint8_t v___x_158_; 
v___x_155_ = lean_uint8_once(&l_Int8_instUpwardEnumerable___lam__0___closed__0, &l_Int8_instUpwardEnumerable___lam__0___closed__0_once, _init_l_Int8_instUpwardEnumerable___lam__0___closed__0);
v___x_156_ = lean_int8_add(v_i_154_, v___x_155_);
v___x_157_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1);
v___x_158_ = lean_int8_dec_eq(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_box(v___x_156_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(0);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l_Int8_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_162_){
_start:
{
uint8_t v_i_boxed_163_; lean_object* v_res_164_; 
v_i_boxed_163_ = lean_unbox(v_i_162_);
v_res_164_ = l_Int8_instUpwardEnumerable___lam__0(v_i_boxed_163_);
return v_res_164_;
}
}
static lean_object* _init_l_Int8_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
uint8_t v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_maxValueSealed___closed__0);
v___x_166_ = lean_int8_to_int(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Int8_instUpwardEnumerable___lam__1(lean_object* v_n_167_, uint8_t v_i_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_169_ = lean_int8_to_int(v_i_168_);
v___x_170_ = lean_nat_to_int(v_n_167_);
v___x_171_ = lean_int_add(v___x_169_, v___x_170_);
lean_dec(v___x_170_);
v___x_172_ = lean_obj_once(&l_Int8_instUpwardEnumerable___lam__1___closed__0, &l_Int8_instUpwardEnumerable___lam__1___closed__0_once, _init_l_Int8_instUpwardEnumerable___lam__1___closed__0);
v___x_173_ = lean_int_dec_le(v___x_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
return v___x_174_;
}
else
{
uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_int8_of_int(v___x_171_);
lean_dec(v___x_171_);
v___x_176_ = lean_box(v___x_175_);
v___x_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Int8_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_178_, lean_object* v_i_179_){
_start:
{
uint8_t v_i_boxed_180_; lean_object* v_res_181_; 
v_i_boxed_180_ = lean_unbox(v_i_179_);
v_res_181_ = l_Int8_instUpwardEnumerable___lam__1(v_n_178_, v_i_boxed_180_);
return v_res_181_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0(void){
_start:
{
uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_uint8_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_minValueSealed___closed__1);
v___x_189_ = lean_box(v___x_188_);
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instLeast_x3f___closed__0);
return v___x_191_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1(void){
_start:
{
lean_object* v___f_193_; lean_object* v___f_194_; lean_object* v___x_195_; 
v___f_193_ = lean_alloc_closure((void*)(l_UInt8_ofBitVec___boxed), 1, 0);
v___f_194_ = ((lean_object*)(l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__0));
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___f_194_);
lean_ctor_set(v___x_195_, 1, v___f_193_);
return v___x_195_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat(void){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int8_instHasModelBitVecOfNatNat___closed__1);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Int8_instRxoHasSize___lam__0(uint8_t v_lo_198_, uint8_t v_hi_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_200_ = lean_int8_to_int(v_hi_199_);
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_203_ = lean_int_add(v___x_200_, v___x_202_);
v___x_204_ = lean_int8_to_int(v_lo_198_);
v___x_205_ = lean_int_sub(v___x_203_, v___x_204_);
lean_dec(v___x_203_);
v___x_206_ = l_Int_toNat(v___x_205_);
lean_dec(v___x_205_);
v___x_207_ = lean_nat_sub(v___x_206_, v___x_201_);
lean_dec(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Int8_instRxoHasSize___lam__0___boxed(lean_object* v_lo_208_, lean_object* v_hi_209_){
_start:
{
uint8_t v_lo_boxed_210_; uint8_t v_hi_boxed_211_; lean_object* v_res_212_; 
v_lo_boxed_210_ = lean_unbox(v_lo_208_);
v_hi_boxed_211_ = lean_unbox(v_hi_209_);
v_res_212_ = l_Int8_instRxoHasSize___lam__0(v_lo_boxed_210_, v_hi_boxed_211_);
return v_res_212_;
}
}
static lean_object* _init_l_Int8_instRxiHasSize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(2u);
v___x_216_ = lean_nat_to_int(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Int8_instRxiHasSize___lam__0___closed__1(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_unsigned_to_nat(7u);
v___x_218_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__0, &l_Int8_instRxiHasSize___lam__0___closed__0_once, _init_l_Int8_instRxiHasSize___lam__0___closed__0);
v___x_219_ = l_Int_pow(v___x_218_, v___x_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Int8_instRxiHasSize___lam__0(uint8_t v_lo_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_221_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__1, &l_Int8_instRxiHasSize___lam__0___closed__1_once, _init_l_Int8_instRxiHasSize___lam__0___closed__1);
v___x_222_ = lean_int8_to_int(v_lo_220_);
v___x_223_ = lean_int_sub(v___x_221_, v___x_222_);
v___x_224_ = l_Int_toNat(v___x_223_);
lean_dec(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Int8_instRxiHasSize___lam__0___boxed(lean_object* v_lo_225_){
_start:
{
uint8_t v_lo_boxed_226_; lean_object* v_res_227_; 
v_lo_boxed_226_ = lean_unbox(v_lo_225_);
v_res_227_ = l_Int8_instRxiHasSize___lam__0(v_lo_boxed_226_);
return v_res_227_;
}
}
static uint16_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0(void){
_start:
{
lean_object* v___x_230_; uint16_t v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(32768u);
v___x_231_ = lean_int16_of_nat(v___x_230_);
return v___x_231_;
}
}
static uint16_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1(void){
_start:
{
uint16_t v___x_232_; uint16_t v___x_233_; 
v___x_232_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__0);
v___x_233_ = lean_int16_neg(v___x_232_);
return v___x_233_;
}
}
static uint16_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed(void){
_start:
{
uint16_t v___x_234_; 
v___x_234_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1);
return v___x_234_;
}
}
static uint16_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0(void){
_start:
{
lean_object* v___x_235_; uint16_t v___x_236_; 
v___x_235_ = lean_unsigned_to_nat(32767u);
v___x_236_ = lean_int16_of_nat(v___x_235_);
return v___x_236_;
}
}
static uint16_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed(void){
_start:
{
uint16_t v___x_237_; 
v___x_237_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0);
return v___x_237_;
}
}
static uint16_t _init_l_Int16_instUpwardEnumerable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_238_; uint16_t v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_int16_of_nat(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Int16_instUpwardEnumerable___lam__0(uint16_t v_i_240_){
_start:
{
uint16_t v___x_241_; uint16_t v___x_242_; uint16_t v___x_243_; uint8_t v___x_244_; 
v___x_241_ = lean_uint16_once(&l_Int16_instUpwardEnumerable___lam__0___closed__0, &l_Int16_instUpwardEnumerable___lam__0___closed__0_once, _init_l_Int16_instUpwardEnumerable___lam__0___closed__0);
v___x_242_ = lean_int16_add(v_i_240_, v___x_241_);
v___x_243_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1);
v___x_244_ = lean_int16_dec_eq(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_box(v___x_242_);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = lean_box(0);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Int16_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_248_){
_start:
{
uint16_t v_i_boxed_249_; lean_object* v_res_250_; 
v_i_boxed_249_ = lean_unbox(v_i_248_);
v_res_250_ = l_Int16_instUpwardEnumerable___lam__0(v_i_boxed_249_);
return v_res_250_;
}
}
static lean_object* _init_l_Int16_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
uint16_t v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_maxValueSealed___closed__0);
v___x_252_ = lean_int16_to_int(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Int16_instUpwardEnumerable___lam__1(lean_object* v_n_253_, uint16_t v_i_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_255_ = lean_int16_to_int(v_i_254_);
v___x_256_ = lean_nat_to_int(v_n_253_);
v___x_257_ = lean_int_add(v___x_255_, v___x_256_);
lean_dec(v___x_256_);
v___x_258_ = lean_obj_once(&l_Int16_instUpwardEnumerable___lam__1___closed__0, &l_Int16_instUpwardEnumerable___lam__1___closed__0_once, _init_l_Int16_instUpwardEnumerable___lam__1___closed__0);
v___x_259_ = lean_int_dec_le(v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
else
{
uint16_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_int16_of_int(v___x_257_);
lean_dec(v___x_257_);
v___x_262_ = lean_box(v___x_261_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Int16_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_264_, lean_object* v_i_265_){
_start:
{
uint16_t v_i_boxed_266_; lean_object* v_res_267_; 
v_i_boxed_266_ = lean_unbox(v_i_265_);
v_res_267_ = l_Int16_instUpwardEnumerable___lam__1(v_n_264_, v_i_boxed_266_);
return v_res_267_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0(void){
_start:
{
uint16_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_uint16_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_minValueSealed___closed__1);
v___x_275_ = lean_box(v___x_274_);
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instLeast_x3f___closed__0);
return v___x_277_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1(void){
_start:
{
lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___x_281_; 
v___f_279_ = lean_alloc_closure((void*)(l_UInt16_ofBitVec___boxed), 1, 0);
v___f_280_ = ((lean_object*)(l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__0));
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___f_280_);
lean_ctor_set(v___x_281_, 1, v___f_279_);
return v___x_281_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int16_instHasModelBitVecOfNatNat___closed__1);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Int16_instRxcHasSize___lam__0(uint16_t v_lo_283_, uint16_t v_hi_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_285_ = lean_int16_to_int(v_hi_284_);
v___x_286_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_287_ = lean_int_add(v___x_285_, v___x_286_);
v___x_288_ = lean_int16_to_int(v_lo_283_);
v___x_289_ = lean_int_sub(v___x_287_, v___x_288_);
lean_dec(v___x_287_);
v___x_290_ = l_Int_toNat(v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Int16_instRxcHasSize___lam__0___boxed(lean_object* v_lo_291_, lean_object* v_hi_292_){
_start:
{
uint16_t v_lo_boxed_293_; uint16_t v_hi_boxed_294_; lean_object* v_res_295_; 
v_lo_boxed_293_ = lean_unbox(v_lo_291_);
v_hi_boxed_294_ = lean_unbox(v_hi_292_);
v_res_295_ = l_Int16_instRxcHasSize___lam__0(v_lo_boxed_293_, v_hi_boxed_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Int16_instRxoHasSize___lam__0(uint16_t v_lo_298_, uint16_t v_hi_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_300_ = lean_int16_to_int(v_hi_299_);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_303_ = lean_int_add(v___x_300_, v___x_302_);
v___x_304_ = lean_int16_to_int(v_lo_298_);
v___x_305_ = lean_int_sub(v___x_303_, v___x_304_);
lean_dec(v___x_303_);
v___x_306_ = l_Int_toNat(v___x_305_);
lean_dec(v___x_305_);
v___x_307_ = lean_nat_sub(v___x_306_, v___x_301_);
lean_dec(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Int16_instRxoHasSize___lam__0___boxed(lean_object* v_lo_308_, lean_object* v_hi_309_){
_start:
{
uint16_t v_lo_boxed_310_; uint16_t v_hi_boxed_311_; lean_object* v_res_312_; 
v_lo_boxed_310_ = lean_unbox(v_lo_308_);
v_hi_boxed_311_ = lean_unbox(v_hi_309_);
v_res_312_ = l_Int16_instRxoHasSize___lam__0(v_lo_boxed_310_, v_hi_boxed_311_);
return v_res_312_;
}
}
static lean_object* _init_l_Int16_instRxiHasSize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_unsigned_to_nat(15u);
v___x_316_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__0, &l_Int8_instRxiHasSize___lam__0___closed__0_once, _init_l_Int8_instRxiHasSize___lam__0___closed__0);
v___x_317_ = l_Int_pow(v___x_316_, v___x_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Int16_instRxiHasSize___lam__0(uint16_t v_lo_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_obj_once(&l_Int16_instRxiHasSize___lam__0___closed__0, &l_Int16_instRxiHasSize___lam__0___closed__0_once, _init_l_Int16_instRxiHasSize___lam__0___closed__0);
v___x_320_ = lean_int16_to_int(v_lo_318_);
v___x_321_ = lean_int_sub(v___x_319_, v___x_320_);
v___x_322_ = l_Int_toNat(v___x_321_);
lean_dec(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Int16_instRxiHasSize___lam__0___boxed(lean_object* v_lo_323_){
_start:
{
uint16_t v_lo_boxed_324_; lean_object* v_res_325_; 
v_lo_boxed_324_ = lean_unbox(v_lo_323_);
v_res_325_ = l_Int16_instRxiHasSize___lam__0(v_lo_boxed_324_);
return v_res_325_;
}
}
static uint32_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0(void){
_start:
{
lean_object* v___x_328_; uint32_t v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(2147483648u);
v___x_329_ = lean_int32_of_nat(v___x_328_);
return v___x_329_;
}
}
static uint32_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1(void){
_start:
{
uint32_t v___x_330_; uint32_t v___x_331_; 
v___x_330_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__0);
v___x_331_ = lean_int32_neg(v___x_330_);
return v___x_331_;
}
}
static uint32_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed(void){
_start:
{
uint32_t v___x_332_; 
v___x_332_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1);
return v___x_332_;
}
}
static uint32_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0(void){
_start:
{
lean_object* v___x_333_; uint32_t v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(2147483647u);
v___x_334_ = lean_int32_of_nat(v___x_333_);
return v___x_334_;
}
}
static uint32_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed(void){
_start:
{
uint32_t v___x_335_; 
v___x_335_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0);
return v___x_335_;
}
}
static uint32_t _init_l_Int32_instUpwardEnumerable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_336_; uint32_t v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_int32_of_nat(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Int32_instUpwardEnumerable___lam__0(uint32_t v_i_338_){
_start:
{
uint32_t v___x_339_; uint32_t v___x_340_; uint32_t v___x_341_; uint8_t v___x_342_; 
v___x_339_ = lean_uint32_once(&l_Int32_instUpwardEnumerable___lam__0___closed__0, &l_Int32_instUpwardEnumerable___lam__0___closed__0_once, _init_l_Int32_instUpwardEnumerable___lam__0___closed__0);
v___x_340_ = lean_int32_add(v_i_338_, v___x_339_);
v___x_341_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1);
v___x_342_ = lean_int32_dec_eq(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_box_uint32(v___x_340_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Int32_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_346_){
_start:
{
uint32_t v_i_boxed_347_; lean_object* v_res_348_; 
v_i_boxed_347_ = lean_unbox_uint32(v_i_346_);
lean_dec(v_i_346_);
v_res_348_ = l_Int32_instUpwardEnumerable___lam__0(v_i_boxed_347_);
return v_res_348_;
}
}
static lean_object* _init_l_Int32_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
uint32_t v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_maxValueSealed___closed__0);
v___x_350_ = lean_int32_to_int(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Int32_instUpwardEnumerable___lam__1(lean_object* v_n_351_, uint32_t v_i_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_353_ = lean_int32_to_int(v_i_352_);
v___x_354_ = lean_nat_to_int(v_n_351_);
v___x_355_ = lean_int_add(v___x_353_, v___x_354_);
lean_dec(v___x_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_obj_once(&l_Int32_instUpwardEnumerable___lam__1___closed__0, &l_Int32_instUpwardEnumerable___lam__1___closed__0_once, _init_l_Int32_instUpwardEnumerable___lam__1___closed__0);
v___x_357_ = lean_int_dec_le(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
return v___x_358_;
}
else
{
uint32_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_int32_of_int(v___x_355_);
lean_dec(v___x_355_);
v___x_360_ = lean_box_uint32(v___x_359_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Int32_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_362_, lean_object* v_i_363_){
_start:
{
uint32_t v_i_boxed_364_; lean_object* v_res_365_; 
v_i_boxed_364_ = lean_unbox_uint32(v_i_363_);
lean_dec(v_i_363_);
v_res_365_ = l_Int32_instUpwardEnumerable___lam__1(v_n_362_, v_i_boxed_364_);
return v_res_365_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_uint32_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_minValueSealed___closed__1);
v___x_373_ = lean_box_uint32(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0___boxed__const__1;
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instLeast_x3f___closed__0);
return v___x_376_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1(void){
_start:
{
lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___x_380_; 
v___f_378_ = lean_alloc_closure((void*)(l_UInt32_ofBitVec___boxed), 1, 0);
v___f_379_ = ((lean_object*)(l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__0));
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___f_379_);
lean_ctor_set(v___x_380_, 1, v___f_378_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int32_instHasModelBitVecOfNatNat___closed__1);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Int32_instRxcHasSize___lam__0(uint32_t v_lo_382_, uint32_t v_hi_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_384_ = lean_int32_to_int(v_hi_383_);
v___x_385_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_386_ = lean_int_add(v___x_384_, v___x_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_int32_to_int(v_lo_382_);
v___x_388_ = lean_int_sub(v___x_386_, v___x_387_);
lean_dec(v___x_387_);
lean_dec(v___x_386_);
v___x_389_ = l_Int_toNat(v___x_388_);
lean_dec(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Int32_instRxcHasSize___lam__0___boxed(lean_object* v_lo_390_, lean_object* v_hi_391_){
_start:
{
uint32_t v_lo_boxed_392_; uint32_t v_hi_boxed_393_; lean_object* v_res_394_; 
v_lo_boxed_392_ = lean_unbox_uint32(v_lo_390_);
lean_dec(v_lo_390_);
v_hi_boxed_393_ = lean_unbox_uint32(v_hi_391_);
lean_dec(v_hi_391_);
v_res_394_ = l_Int32_instRxcHasSize___lam__0(v_lo_boxed_392_, v_hi_boxed_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Int32_instRxoHasSize___lam__0(uint32_t v_lo_397_, uint32_t v_hi_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_399_ = lean_int32_to_int(v_hi_398_);
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_402_ = lean_int_add(v___x_399_, v___x_401_);
lean_dec(v___x_399_);
v___x_403_ = lean_int32_to_int(v_lo_397_);
v___x_404_ = lean_int_sub(v___x_402_, v___x_403_);
lean_dec(v___x_403_);
lean_dec(v___x_402_);
v___x_405_ = l_Int_toNat(v___x_404_);
lean_dec(v___x_404_);
v___x_406_ = lean_nat_sub(v___x_405_, v___x_400_);
lean_dec(v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Int32_instRxoHasSize___lam__0___boxed(lean_object* v_lo_407_, lean_object* v_hi_408_){
_start:
{
uint32_t v_lo_boxed_409_; uint32_t v_hi_boxed_410_; lean_object* v_res_411_; 
v_lo_boxed_409_ = lean_unbox_uint32(v_lo_407_);
lean_dec(v_lo_407_);
v_hi_boxed_410_ = lean_unbox_uint32(v_hi_408_);
lean_dec(v_hi_408_);
v_res_411_ = l_Int32_instRxoHasSize___lam__0(v_lo_boxed_409_, v_hi_boxed_410_);
return v_res_411_;
}
}
static lean_object* _init_l_Int32_instRxiHasSize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_unsigned_to_nat(31u);
v___x_415_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__0, &l_Int8_instRxiHasSize___lam__0___closed__0_once, _init_l_Int8_instRxiHasSize___lam__0___closed__0);
v___x_416_ = l_Int_pow(v___x_415_, v___x_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Int32_instRxiHasSize___lam__0(uint32_t v_lo_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = lean_obj_once(&l_Int32_instRxiHasSize___lam__0___closed__0, &l_Int32_instRxiHasSize___lam__0___closed__0_once, _init_l_Int32_instRxiHasSize___lam__0___closed__0);
v___x_419_ = lean_int32_to_int(v_lo_417_);
v___x_420_ = lean_int_sub(v___x_418_, v___x_419_);
lean_dec(v___x_419_);
v___x_421_ = l_Int_toNat(v___x_420_);
lean_dec(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Int32_instRxiHasSize___lam__0___boxed(lean_object* v_lo_422_){
_start:
{
uint32_t v_lo_boxed_423_; lean_object* v_res_424_; 
v_lo_boxed_423_ = lean_unbox_uint32(v_lo_422_);
lean_dec(v_lo_422_);
v_res_424_ = l_Int32_instRxiHasSize___lam__0(v_lo_boxed_423_);
return v_res_424_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0(void){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = lean_cstr_to_nat("9223372036854775808");
return v___x_427_;
}
}
static uint64_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1(void){
_start:
{
lean_object* v___x_428_; uint64_t v___x_429_; 
v___x_428_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__0);
v___x_429_ = lean_int64_of_nat(v___x_428_);
return v___x_429_;
}
}
static uint64_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2(void){
_start:
{
uint64_t v___x_430_; uint64_t v___x_431_; 
v___x_430_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__1);
v___x_431_ = lean_int64_neg(v___x_430_);
return v___x_431_;
}
}
static uint64_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed(void){
_start:
{
uint64_t v___x_432_; 
v___x_432_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2);
return v___x_432_;
}
}
static uint64_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0(void){
_start:
{
lean_object* v___x_433_; uint64_t v___x_434_; 
v___x_433_ = lean_cstr_to_nat("9223372036854775807");
v___x_434_ = lean_int64_of_nat(v___x_433_);
return v___x_434_;
}
}
static uint64_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed(void){
_start:
{
uint64_t v___x_435_; 
v___x_435_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0);
return v___x_435_;
}
}
static uint64_t _init_l_Int64_instUpwardEnumerable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_436_; uint64_t v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_int64_of_nat(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Int64_instUpwardEnumerable___lam__0(uint64_t v_i_438_){
_start:
{
uint64_t v___x_439_; uint64_t v___x_440_; uint64_t v___x_441_; uint8_t v___x_442_; 
v___x_439_ = lean_uint64_once(&l_Int64_instUpwardEnumerable___lam__0___closed__0, &l_Int64_instUpwardEnumerable___lam__0___closed__0_once, _init_l_Int64_instUpwardEnumerable___lam__0___closed__0);
v___x_440_ = lean_int64_add(v_i_438_, v___x_439_);
v___x_441_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2);
v___x_442_ = lean_int64_dec_eq(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_box_uint64(v___x_440_);
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
else
{
lean_object* v___x_445_; 
v___x_445_ = lean_box(0);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Int64_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_446_){
_start:
{
uint64_t v_i_boxed_447_; lean_object* v_res_448_; 
v_i_boxed_447_ = lean_unbox_uint64(v_i_446_);
lean_dec_ref(v_i_446_);
v_res_448_ = l_Int64_instUpwardEnumerable___lam__0(v_i_boxed_447_);
return v_res_448_;
}
}
static lean_object* _init_l_Int64_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
uint64_t v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_maxValueSealed___closed__0);
v___x_450_ = lean_int64_to_int_sint(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Int64_instUpwardEnumerable___lam__1(lean_object* v_n_451_, uint64_t v_i_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_453_ = lean_int64_to_int_sint(v_i_452_);
v___x_454_ = lean_nat_to_int(v_n_451_);
v___x_455_ = lean_int_add(v___x_453_, v___x_454_);
lean_dec(v___x_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_obj_once(&l_Int64_instUpwardEnumerable___lam__1___closed__0, &l_Int64_instUpwardEnumerable___lam__1___closed__0_once, _init_l_Int64_instUpwardEnumerable___lam__1___closed__0);
v___x_457_ = lean_int_dec_le(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
return v___x_458_;
}
else
{
uint64_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_int64_of_int(v___x_455_);
lean_dec(v___x_455_);
v___x_460_ = lean_box_uint64(v___x_459_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Int64_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_462_, lean_object* v_i_463_){
_start:
{
uint64_t v_i_boxed_464_; lean_object* v_res_465_; 
v_i_boxed_464_ = lean_unbox_uint64(v_i_463_);
lean_dec_ref(v_i_463_);
v_res_465_ = l_Int64_instUpwardEnumerable___lam__1(v_n_462_, v_i_boxed_464_);
return v_res_465_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1(void){
_start:
{
uint64_t v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_uint64_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_minValueSealed___closed__2);
v___x_473_ = lean_box_uint64(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0___boxed__const__1;
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instLeast_x3f___closed__0);
return v___x_476_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1(void){
_start:
{
lean_object* v___f_478_; lean_object* v___f_479_; lean_object* v___x_480_; 
v___f_478_ = lean_alloc_closure((void*)(l_UInt64_ofBitVec___boxed), 1, 0);
v___f_479_ = ((lean_object*)(l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__0));
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___f_479_);
lean_ctor_set(v___x_480_, 1, v___f_478_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat(void){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__Int64_instHasModelBitVecOfNatNat___closed__1);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Int64_instRxcHasSize___lam__0(uint64_t v_lo_482_, uint64_t v_hi_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_484_ = lean_int64_to_int_sint(v_hi_483_);
v___x_485_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_486_ = lean_int_add(v___x_484_, v___x_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_int64_to_int_sint(v_lo_482_);
v___x_488_ = lean_int_sub(v___x_486_, v___x_487_);
lean_dec(v___x_487_);
lean_dec(v___x_486_);
v___x_489_ = l_Int_toNat(v___x_488_);
lean_dec(v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Int64_instRxcHasSize___lam__0___boxed(lean_object* v_lo_490_, lean_object* v_hi_491_){
_start:
{
uint64_t v_lo_boxed_492_; uint64_t v_hi_boxed_493_; lean_object* v_res_494_; 
v_lo_boxed_492_ = lean_unbox_uint64(v_lo_490_);
lean_dec_ref(v_lo_490_);
v_hi_boxed_493_ = lean_unbox_uint64(v_hi_491_);
lean_dec_ref(v_hi_491_);
v_res_494_ = l_Int64_instRxcHasSize___lam__0(v_lo_boxed_492_, v_hi_boxed_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Int64_instRxoHasSize___lam__0(uint64_t v_lo_497_, uint64_t v_hi_498_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_499_ = lean_int64_to_int_sint(v_hi_498_);
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_502_ = lean_int_add(v___x_499_, v___x_501_);
lean_dec(v___x_499_);
v___x_503_ = lean_int64_to_int_sint(v_lo_497_);
v___x_504_ = lean_int_sub(v___x_502_, v___x_503_);
lean_dec(v___x_503_);
lean_dec(v___x_502_);
v___x_505_ = l_Int_toNat(v___x_504_);
lean_dec(v___x_504_);
v___x_506_ = lean_nat_sub(v___x_505_, v___x_500_);
lean_dec(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Int64_instRxoHasSize___lam__0___boxed(lean_object* v_lo_507_, lean_object* v_hi_508_){
_start:
{
uint64_t v_lo_boxed_509_; uint64_t v_hi_boxed_510_; lean_object* v_res_511_; 
v_lo_boxed_509_ = lean_unbox_uint64(v_lo_507_);
lean_dec_ref(v_lo_507_);
v_hi_boxed_510_ = lean_unbox_uint64(v_hi_508_);
lean_dec_ref(v_hi_508_);
v_res_511_ = l_Int64_instRxoHasSize___lam__0(v_lo_boxed_509_, v_hi_boxed_510_);
return v_res_511_;
}
}
static lean_object* _init_l_Int64_instRxiHasSize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_unsigned_to_nat(63u);
v___x_515_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__0, &l_Int8_instRxiHasSize___lam__0___closed__0_once, _init_l_Int8_instRxiHasSize___lam__0___closed__0);
v___x_516_ = l_Int_pow(v___x_515_, v___x_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Int64_instRxiHasSize___lam__0(uint64_t v_lo_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = lean_obj_once(&l_Int64_instRxiHasSize___lam__0___closed__0, &l_Int64_instRxiHasSize___lam__0___closed__0_once, _init_l_Int64_instRxiHasSize___lam__0___closed__0);
v___x_519_ = lean_int64_to_int_sint(v_lo_517_);
v___x_520_ = lean_int_sub(v___x_518_, v___x_519_);
lean_dec(v___x_519_);
v___x_521_ = l_Int_toNat(v___x_520_);
lean_dec(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Int64_instRxiHasSize___lam__0___boxed(lean_object* v_lo_522_){
_start:
{
uint64_t v_lo_boxed_523_; lean_object* v_res_524_; 
v_lo_boxed_523_ = lean_unbox_uint64(v_lo_522_);
lean_dec_ref(v_lo_522_);
v_res_524_ = l_Int64_instRxiHasSize___lam__0(v_lo_boxed_523_);
return v_res_524_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = l_System_Platform_numBits;
v___x_529_ = lean_nat_sub(v___x_528_, v___x_527_);
return v___x_529_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__0);
v___x_531_ = lean_obj_once(&l_Int8_instRxiHasSize___lam__0___closed__0, &l_Int8_instRxiHasSize___lam__0___closed__0_once, _init_l_Int8_instRxiHasSize___lam__0___closed__0);
v___x_532_ = l_Int_pow(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1);
v___x_534_ = lean_int_neg(v___x_533_);
return v___x_534_;
}
}
static size_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3(void){
_start:
{
lean_object* v___x_535_; size_t v___x_536_; 
v___x_535_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__2);
v___x_536_ = lean_isize_of_int(v___x_535_);
return v___x_536_;
}
}
static size_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed(void){
_start:
{
size_t v___x_537_; 
v___x_537_ = lean_usize_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3);
return v___x_537_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_539_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1);
v___x_540_ = lean_int_sub(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static size_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1(void){
_start:
{
lean_object* v___x_541_; size_t v___x_542_; 
v___x_541_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__0);
v___x_542_ = lean_isize_of_int(v___x_541_);
return v___x_542_;
}
}
static size_t _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed(void){
_start:
{
size_t v___x_543_; 
v___x_543_ = lean_usize_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1);
return v___x_543_;
}
}
static size_t _init_l_ISize_instUpwardEnumerable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_544_; size_t v___x_545_; 
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_isize_of_nat(v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_ISize_instUpwardEnumerable___lam__0(size_t v_i_546_){
_start:
{
size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; uint8_t v___x_550_; 
v___x_547_ = lean_usize_once(&l_ISize_instUpwardEnumerable___lam__0___closed__0, &l_ISize_instUpwardEnumerable___lam__0___closed__0_once, _init_l_ISize_instUpwardEnumerable___lam__0___closed__0);
v___x_548_ = lean_isize_add(v_i_546_, v___x_547_);
v___x_549_ = lean_usize_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3);
v___x_550_ = lean_isize_dec_eq(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_box_usize(v___x_548_);
v___x_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = lean_box(0);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_ISize_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_554_){
_start:
{
size_t v_i_boxed_555_; lean_object* v_res_556_; 
v_i_boxed_555_ = lean_unbox_usize(v_i_554_);
lean_dec(v_i_554_);
v_res_556_ = l_ISize_instUpwardEnumerable___lam__0(v_i_boxed_555_);
return v_res_556_;
}
}
static lean_object* _init_l_ISize_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
size_t v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_usize_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_maxValueSealed___closed__1);
v___x_558_ = lean_isize_to_int(v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_ISize_instUpwardEnumerable___lam__1(lean_object* v_n_559_, size_t v_i_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_561_ = lean_isize_to_int(v_i_560_);
v___x_562_ = lean_nat_to_int(v_n_559_);
v___x_563_ = lean_int_add(v___x_561_, v___x_562_);
lean_dec(v___x_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_obj_once(&l_ISize_instUpwardEnumerable___lam__1___closed__0, &l_ISize_instUpwardEnumerable___lam__1___closed__0_once, _init_l_ISize_instUpwardEnumerable___lam__1___closed__0);
v___x_565_ = lean_int_dec_le(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
return v___x_566_;
}
else
{
size_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_isize_of_int(v___x_563_);
lean_dec(v___x_563_);
v___x_568_ = lean_box_usize(v___x_567_);
v___x_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l_ISize_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_570_, lean_object* v_i_571_){
_start:
{
size_t v_i_boxed_572_; lean_object* v_res_573_; 
v_i_boxed_572_ = lean_unbox_usize(v_i_571_);
lean_dec(v_i_571_);
v_res_573_ = l_ISize_instUpwardEnumerable___lam__1(v_n_570_, v_i_boxed_572_);
return v_res_573_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1(void){
_start:
{
size_t v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_usize_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__3);
v___x_581_ = lean_box_usize(v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0___boxed__const__1;
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f(void){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instLeast_x3f___closed__0);
return v___x_584_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1(void){
_start:
{
lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___x_588_; 
v___f_586_ = lean_alloc_closure((void*)(l_USize_ofBitVec___boxed), 1, 0);
v___f_587_ = ((lean_object*)(l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__0));
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___f_587_);
lean_ctor_set(v___x_588_, 1, v___f_586_);
return v___x_588_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits(void){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_instHasModelBitVecNumBits___closed__1);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_ISize_instRxcHasSize___lam__0(size_t v_lo_590_, size_t v_hi_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_592_ = lean_isize_to_int(v_hi_591_);
v___x_593_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_594_ = lean_int_add(v___x_592_, v___x_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_isize_to_int(v_lo_590_);
v___x_596_ = lean_int_sub(v___x_594_, v___x_595_);
lean_dec(v___x_595_);
lean_dec(v___x_594_);
v___x_597_ = l_Int_toNat(v___x_596_);
lean_dec(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_ISize_instRxcHasSize___lam__0___boxed(lean_object* v_lo_598_, lean_object* v_hi_599_){
_start:
{
size_t v_lo_boxed_600_; size_t v_hi_boxed_601_; lean_object* v_res_602_; 
v_lo_boxed_600_ = lean_unbox_usize(v_lo_598_);
lean_dec(v_lo_598_);
v_hi_boxed_601_ = lean_unbox_usize(v_hi_599_);
lean_dec(v_hi_599_);
v_res_602_ = l_ISize_instRxcHasSize___lam__0(v_lo_boxed_600_, v_hi_boxed_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_ISize_instRxoHasSize___lam__0(size_t v_lo_605_, size_t v_hi_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_607_ = lean_isize_to_int(v_hi_606_);
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0, &l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__HasModel_instHasSizeInt8___lam__0___closed__0);
v___x_610_ = lean_int_add(v___x_607_, v___x_609_);
lean_dec(v___x_607_);
v___x_611_ = lean_isize_to_int(v_lo_605_);
v___x_612_ = lean_int_sub(v___x_610_, v___x_611_);
lean_dec(v___x_611_);
lean_dec(v___x_610_);
v___x_613_ = l_Int_toNat(v___x_612_);
lean_dec(v___x_612_);
v___x_614_ = lean_nat_sub(v___x_613_, v___x_608_);
lean_dec(v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_ISize_instRxoHasSize___lam__0___boxed(lean_object* v_lo_615_, lean_object* v_hi_616_){
_start:
{
size_t v_lo_boxed_617_; size_t v_hi_boxed_618_; lean_object* v_res_619_; 
v_lo_boxed_617_ = lean_unbox_usize(v_lo_615_);
lean_dec(v_lo_615_);
v_hi_boxed_618_ = lean_unbox_usize(v_hi_616_);
lean_dec(v_hi_616_);
v_res_619_ = l_ISize_instRxoHasSize___lam__0(v_lo_boxed_617_, v_hi_boxed_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_ISize_instRxiHasSize___lam__0(size_t v_lo_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_obj_once(&l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1, &l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1_once, _init_l___private_Init_Data_Range_Polymorphic_SInt_0__ISize_minValueSealed___closed__1);
v___x_624_ = lean_isize_to_int(v_lo_622_);
v___x_625_ = lean_int_sub(v___x_623_, v___x_624_);
lean_dec(v___x_624_);
v___x_626_ = l_Int_toNat(v___x_625_);
lean_dec(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_ISize_instRxiHasSize___lam__0___boxed(lean_object* v_lo_627_){
_start:
{
size_t v_lo_boxed_628_; lean_object* v_res_629_; 
v_lo_boxed_628_ = lean_unbox_usize(v_lo_627_);
lean_dec(v_lo_627_);
v_res_629_ = l_ISize_instRxiHasSize___lam__0(v_lo_boxed_628_);
return v_res_629_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Internal_SignedBitVec(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_SInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
