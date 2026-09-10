// Lean compiler output
// Module: Lean.Compiler.LCNF.PassManager
// Imports: public import Lean.Compiler.LCNF.CompilerM import Init.Data.Fin.Lemmas import Init.Omega
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx(uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Purity_ctorIdx(uint8_t);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toNat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toNat___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "base"};
static const lean_object* l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mono"};
static const lean_object* l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "impure"};
static const lean_object* l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToStringPhase___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToStringPhase___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instToStringPhase___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instToStringPhase___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instToStringPhase___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instToStringPhase___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instToStringPhase = (const lean_object*)&l_Lean_Compiler_LCNF_instToStringPhase___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Compiler.LCNF.PassManager"};
static const lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Compiler.LCNF.Phase.withPurityCheck"};
static const lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ", this is a bug"};
static const lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Compiler error: "};
static const lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " is not equivalent to IR phase "};
static const lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instLTPhase;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instLEPhase;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableLtPhase(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableLtPhase___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableLePhase(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableLePhase___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4_value;
static const lean_array_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__14_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__16_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__16_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__18_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__18_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19_value;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arith"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23_value),LEAN_SCALAR_PTR_LITERAL(72, 221, 106, 103, 22, 21, 224, 51)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32;
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33_value),LEAN_SCALAR_PTR_LITERAL(236, 252, 83, 10, 217, 228, 80, 149)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedPass___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPass___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPass___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPass___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedPass = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPass___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___closed__1_value;
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedPassManager_default = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instInhabitedPassManager = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedPassManager_default___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LCNF compiler"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " has phase "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " but should have "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_validate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_validate___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not find any occurrence of "};
static const lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Lean.Compiler.LCNF.PassInstaller.withEachOccurrence"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "phase mismatch"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Tried to insert pass after "};
static const lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", occurrence "};
static const lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " but "};
static const lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " is not in the pass list"};
static const lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Tried to replace "};
static const lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PassInstaller"};
static const lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(110, 217, 253, 71, 42, 135, 144, 215)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toNat(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toNat___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_34__boxed_6_; lean_object* v_res_7_; 
v_x_34__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Compiler_LCNF_Phase_toNat(v_x_34__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToStringPhase___lam__0(uint8_t v_x_11_){
_start:
{
switch(v_x_11_)
{
case 0:
{
lean_object* v___x_12_; 
v___x_12_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
return v___x_12_;
}
case 1:
{
lean_object* v___x_13_; 
v___x_13_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
return v___x_13_;
}
default: 
{
lean_object* v___x_14_; 
v___x_14_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToStringPhase___lam__0___boxed(lean_object* v_x_15_){
_start:
{
uint8_t v_x_36__boxed_16_; lean_object* v_res_17_; 
v_x_36__boxed_16_ = lean_unbox(v_x_15_);
v_res_17_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0(v_x_36__boxed_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object* v_inst_26_, uint8_t v_pp_27_, uint8_t v_ip_28_, lean_object* v_x_29_){
_start:
{
uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_30_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_pp_27_);
v___x_31_ = l_Lean_Compiler_LCNF_Purity_ctorIdx(v___x_30_);
v___x_32_ = l_Lean_Compiler_LCNF_Purity_ctorIdx(v_ip_28_);
v___x_33_ = lean_nat_dec_eq(v___x_31_, v___x_32_);
lean_dec(v___x_32_);
lean_dec(v___x_31_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___y_39_; lean_object* v___y_40_; lean_object* v___x_46_; lean_object* v___y_48_; 
lean_dec(v_x_29_);
v___x_34_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0));
v___x_35_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1));
v___x_36_ = lean_unsigned_to_nat(33u);
v___x_37_ = lean_unsigned_to_nat(4u);
v___x_46_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3));
switch(v_pp_27_)
{
case 0:
{
lean_object* v___x_54_; 
v___x_54_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_48_ = v___x_54_;
goto v___jp_47_;
}
case 1:
{
lean_object* v___x_55_; 
v___x_55_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_48_ = v___x_55_;
goto v___jp_47_;
}
default: 
{
lean_object* v___x_56_; 
v___x_56_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_48_ = v___x_56_;
goto v___jp_47_;
}
}
v___jp_38_:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_string_append(v___y_39_, v___y_40_);
v___x_42_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2));
v___x_43_ = lean_string_append(v___x_41_, v___x_42_);
v___x_44_ = l_mkPanicMessageWithDecl(v___x_34_, v___x_35_, v___x_36_, v___x_37_, v___x_43_);
lean_dec_ref(v___x_43_);
v___x_45_ = l_panic___redArg(v_inst_26_, v___x_44_);
return v___x_45_;
}
v___jp_47_:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_string_append(v___x_46_, v___y_48_);
v___x_50_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4));
v___x_51_ = lean_string_append(v___x_49_, v___x_50_);
if (v_ip_28_ == 0)
{
lean_object* v___x_52_; 
v___x_52_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5));
v___y_39_ = v___x_51_;
v___y_40_ = v___x_52_;
goto v___jp_38_;
}
else
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_39_ = v___x_51_;
v___y_40_ = v___x_53_;
goto v___jp_38_;
}
}
}
else
{
lean_object* v___x_57_; 
v___x_57_ = lean_apply_1(v_x_29_, lean_box(0));
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___boxed(lean_object* v_inst_58_, lean_object* v_pp_59_, lean_object* v_ip_60_, lean_object* v_x_61_){
_start:
{
uint8_t v_pp_boxed_62_; uint8_t v_ip_boxed_63_; lean_object* v_res_64_; 
v_pp_boxed_62_ = lean_unbox(v_pp_59_);
v_ip_boxed_63_ = lean_unbox(v_ip_60_);
v_res_64_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v_inst_58_, v_pp_boxed_62_, v_ip_boxed_63_, v_x_61_);
lean_dec(v_inst_58_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck(lean_object* v_00_u03b1_65_, lean_object* v_inst_66_, uint8_t v_pp_67_, uint8_t v_ip_68_, lean_object* v_x_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v_inst_66_, v_pp_67_, v_ip_68_, v_x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___boxed(lean_object* v_00_u03b1_71_, lean_object* v_inst_72_, lean_object* v_pp_73_, lean_object* v_ip_74_, lean_object* v_x_75_){
_start:
{
uint8_t v_pp_boxed_76_; uint8_t v_ip_boxed_77_; lean_object* v_res_78_; 
v_pp_boxed_76_ = lean_unbox(v_pp_73_);
v_ip_boxed_77_ = lean_unbox(v_ip_74_);
v_res_78_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck(v_00_u03b1_71_, v_inst_72_, v_pp_boxed_76_, v_ip_boxed_77_, v_x_75_);
lean_dec(v_inst_72_);
return v_res_78_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instLTPhase(void){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_box(0);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instLEPhase(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(0);
return v___x_80_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableLtPhase(uint8_t v_p1_81_, uint8_t v_p2_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_83_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p1_81_);
v___x_84_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p2_82_);
v___x_85_ = lean_nat_dec_lt(v___x_83_, v___x_84_);
lean_dec(v___x_84_);
lean_dec(v___x_83_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableLtPhase___boxed(lean_object* v_p1_86_, lean_object* v_p2_87_){
_start:
{
uint8_t v_p1_boxed_88_; uint8_t v_p2_boxed_89_; uint8_t v_res_90_; lean_object* v_r_91_; 
v_p1_boxed_88_ = lean_unbox(v_p1_86_);
v_p2_boxed_89_ = lean_unbox(v_p2_87_);
v_res_90_ = l_Lean_Compiler_LCNF_instDecidableLtPhase(v_p1_boxed_88_, v_p2_boxed_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableLePhase(uint8_t v_p1_92_, uint8_t v_p2_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_94_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p1_92_);
v___x_95_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p2_93_);
v___x_96_ = lean_nat_dec_le(v___x_94_, v___x_95_);
lean_dec(v___x_95_);
lean_dec(v___x_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableLePhase___boxed(lean_object* v_p1_97_, lean_object* v_p2_98_){
_start:
{
uint8_t v_p1_boxed_99_; uint8_t v_p2_boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v_p1_boxed_99_ = lean_unbox(v_p1_97_);
v_p2_boxed_100_ = lean_unbox(v_p2_98_);
v_res_101_ = l_Lean_Compiler_LCNF_instDecidableLePhase(v_p1_boxed_99_, v_p2_boxed_100_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10));
v___x_130_ = l_Lean_mkAtom(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12);
v___x_132_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_133_ = lean_array_push(v___x_132_, v___x_131_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20));
v___x_154_ = l_Lean_mkAtom(v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21);
v___x_156_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_157_ = lean_array_push(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23));
v___x_160_ = lean_string_utf8_byte_size(v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23));
v___x_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_161_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_167_ = lean_box(0);
v___x_168_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26));
v___x_169_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25);
v___x_170_ = lean_box(2);
v___x_171_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
lean_ctor_set(v___x_171_, 3, v___x_167_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27);
v___x_173_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22);
v___x_174_ = lean_array_push(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28);
v___x_176_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19));
v___x_177_ = lean_box(2);
v___x_178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29);
v___x_180_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_181_ = lean_array_push(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30);
v___x_183_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17));
v___x_184_ = lean_box(2);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31);
v___x_187_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_188_ = lean_array_push(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33));
v___x_191_ = lean_string_utf8_byte_size(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33));
v___x_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 2, v___x_192_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_198_ = lean_box(0);
v___x_199_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36));
v___x_200_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35);
v___x_201_ = lean_box(2);
v___x_202_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_200_);
lean_ctor_set(v___x_202_, 2, v___x_199_);
lean_ctor_set(v___x_202_, 3, v___x_198_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37);
v___x_204_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22);
v___x_205_ = lean_array_push(v___x_204_, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_206_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38);
v___x_207_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19));
v___x_208_ = lean_box(2);
v___x_209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_207_);
lean_ctor_set(v___x_209_, 2, v___x_206_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39);
v___x_211_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_212_ = lean_array_push(v___x_211_, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_213_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40);
v___x_214_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17));
v___x_215_ = lean_box(2);
v___x_216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_214_);
lean_ctor_set(v___x_216_, 2, v___x_213_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41);
v___x_218_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32);
v___x_219_ = lean_array_push(v___x_218_, v___x_217_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42);
v___x_221_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9));
v___x_222_ = lean_box(2);
v___x_223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v___x_221_);
lean_ctor_set(v___x_223_, 2, v___x_220_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43);
v___x_225_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_226_ = lean_array_push(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_227_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44);
v___x_228_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15));
v___x_229_ = lean_box(2);
v___x_230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
lean_ctor_set(v___x_230_, 2, v___x_227_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45);
v___x_232_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13);
v___x_233_ = lean_array_push(v___x_232_, v___x_231_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47));
v___x_239_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46);
v___x_240_ = lean_array_push(v___x_239_, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47));
v___x_242_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48);
v___x_243_ = lean_array_push(v___x_242_, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47));
v___x_245_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49);
v___x_246_ = lean_array_push(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47));
v___x_248_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50);
v___x_249_ = lean_array_push(v___x_248_, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_250_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51);
v___x_251_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11));
v___x_252_ = lean_box(2);
v___x_253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_251_);
lean_ctor_set(v___x_253_, 2, v___x_250_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52);
v___x_255_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_256_ = lean_array_push(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_257_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53);
v___x_258_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9));
v___x_259_ = lean_box(2);
v___x_260_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_258_);
lean_ctor_set(v___x_260_, 2, v___x_257_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54);
v___x_262_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_263_ = lean_array_push(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55);
v___x_265_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7));
v___x_266_ = lean_box(2);
v___x_267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_264_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56);
v___x_269_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_270_ = lean_array_push(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57);
v___x_272_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4));
v___x_273_ = lean_box(2);
v___x_274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_271_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(lean_object* v_decls_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v_decls_276_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___lam__0___boxed(lean_object* v_decls_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(v_decls_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___y_298_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___boxed(lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(lean_object* v_run_321_, size_t v_sz_322_, size_t v_i_323_, lean_object* v_bs_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_lt(v_i_323_, v_sz_322_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec_ref(v_run_321_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_bs_324_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0));
v___x_333_ = l_Lean_Core_checkSystem(v___x_332_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_v_334_; lean_object* v___x_335_; 
lean_dec_ref_known(v___x_333_, 1);
v_v_334_ = lean_array_uget_borrowed(v_bs_324_, v_i_323_);
lean_inc_ref(v_run_321_);
lean_inc(v___y_328_);
lean_inc_ref(v___y_327_);
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
lean_inc(v_v_334_);
v___x_335_ = lean_apply_6(v_run_321_, v_v_334_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, lean_box(0));
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; lean_object* v_bs_x27_338_; size_t v___x_339_; size_t v___x_340_; lean_object* v___x_341_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
v___x_337_ = lean_unsigned_to_nat(0u);
v_bs_x27_338_ = lean_array_uset(v_bs_324_, v_i_323_, v___x_337_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_add(v_i_323_, v___x_339_);
v___x_341_ = lean_array_uset(v_bs_x27_338_, v_i_323_, v_a_336_);
v_i_323_ = v___x_340_;
v_bs_324_ = v___x_341_;
goto _start;
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v_bs_324_);
lean_dec_ref(v_run_321_);
v_a_343_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_335_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_335_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v_bs_324_);
lean_dec_ref(v_run_321_);
v_a_351_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_333_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_333_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___boxed(lean_object* v_run_359_, lean_object* v_sz_360_, lean_object* v_i_361_, lean_object* v_bs_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
size_t v_sz_boxed_368_; size_t v_i_boxed_369_; lean_object* v_res_370_; 
v_sz_boxed_368_ = lean_unbox_usize(v_sz_360_);
lean_dec(v_sz_360_);
v_i_boxed_369_ = lean_unbox_usize(v_i_361_);
lean_dec(v_i_361_);
v_res_370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_359_, v_sz_boxed_368_, v_i_boxed_369_, v_bs_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(lean_object* v_run_371_, lean_object* v_xs_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
size_t v_sz_378_; size_t v___x_379_; lean_object* v___x_380_; 
v_sz_378_ = lean_array_size(v_xs_372_);
v___x_379_ = ((size_t)0ULL);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_371_, v_sz_378_, v___x_379_, v_xs_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed(lean_object* v_run_381_, lean_object* v_xs_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(v_run_381_, v_xs_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object* v_name_389_, uint8_t v_phase_390_, lean_object* v_run_391_, lean_object* v_occurrence_392_){
_start:
{
lean_object* v___f_393_; uint8_t v___x_394_; lean_object* v___x_395_; 
v___f_393_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed), 7, 1);
lean_closure_set(v___f_393_, 0, v_run_391_);
v___x_394_ = 0;
v___x_395_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_395_, 0, v_occurrence_392_);
lean_ctor_set(v___x_395_, 1, v_name_389_);
lean_ctor_set(v___x_395_, 2, v___f_393_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*3, v_phase_390_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*3 + 1, v_phase_390_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*3 + 2, v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___boxed(lean_object* v_name_396_, lean_object* v_phase_397_, lean_object* v_run_398_, lean_object* v_occurrence_399_){
_start:
{
uint8_t v_phase_boxed_400_; lean_object* v_res_401_; 
v_phase_boxed_400_ = lean_unbox(v_phase_397_);
v_res_401_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v_name_396_, v_phase_boxed_400_, v_run_398_, v_occurrence_399_);
return v_res_401_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_402_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_406_);
lean_ctor_set(v___x_407_, 3, v___x_406_);
lean_ctor_set(v___x_407_, 4, v___x_405_);
lean_ctor_set(v___x_407_, 5, v___x_405_);
lean_ctor_set(v___x_407_, 6, v___x_405_);
lean_ctor_set(v___x_407_, 7, v___x_405_);
lean_ctor_set(v___x_407_, 8, v___x_405_);
lean_ctor_set(v___x_407_, 9, v___x_405_);
lean_ctor_set(v___x_407_, 10, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_unsigned_to_nat(32u);
v___x_409_ = lean_mk_empty_array_with_capacity(v___x_408_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_411_ = ((size_t)5ULL);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_unsigned_to_nat(32u);
v___x_414_ = lean_mk_empty_array_with_capacity(v___x_413_);
v___x_415_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3);
v___x_416_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_412_);
lean_ctor_set(v___x_416_, 3, v___x_412_);
lean_ctor_set_usize(v___x_416_, 4, v___x_411_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = lean_box(1);
v___x_418_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4);
v___x_419_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
v___x_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_418_);
lean_ctor_set(v___x_420_, 2, v___x_417_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(lean_object* v_msgData_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; lean_object* v_toCold_426_; lean_object* v_env_427_; lean_object* v_options_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_425_ = lean_st_ref_get(v___y_423_);
v_toCold_426_ = lean_ctor_get(v___y_422_, 0);
v_env_427_ = lean_ctor_get(v___x_425_, 0);
lean_inc_ref(v_env_427_);
lean_dec(v___x_425_);
v_options_428_ = lean_ctor_get(v_toCold_426_, 2);
v___x_429_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2);
v___x_430_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_428_);
v___x_431_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_431_, 0, v_env_427_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
lean_ctor_set(v___x_431_, 2, v___x_430_);
lean_ctor_set(v___x_431_, 3, v_options_428_);
v___x_432_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_msgData_421_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___boxed(lean_object* v_msgData_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msgData_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(lean_object* v_msg_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_ref_443_; lean_object* v___x_444_; lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
v_ref_443_ = lean_ctor_get(v___y_440_, 2);
v___x_444_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msg_439_, v___y_440_, v___y_441_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_453_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_451_; 
lean_inc(v_ref_443_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_ref_443_);
lean_ctor_set(v___x_449_, 1, v_a_445_);
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 1);
lean_ctor_set(v___x_447_, 0, v___x_449_);
v___x_451_ = v___x_447_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg___boxed(lean_object* v_msg_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(uint8_t v_phase_461_, lean_object* v_as_462_, size_t v_sz_463_, size_t v_i_464_, lean_object* v_b_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_a_470_; uint8_t v___x_474_; 
v___x_474_ = lean_usize_dec_lt(v_i_464_, v_sz_463_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v_b_465_);
return v___x_475_;
}
else
{
lean_object* v_a_476_; uint8_t v_phase_477_; lean_object* v_name_478_; lean_object* v___x_479_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_a_476_ = lean_array_uget_borrowed(v_as_462_, v_i_464_);
v_phase_477_ = lean_ctor_get_uint8(v_a_476_, sizeof(void*)*3);
v_name_478_ = lean_ctor_get(v_a_476_, 1);
v___x_479_ = lean_box(0);
v___x_487_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_phase_477_);
v___x_488_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_phase_461_);
v___x_489_ = lean_nat_dec_eq(v___x_487_, v___x_488_);
lean_dec(v___x_488_);
lean_dec(v___x_487_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___y_494_; 
lean_inc(v_name_478_);
v___x_490_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_478_, v___x_474_);
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0));
v___x_492_ = lean_string_append(v___x_490_, v___x_491_);
switch(v_phase_477_)
{
case 0:
{
lean_object* v___x_501_; 
v___x_501_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_494_ = v___x_501_;
goto v___jp_493_;
}
case 1:
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_494_ = v___x_502_;
goto v___jp_493_;
}
default: 
{
lean_object* v___x_503_; 
v___x_503_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_494_ = v___x_503_;
goto v___jp_493_;
}
}
v___jp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_string_append(v___x_492_, v___y_494_);
v___x_496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1));
v___x_497_ = lean_string_append(v___x_495_, v___x_496_);
switch(v_phase_461_)
{
case 0:
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_481_ = v___x_497_;
v___y_482_ = v___x_498_;
goto v___jp_480_;
}
case 1:
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_481_ = v___x_497_;
v___y_482_ = v___x_499_;
goto v___jp_480_;
}
default: 
{
lean_object* v___x_500_; 
v___x_500_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_481_ = v___x_497_;
v___y_482_ = v___x_500_;
goto v___jp_480_;
}
}
}
}
else
{
v_a_470_ = v___x_479_;
goto v___jp_469_;
}
v___jp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_483_ = lean_string_append(v___y_481_, v___y_482_);
v___x_484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
v___x_485_ = l_Lean_MessageData_ofFormat(v___x_484_);
v___x_486_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_485_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_dec_ref_known(v___x_486_, 1);
v_a_470_ = v___x_479_;
goto v___jp_469_;
}
else
{
return v___x_486_;
}
}
}
v___jp_469_:
{
size_t v___x_471_; size_t v___x_472_; 
v___x_471_ = ((size_t)1ULL);
v___x_472_ = lean_usize_add(v_i_464_, v___x_471_);
v_i_464_ = v___x_472_;
v_b_465_ = v_a_470_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___boxed(lean_object* v_phase_504_, lean_object* v_as_505_, lean_object* v_sz_506_, lean_object* v_i_507_, lean_object* v_b_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
uint8_t v_phase_boxed_512_; size_t v_sz_boxed_513_; size_t v_i_boxed_514_; lean_object* v_res_515_; 
v_phase_boxed_512_ = lean_unbox(v_phase_504_);
v_sz_boxed_513_ = lean_unbox_usize(v_sz_506_);
lean_dec(v_sz_506_);
v_i_boxed_514_ = lean_unbox_usize(v_i_507_);
lean_dec(v_i_507_);
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_boxed_512_, v_as_505_, v_sz_boxed_513_, v_i_boxed_514_, v_b_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v_as_505_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(uint8_t v_phase_516_, lean_object* v_passes_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___x_521_; size_t v_sz_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_521_ = lean_box(0);
v_sz_522_ = lean_array_size(v_passes_517_);
v___x_523_ = ((size_t)0ULL);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_516_, v_passes_517_, v_sz_522_, v___x_523_, v___x_521_, v_a_518_, v_a_519_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v___x_524_, 0);
lean_dec(v_unused_532_);
v___x_526_ = v___x_524_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_dec(v___x_524_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_521_);
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_521_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses___boxed(lean_object* v_phase_533_, lean_object* v_passes_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
uint8_t v_phase_boxed_538_; lean_object* v_res_539_; 
v_phase_boxed_538_ = lean_unbox(v_phase_533_);
v_res_539_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v_phase_boxed_538_, v_passes_534_, v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_passes_534_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(lean_object* v_00_u03b1_540_, lean_object* v_msg_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_541_, v___y_542_, v___y_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___boxed(lean_object* v_00_u03b1_546_, lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(v_00_u03b1_546_, v_msg_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_validate(lean_object* v_manager_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_basePasses_556_; lean_object* v_monoPasses_557_; lean_object* v_monoPassesNoLambda_558_; uint8_t v___x_559_; lean_object* v___x_560_; 
v_basePasses_556_ = lean_ctor_get(v_manager_552_, 0);
v_monoPasses_557_ = lean_ctor_get(v_manager_552_, 1);
v_monoPassesNoLambda_558_ = lean_ctor_get(v_manager_552_, 2);
v___x_559_ = 0;
v___x_560_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_559_, v_basePasses_556_, v_a_553_, v_a_554_);
if (lean_obj_tag(v___x_560_) == 0)
{
uint8_t v___x_561_; lean_object* v___x_562_; 
lean_dec_ref_known(v___x_560_, 1);
v___x_561_ = 1;
v___x_562_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_561_, v_monoPasses_557_, v_a_553_, v_a_554_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; 
lean_dec_ref_known(v___x_562_, 1);
v___x_563_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_561_, v_monoPassesNoLambda_558_, v_a_553_, v_a_554_);
return v___x_563_;
}
else
{
return v___x_562_;
}
}
else
{
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_validate___boxed(lean_object* v_manager_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Compiler_LCNF_PassManager_validate(v_manager_564_, v_a_565_, v_a_566_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec_ref(v_manager_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(lean_object* v_targetName_569_, lean_object* v_as_570_, size_t v_sz_571_, size_t v_i_572_, lean_object* v_b_573_){
_start:
{
lean_object* v_a_576_; uint8_t v___x_580_; 
v___x_580_ = lean_usize_dec_lt(v_i_572_, v_sz_571_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v_b_573_);
return v___x_581_;
}
else
{
lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_600_; 
v_fst_582_ = lean_ctor_get(v_b_573_, 0);
v_snd_583_ = lean_ctor_get(v_b_573_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_b_573_);
if (v_isSharedCheck_600_ == 0)
{
v___x_585_ = v_b_573_;
v_isShared_586_ = v_isSharedCheck_600_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_snd_583_);
lean_inc(v_fst_582_);
lean_dec(v_b_573_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_600_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_a_587_; lean_object* v___y_589_; lean_object* v_occurrence_595_; lean_object* v_name_596_; uint8_t v___x_597_; 
v_a_587_ = lean_array_uget_borrowed(v_as_570_, v_i_572_);
v_occurrence_595_ = lean_ctor_get(v_a_587_, 0);
v_name_596_ = lean_ctor_get(v_a_587_, 1);
v___x_597_ = lean_name_eq(v_name_596_, v_targetName_569_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_del_object(v___x_585_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_fst_582_);
lean_ctor_set(v___x_598_, 1, v_snd_583_);
v_a_576_ = v___x_598_;
goto v___jp_575_;
}
else
{
lean_dec(v_snd_583_);
if (lean_obj_tag(v_fst_582_) == 0)
{
if (v___x_597_ == 0)
{
v___y_589_ = v_fst_582_;
goto v___jp_588_;
}
else
{
lean_object* v___x_599_; 
lean_inc(v_occurrence_595_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v_occurrence_595_);
v___y_589_ = v___x_599_;
goto v___jp_588_;
}
}
else
{
v___y_589_ = v_fst_582_;
goto v___jp_588_;
}
}
v___jp_588_:
{
lean_object* v_occurrence_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v_occurrence_590_ = lean_ctor_get(v_a_587_, 0);
lean_inc(v_occurrence_590_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v_occurrence_590_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 1, v___x_591_);
lean_ctor_set(v___x_585_, 0, v___y_589_);
v___x_593_ = v___x_585_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___y_589_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
v_a_576_ = v___x_593_;
goto v___jp_575_;
}
}
}
}
v___jp_575_:
{
size_t v___x_577_; size_t v___x_578_; 
v___x_577_ = ((size_t)1ULL);
v___x_578_ = lean_usize_add(v_i_572_, v___x_577_);
v_i_572_ = v___x_578_;
v_b_573_ = v_a_576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg___boxed(lean_object* v_targetName_601_, lean_object* v_as_602_, lean_object* v_sz_603_, lean_object* v_i_604_, lean_object* v_b_605_, lean_object* v___y_606_){
_start:
{
size_t v_sz_boxed_607_; size_t v_i_boxed_608_; lean_object* v_res_609_; 
v_sz_boxed_607_ = lean_unbox_usize(v_sz_603_);
lean_dec(v_sz_603_);
v_i_boxed_608_ = lean_unbox_usize(v_i_604_);
lean_dec(v_i_604_);
v_res_609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_601_, v_as_602_, v_sz_boxed_607_, v_i_boxed_608_, v_b_605_);
lean_dec_ref(v_as_602_);
lean_dec(v_targetName_601_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(lean_object* v_targetName_613_, lean_object* v_passes_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___x_628_; size_t v_sz_629_; size_t v___x_630_; lean_object* v___x_631_; 
v___x_628_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1));
v_sz_629_ = lean_array_size(v_passes_614_);
v___x_630_ = ((size_t)0ULL);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_613_, v_passes_614_, v_sz_629_, v___x_630_, v___x_628_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_651_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_651_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_651_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_651_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v_fst_636_; 
v_fst_636_ = lean_ctor_get(v_a_632_, 0);
lean_inc(v_fst_636_);
if (lean_obj_tag(v_fst_636_) == 1)
{
lean_object* v_snd_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_649_; 
v_snd_637_ = lean_ctor_get(v_a_632_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_a_632_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_a_632_, 0);
lean_dec(v_unused_650_);
v___x_639_ = v_a_632_;
v_isShared_640_ = v_isSharedCheck_649_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_snd_637_);
lean_dec(v_a_632_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_649_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
if (lean_obj_tag(v_snd_637_) == 1)
{
lean_object* v_val_641_; lean_object* v_val_642_; lean_object* v___x_644_; 
lean_dec(v_targetName_613_);
v_val_641_ = lean_ctor_get(v_fst_636_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v_fst_636_, 1);
v_val_642_ = lean_ctor_get(v_snd_637_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v_snd_637_, 1);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v_val_642_);
lean_ctor_set(v___x_639_, 0, v_val_641_);
v___x_644_ = v___x_639_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_val_641_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v_val_642_);
v___x_644_ = v_reuseFailAlloc_648_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_644_);
v___x_646_ = v___x_634_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
else
{
lean_del_object(v___x_639_);
lean_dec(v_snd_637_);
lean_dec_ref_known(v_fst_636_, 1);
lean_del_object(v___x_634_);
v___y_619_ = v_a_615_;
v___y_620_ = v_a_616_;
goto v___jp_618_;
}
}
}
else
{
lean_dec(v_fst_636_);
lean_del_object(v___x_634_);
lean_dec(v_a_632_);
v___y_619_ = v_a_615_;
v___y_620_ = v_a_616_;
goto v___jp_618_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_targetName_613_);
v_a_652_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_631_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_631_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
v___jp_618_:
{
lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_621_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0));
v___x_622_ = 1;
v___x_623_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_613_, v___x_622_);
v___x_624_ = lean_string_append(v___x_621_, v___x_623_);
lean_dec_ref(v___x_623_);
v___x_625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = l_Lean_MessageData_ofFormat(v___x_625_);
v___x_627_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_626_, v___y_619_, v___y_620_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___boxed(lean_object* v_targetName_660_, lean_object* v_passes_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(v_targetName_660_, v_passes_661_, v_a_662_, v_a_663_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec_ref(v_passes_661_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(lean_object* v_targetName_666_, lean_object* v_as_667_, size_t v_sz_668_, size_t v_i_669_, lean_object* v_b_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_666_, v_as_667_, v_sz_668_, v_i_669_, v_b_670_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___boxed(lean_object* v_targetName_675_, lean_object* v_as_676_, lean_object* v_sz_677_, lean_object* v_i_678_, lean_object* v_b_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
size_t v_sz_boxed_683_; size_t v_i_boxed_684_; lean_object* v_res_685_; 
v_sz_boxed_683_ = lean_unbox_usize(v_sz_677_);
lean_dec(v_sz_677_);
v_i_boxed_684_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(v_targetName_675_, v_as_676_, v_sz_boxed_683_, v_i_boxed_684_, v_b_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec_ref(v_as_676_);
lean_dec(v_targetName_675_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(lean_object* v_p_686_, lean_object* v_passes_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_array_push(v_passes_687_, v_p_686_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed(lean_object* v_p_693_, lean_object* v_passes_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(v_p_693_, v_passes_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(uint8_t v_phase_699_, lean_object* v_p_700_){
_start:
{
lean_object* v___f_701_; lean_object* v___x_702_; 
v___f_701_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_701_, 0, v_p_700_);
v___x_702_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_702_, 0, v___f_701_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*1, v_phase_699_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___boxed(lean_object* v_phase_703_, lean_object* v_p_704_){
_start:
{
uint8_t v_phase_boxed_705_; lean_object* v_res_706_; 
v_phase_boxed_705_ = lean_unbox(v_phase_703_);
v_res_706_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(v_phase_boxed_705_, v_p_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(lean_object* v_passesNew_707_, lean_object* v_passes_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = l_Array_append___redArg(v_passes_708_, v_passesNew_707_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed(lean_object* v_passesNew_714_, lean_object* v_passes_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(v_passesNew_714_, v_passes_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_passesNew_714_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append(uint8_t v_phase_720_, lean_object* v_passesNew_721_){
_start:
{
lean_object* v___f_722_; lean_object* v___x_723_; 
v___f_722_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed), 5, 1);
lean_closure_set(v___f_722_, 0, v_passesNew_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_723_, 0, v___f_722_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*1, v_phase_720_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___boxed(lean_object* v_phase_724_, lean_object* v_passesNew_725_){
_start:
{
uint8_t v_phase_boxed_726_; lean_object* v_res_727_; 
v_phase_boxed_726_ = lean_unbox(v_phase_724_);
v_res_727_ = l_Lean_Compiler_LCNF_PassInstaller_append(v_phase_boxed_726_, v_passesNew_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___f_733_; lean_object* v___x_1598__overap_734_; lean_object* v___x_735_; 
v___f_733_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0));
v___x_1598__overap_734_ = lean_panic_fn_borrowed(v___f_733_, v_msg_729_);
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
v___x_735_ = lean_apply_3(v___x_1598__overap_734_, v___y_730_, v___y_731_, lean_box(0));
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___boxed(lean_object* v_msg_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v_msg_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(lean_object* v_install_741_, lean_object* v_b_742_, lean_object* v_____r_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; 
lean_inc(v___y_745_);
lean_inc_ref(v___y_744_);
v___x_747_ = lean_apply_4(v_install_741_, v_b_742_, v___y_744_, v___y_745_, lean_box(0));
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v_a_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
v_a_757_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_747_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_747_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0___boxed(lean_object* v_install_765_, lean_object* v_b_766_, lean_object* v_____r_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_765_, v_b_766_, v_____r_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_771_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_774_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1));
v___x_775_ = lean_unsigned_to_nat(8u);
v___x_776_ = lean_unsigned_to_nat(170u);
v___x_777_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0));
v___x_778_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0));
v___x_779_ = l_mkPanicMessageWithDecl(v___x_778_, v___x_777_, v___x_776_, v___x_775_, v___x_774_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(lean_object* v_upperBound_780_, lean_object* v_f_781_, uint8_t v_phase_782_, lean_object* v_a_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___y_789_; uint8_t v___x_811_; 
v___x_811_ = lean_nat_dec_le(v_a_783_, v_upperBound_780_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec(v_a_783_);
lean_dec_ref(v_f_781_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v_b_784_);
return v___x_812_;
}
else
{
lean_object* v___x_813_; uint8_t v_phase_814_; lean_object* v_install_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
lean_inc_ref(v_f_781_);
lean_inc(v_a_783_);
v___x_813_ = lean_apply_1(v_f_781_, v_a_783_);
v_phase_814_ = lean_ctor_get_uint8(v___x_813_, sizeof(void*)*1);
v_install_815_ = lean_ctor_get(v___x_813_, 0);
lean_inc_ref(v_install_815_);
lean_dec_ref(v___x_813_);
v___x_816_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_phase_814_);
v___x_817_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_phase_782_);
v___x_818_ = lean_nat_dec_eq(v___x_816_, v___x_817_);
lean_dec(v___x_817_);
lean_dec(v___x_816_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2);
v___x_820_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v___x_819_, v___y_785_, v___y_786_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
v___x_822_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_815_, v_b_784_, v_a_821_, v___y_785_, v___y_786_);
v___y_789_ = v___x_822_;
goto v___jp_788_;
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref(v_install_815_);
lean_dec_ref(v_b_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_f_781_);
v_a_823_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_820_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_820_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_box(0);
v___x_832_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_815_, v_b_784_, v___x_831_, v___y_785_, v___y_786_);
v___y_789_ = v___x_832_;
goto v___jp_788_;
}
}
v___jp_788_:
{
if (lean_obj_tag(v___y_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_802_; 
v_a_790_ = lean_ctor_get(v___y_789_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___y_789_);
if (v_isSharedCheck_802_ == 0)
{
v___x_792_ = v___y_789_;
v_isShared_793_ = v_isSharedCheck_802_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___y_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_802_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
if (lean_obj_tag(v_a_790_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; 
lean_dec(v_a_783_);
lean_dec_ref(v_f_781_);
v_a_794_ = lean_ctor_get(v_a_790_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v_a_790_, 1);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v_a_794_);
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_792_);
v_a_798_ = lean_ctor_get(v_a_790_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v_a_790_, 1);
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_a_783_, v___x_799_);
lean_dec(v_a_783_);
v_a_783_ = v___x_800_;
v_b_784_ = v_a_798_;
goto _start;
}
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
lean_dec(v_a_783_);
lean_dec_ref(v_f_781_);
v_a_803_ = lean_ctor_get(v___y_789_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___y_789_);
if (v_isSharedCheck_810_ == 0)
{
v___x_805_ = v___y_789_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___y_789_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___boxed(lean_object* v_upperBound_833_, lean_object* v_f_834_, lean_object* v_phase_835_, lean_object* v_a_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
uint8_t v_phase_boxed_841_; lean_object* v_res_842_; 
v_phase_boxed_841_ = lean_unbox(v_phase_835_);
v_res_842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_833_, v_f_834_, v_phase_boxed_841_, v_a_836_, v_b_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v_upperBound_833_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(lean_object* v_targetName_843_, lean_object* v_f_844_, uint8_t v_phase_845_, lean_object* v_passes_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(v_targetName_843_, v_passes_846_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v_fst_852_; lean_object* v_snd_853_; lean_object* v___x_854_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v_fst_852_ = lean_ctor_get(v_a_851_, 0);
lean_inc(v_fst_852_);
v_snd_853_ = lean_ctor_get(v_a_851_, 1);
lean_inc(v_snd_853_);
lean_dec(v_a_851_);
v___x_854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_snd_853_, v_f_844_, v_phase_845_, v_fst_852_, v_passes_846_, v___y_847_, v___y_848_);
lean_dec(v_snd_853_);
return v___x_854_;
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v_passes_846_);
lean_dec_ref(v_f_844_);
v_a_855_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_850_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_850_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed(lean_object* v_targetName_863_, lean_object* v_f_864_, lean_object* v_phase_865_, lean_object* v_passes_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v_phase_boxed_870_; lean_object* v_res_871_; 
v_phase_boxed_870_ = lean_unbox(v_phase_865_);
v_res_871_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(v_targetName_863_, v_f_864_, v_phase_boxed_870_, v_passes_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(uint8_t v_phase_872_, lean_object* v_targetName_873_, lean_object* v_f_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___f_876_; lean_object* v___x_877_; 
v___x_875_ = lean_box(v_phase_872_);
v___f_876_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed), 7, 3);
lean_closure_set(v___f_876_, 0, v_targetName_873_);
lean_closure_set(v___f_876_, 1, v_f_874_);
lean_closure_set(v___f_876_, 2, v___x_875_);
v___x_877_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_877_, 0, v___f_876_);
lean_ctor_set_uint8(v___x_877_, sizeof(void*)*1, v_phase_872_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___boxed(lean_object* v_phase_878_, lean_object* v_targetName_879_, lean_object* v_f_880_){
_start:
{
uint8_t v_phase_boxed_881_; lean_object* v_res_882_; 
v_phase_boxed_881_ = lean_unbox(v_phase_878_);
v_res_882_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_boxed_881_, v_targetName_879_, v_f_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(lean_object* v_upperBound_883_, lean_object* v_f_884_, uint8_t v_phase_885_, lean_object* v_inst_886_, lean_object* v_R_887_, lean_object* v_a_888_, lean_object* v_b_889_, lean_object* v_c_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_883_, v_f_884_, v_phase_885_, v_a_888_, v_b_889_, v___y_891_, v___y_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___boxed(lean_object* v_upperBound_895_, lean_object* v_f_896_, lean_object* v_phase_897_, lean_object* v_inst_898_, lean_object* v_R_899_, lean_object* v_a_900_, lean_object* v_b_901_, lean_object* v_c_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
uint8_t v_phase_boxed_906_; lean_object* v_res_907_; 
v_phase_boxed_906_ = lean_unbox(v_phase_897_);
v_res_907_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(v_upperBound_895_, v_f_896_, v_phase_boxed_906_, v_inst_898_, v_R_899_, v_a_900_, v_b_901_, v_c_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v_upperBound_895_);
return v_res_907_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(lean_object* v_targetName_908_, lean_object* v_occurrence_909_, lean_object* v_p_910_){
_start:
{
lean_object* v_occurrence_911_; lean_object* v_name_912_; uint8_t v___x_913_; 
v_occurrence_911_ = lean_ctor_get(v_p_910_, 0);
v_name_912_ = lean_ctor_get(v_p_910_, 1);
v___x_913_ = lean_name_eq(v_name_912_, v_targetName_908_);
if (v___x_913_ == 0)
{
return v___x_913_;
}
else
{
uint8_t v___x_914_; 
v___x_914_ = lean_nat_dec_eq(v_occurrence_911_, v_occurrence_909_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed(lean_object* v_targetName_915_, lean_object* v_occurrence_916_, lean_object* v_p_917_){
_start:
{
uint8_t v_res_918_; lean_object* v_r_919_; 
v_res_918_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(v_targetName_915_, v_occurrence_916_, v_p_917_);
lean_dec_ref(v_p_917_);
lean_dec(v_occurrence_916_);
lean_dec(v_targetName_915_);
v_r_919_ = lean_box(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(lean_object* v___f_924_, lean_object* v_p_925_, lean_object* v_targetName_926_, lean_object* v_occurrence_927_, lean_object* v_passes_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_924_, v_passes_928_, v___x_932_);
if (lean_obj_tag(v___x_933_) == 1)
{
lean_object* v_val_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_occurrence_927_);
lean_dec(v_targetName_926_);
v_val_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_948_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_948_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_val_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_948_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_passUnderTest_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_j_942_; lean_object* v_as_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v_passUnderTest_938_ = lean_array_fget_borrowed(v_passes_928_, v_val_934_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_val_934_, v___x_939_);
lean_dec(v_val_934_);
lean_inc(v_passUnderTest_938_);
v___x_941_ = lean_apply_1(v_p_925_, v_passUnderTest_938_);
v_j_942_ = lean_array_get_size(v_passes_928_);
v_as_943_ = lean_array_push(v_passes_928_, v___x_941_);
v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_940_, v_as_943_, v_j_942_);
lean_dec(v___x_940_);
if (v_isShared_937_ == 0)
{
lean_ctor_set_tag(v___x_936_, 0);
lean_ctor_set(v___x_936_, 0, v___x_944_);
v___x_946_ = v___x_936_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
lean_object* v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v___x_933_);
lean_dec_ref(v_passes_928_);
lean_dec_ref(v_p_925_);
v___x_949_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0));
v___x_950_ = 1;
v___x_951_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_926_, v___x_950_);
v___x_952_ = lean_string_append(v___x_949_, v___x_951_);
v___x_953_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_954_ = lean_string_append(v___x_952_, v___x_953_);
v___x_955_ = l_Nat_reprFast(v_occurrence_927_);
v___x_956_ = lean_string_append(v___x_954_, v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_958_ = lean_string_append(v___x_956_, v___x_957_);
v___x_959_ = lean_string_append(v___x_958_, v___x_951_);
lean_dec_ref(v___x_951_);
v___x_960_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_961_ = lean_string_append(v___x_959_, v___x_960_);
v___x_962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
v___x_963_ = l_Lean_MessageData_ofFormat(v___x_962_);
v___x_964_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_963_, v___y_929_, v___y_930_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed(lean_object* v___f_965_, lean_object* v_p_966_, lean_object* v_targetName_967_, lean_object* v_occurrence_968_, lean_object* v_passes_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(v___f_965_, v_p_966_, v_targetName_967_, v_occurrence_968_, v_passes_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter(uint8_t v_phase_974_, lean_object* v_targetName_975_, lean_object* v_p_976_, lean_object* v_occurrence_977_){
_start:
{
lean_object* v___f_978_; lean_object* v___f_979_; lean_object* v___x_980_; 
lean_inc(v_occurrence_977_);
lean_inc(v_targetName_975_);
v___f_978_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed), 3, 2);
lean_closure_set(v___f_978_, 0, v_targetName_975_);
lean_closure_set(v___f_978_, 1, v_occurrence_977_);
v___f_979_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed), 8, 4);
lean_closure_set(v___f_979_, 0, v___f_978_);
lean_closure_set(v___f_979_, 1, v_p_976_);
lean_closure_set(v___f_979_, 2, v_targetName_975_);
lean_closure_set(v___f_979_, 3, v_occurrence_977_);
v___x_980_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_980_, 0, v___f_979_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*1, v_phase_974_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___boxed(lean_object* v_phase_981_, lean_object* v_targetName_982_, lean_object* v_p_983_, lean_object* v_occurrence_984_){
_start:
{
uint8_t v_phase_boxed_985_; lean_object* v_res_986_; 
v_phase_boxed_985_ = lean_unbox(v_phase_981_);
v_res_986_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_boxed_985_, v_targetName_982_, v_p_983_, v_occurrence_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(uint8_t v_phase_987_, lean_object* v_targetName_988_, lean_object* v_p_989_, lean_object* v_x_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_987_, v_targetName_988_, v_p_989_, v_x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed(lean_object* v_phase_992_, lean_object* v_targetName_993_, lean_object* v_p_994_, lean_object* v_x_995_){
_start:
{
uint8_t v_phase_boxed_996_; lean_object* v_res_997_; 
v_phase_boxed_996_ = lean_unbox(v_phase_992_);
v_res_997_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(v_phase_boxed_996_, v_targetName_993_, v_p_994_, v_x_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(uint8_t v_phase_998_, lean_object* v_targetName_999_, lean_object* v_p_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; 
v___x_1001_ = lean_box(v_phase_998_);
lean_inc(v_targetName_999_);
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1002_, 0, v___x_1001_);
lean_closure_set(v___f_1002_, 1, v_targetName_999_);
lean_closure_set(v___f_1002_, 2, v_p_1000_);
v___x_1003_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_998_, v_targetName_999_, v___f_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___boxed(lean_object* v_phase_1004_, lean_object* v_targetName_1005_, lean_object* v_p_1006_){
_start:
{
uint8_t v_phase_boxed_1007_; lean_object* v_res_1008_; 
v_phase_boxed_1007_ = lean_unbox(v_phase_1004_);
v_res_1008_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(v_phase_boxed_1007_, v_targetName_1005_, v_p_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(lean_object* v___f_1009_, lean_object* v_p_1010_, lean_object* v_targetName_1011_, lean_object* v_occurrence_1012_, lean_object* v_passes_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1009_, v_passes_1013_, v___x_1017_);
if (lean_obj_tag(v___x_1018_) == 1)
{
lean_object* v_val_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_occurrence_1012_);
lean_dec(v_targetName_1011_);
v_val_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1031_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_val_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1031_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_passUnderTest_1023_; lean_object* v___x_1024_; lean_object* v_j_1025_; lean_object* v_as_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v_passUnderTest_1023_ = lean_array_fget_borrowed(v_passes_1013_, v_val_1019_);
lean_inc(v_passUnderTest_1023_);
v___x_1024_ = lean_apply_1(v_p_1010_, v_passUnderTest_1023_);
v_j_1025_ = lean_array_get_size(v_passes_1013_);
v_as_1026_ = lean_array_push(v_passes_1013_, v___x_1024_);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_val_1019_, v_as_1026_, v_j_1025_);
lean_dec(v_val_1019_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set_tag(v___x_1021_, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1027_);
v___x_1029_ = v___x_1021_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec(v___x_1018_);
lean_dec_ref(v_passes_1013_);
lean_dec_ref(v_p_1010_);
v___x_1032_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0));
v___x_1033_ = 1;
v___x_1034_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_1011_, v___x_1033_);
v___x_1035_ = lean_string_append(v___x_1032_, v___x_1034_);
v___x_1036_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_1037_ = lean_string_append(v___x_1035_, v___x_1036_);
v___x_1038_ = l_Nat_reprFast(v_occurrence_1012_);
v___x_1039_ = lean_string_append(v___x_1037_, v___x_1038_);
lean_dec_ref(v___x_1038_);
v___x_1040_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_string_append(v___x_1041_, v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1043_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_1044_ = lean_string_append(v___x_1042_, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
v___x_1046_ = l_Lean_MessageData_ofFormat(v___x_1045_);
v___x_1047_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1046_, v___y_1014_, v___y_1015_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed(lean_object* v___f_1048_, lean_object* v_p_1049_, lean_object* v_targetName_1050_, lean_object* v_occurrence_1051_, lean_object* v_passes_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(v___f_1048_, v_p_1049_, v_targetName_1050_, v_occurrence_1051_, v_passes_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore(uint8_t v_phase_1057_, lean_object* v_targetName_1058_, lean_object* v_p_1059_, lean_object* v_occurrence_1060_){
_start:
{
lean_object* v___f_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; 
lean_inc(v_occurrence_1060_);
lean_inc(v_targetName_1058_);
v___f_1061_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1061_, 0, v_targetName_1058_);
lean_closure_set(v___f_1061_, 1, v_occurrence_1060_);
v___f_1062_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1062_, 0, v___f_1061_);
lean_closure_set(v___f_1062_, 1, v_p_1059_);
lean_closure_set(v___f_1062_, 2, v_targetName_1058_);
lean_closure_set(v___f_1062_, 3, v_occurrence_1060_);
v___x_1063_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1063_, 0, v___f_1062_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*1, v_phase_1057_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___boxed(lean_object* v_phase_1064_, lean_object* v_targetName_1065_, lean_object* v_p_1066_, lean_object* v_occurrence_1067_){
_start:
{
uint8_t v_phase_boxed_1068_; lean_object* v_res_1069_; 
v_phase_boxed_1068_ = lean_unbox(v_phase_1064_);
v_res_1069_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_boxed_1068_, v_targetName_1065_, v_p_1066_, v_occurrence_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(uint8_t v_phase_1070_, lean_object* v_targetName_1071_, lean_object* v_p_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_1070_, v_targetName_1071_, v_p_1072_, v_x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed(lean_object* v_phase_1075_, lean_object* v_targetName_1076_, lean_object* v_p_1077_, lean_object* v_x_1078_){
_start:
{
uint8_t v_phase_boxed_1079_; lean_object* v_res_1080_; 
v_phase_boxed_1079_ = lean_unbox(v_phase_1075_);
v_res_1080_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(v_phase_boxed_1079_, v_targetName_1076_, v_p_1077_, v_x_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(uint8_t v_phase_1081_, lean_object* v_targetName_1082_, lean_object* v_p_1083_){
_start:
{
lean_object* v___x_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; 
v___x_1084_ = lean_box(v_phase_1081_);
lean_inc(v_targetName_1082_);
v___f_1085_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1085_, 0, v___x_1084_);
lean_closure_set(v___f_1085_, 1, v_targetName_1082_);
lean_closure_set(v___f_1085_, 2, v_p_1083_);
v___x_1086_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1081_, v_targetName_1082_, v___f_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___boxed(lean_object* v_phase_1087_, lean_object* v_targetName_1088_, lean_object* v_p_1089_){
_start:
{
uint8_t v_phase_boxed_1090_; lean_object* v_res_1091_; 
v_phase_boxed_1090_ = lean_unbox(v_phase_1087_);
v_res_1091_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(v_phase_boxed_1090_, v_targetName_1088_, v_p_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(lean_object* v_targetName_1092_, lean_object* v_occurrence_1093_, lean_object* v_as_1094_, lean_object* v_j_1095_){
_start:
{
uint8_t v___y_1097_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = lean_array_get_size(v_as_1094_);
v___x_1103_ = lean_nat_dec_lt(v_j_1095_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
lean_dec(v_j_1095_);
v___x_1104_ = lean_box(0);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; lean_object* v_occurrence_1106_; lean_object* v_name_1107_; uint8_t v___x_1108_; 
v___x_1105_ = lean_array_fget_borrowed(v_as_1094_, v_j_1095_);
v_occurrence_1106_ = lean_ctor_get(v___x_1105_, 0);
v_name_1107_ = lean_ctor_get(v___x_1105_, 1);
v___x_1108_ = lean_name_eq(v_name_1107_, v_targetName_1092_);
if (v___x_1108_ == 0)
{
v___y_1097_ = v___x_1108_;
goto v___jp_1096_;
}
else
{
uint8_t v___x_1109_; 
v___x_1109_ = lean_nat_dec_eq(v_occurrence_1106_, v_occurrence_1093_);
v___y_1097_ = v___x_1109_;
goto v___jp_1096_;
}
}
v___jp_1096_:
{
if (v___y_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_nat_add(v_j_1095_, v___x_1098_);
lean_dec(v_j_1095_);
v_j_1095_ = v___x_1099_;
goto _start;
}
else
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_j_1095_);
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0___boxed(lean_object* v_targetName_1110_, lean_object* v_occurrence_1111_, lean_object* v_as_1112_, lean_object* v_j_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_1110_, v_occurrence_1111_, v_as_1112_, v_j_1113_);
lean_dec_ref(v_as_1112_);
lean_dec(v_occurrence_1111_);
lean_dec(v_targetName_1110_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(lean_object* v_targetName_1116_, lean_object* v_occurrence_1117_, lean_object* v_p_1118_, lean_object* v_passes_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_1116_, v_occurrence_1117_, v_passes_1119_, v___x_1123_);
if (lean_obj_tag(v___x_1124_) == 1)
{
lean_object* v_val_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_occurrence_1117_);
lean_dec(v_targetName_1116_);
v_val_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1142_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_val_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1142_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = lean_array_get_size(v_passes_1119_);
v___x_1130_ = lean_nat_dec_lt(v_val_1125_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1132_; 
lean_dec(v_val_1125_);
lean_dec_ref(v_p_1118_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set_tag(v___x_1127_, 0);
lean_ctor_set(v___x_1127_, 0, v_passes_1119_);
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_passes_1119_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
else
{
lean_object* v_v_1134_; lean_object* v___x_1135_; lean_object* v_xs_x27_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v_v_1134_ = lean_array_fget(v_passes_1119_, v_val_1125_);
v___x_1135_ = lean_box(0);
v_xs_x27_1136_ = lean_array_fset(v_passes_1119_, v_val_1125_, v___x_1135_);
v___x_1137_ = lean_apply_1(v_p_1118_, v_v_1134_);
v___x_1138_ = lean_array_fset(v_xs_x27_1136_, v_val_1125_, v___x_1137_);
lean_dec(v_val_1125_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set_tag(v___x_1127_, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1138_);
v___x_1140_ = v___x_1127_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
lean_dec(v___x_1124_);
lean_dec_ref(v_passes_1119_);
lean_dec_ref(v_p_1118_);
v___x_1143_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0));
v___x_1144_ = 1;
v___x_1145_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_1116_, v___x_1144_);
v___x_1146_ = lean_string_append(v___x_1143_, v___x_1145_);
v___x_1147_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_1148_ = lean_string_append(v___x_1146_, v___x_1147_);
v___x_1149_ = l_Nat_reprFast(v_occurrence_1117_);
v___x_1150_ = lean_string_append(v___x_1148_, v___x_1149_);
lean_dec_ref(v___x_1149_);
v___x_1151_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_1152_ = lean_string_append(v___x_1150_, v___x_1151_);
v___x_1153_ = lean_string_append(v___x_1152_, v___x_1145_);
lean_dec_ref(v___x_1145_);
v___x_1154_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_1155_ = lean_string_append(v___x_1153_, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
v___x_1157_ = l_Lean_MessageData_ofFormat(v___x_1156_);
v___x_1158_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1157_, v___y_1120_, v___y_1121_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed(lean_object* v_targetName_1159_, lean_object* v_occurrence_1160_, lean_object* v_p_1161_, lean_object* v_passes_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(v_targetName_1159_, v_occurrence_1160_, v_p_1161_, v_passes_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass(uint8_t v_phase_1167_, lean_object* v_targetName_1168_, lean_object* v_p_1169_, lean_object* v_occurrence_1170_){
_start:
{
lean_object* v___f_1171_; lean_object* v___x_1172_; 
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1171_, 0, v_targetName_1168_);
lean_closure_set(v___f_1171_, 1, v_occurrence_1170_);
lean_closure_set(v___f_1171_, 2, v_p_1169_);
v___x_1172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1172_, 0, v___f_1171_);
lean_ctor_set_uint8(v___x_1172_, sizeof(void*)*1, v_phase_1167_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___boxed(lean_object* v_phase_1173_, lean_object* v_targetName_1174_, lean_object* v_p_1175_, lean_object* v_occurrence_1176_){
_start:
{
uint8_t v_phase_boxed_1177_; lean_object* v_res_1178_; 
v_phase_boxed_1177_ = lean_unbox(v_phase_1173_);
v_res_1178_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_boxed_1177_, v_targetName_1174_, v_p_1175_, v_occurrence_1176_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(uint8_t v_phase_1179_, lean_object* v_targetName_1180_, lean_object* v_p_1181_, lean_object* v_x_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_1179_, v_targetName_1180_, v_p_1181_, v_x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed(lean_object* v_phase_1184_, lean_object* v_targetName_1185_, lean_object* v_p_1186_, lean_object* v_x_1187_){
_start:
{
uint8_t v_phase_boxed_1188_; lean_object* v_res_1189_; 
v_phase_boxed_1188_ = lean_unbox(v_phase_1184_);
v_res_1189_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(v_phase_boxed_1188_, v_targetName_1185_, v_p_1186_, v_x_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(uint8_t v_phase_1190_, lean_object* v_targetName_1191_, lean_object* v_p_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; 
v___x_1193_ = lean_box(v_phase_1190_);
lean_inc(v_targetName_1191_);
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1194_, 0, v___x_1193_);
lean_closure_set(v___f_1194_, 1, v_targetName_1191_);
lean_closure_set(v___f_1194_, 2, v_p_1192_);
v___x_1195_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1190_, v_targetName_1191_, v___f_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___boxed(lean_object* v_phase_1196_, lean_object* v_targetName_1197_, lean_object* v_p_1198_){
_start:
{
uint8_t v_phase_boxed_1199_; lean_object* v_res_1200_; 
v_phase_boxed_1199_ = lean_unbox(v_phase_1196_);
v_res_1200_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(v_phase_boxed_1199_, v_targetName_1197_, v_p_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run(lean_object* v_manager_1201_, lean_object* v_installer_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
uint8_t v_phase_1206_; 
v_phase_1206_ = lean_ctor_get_uint8(v_installer_1202_, sizeof(void*)*1);
switch(v_phase_1206_)
{
case 0:
{
lean_object* v_install_1207_; lean_object* v_basePasses_1208_; lean_object* v_monoPasses_1209_; lean_object* v_monoPassesNoLambda_1210_; lean_object* v_impurePasses_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1235_; 
v_install_1207_ = lean_ctor_get(v_installer_1202_, 0);
lean_inc_ref(v_install_1207_);
lean_dec_ref(v_installer_1202_);
v_basePasses_1208_ = lean_ctor_get(v_manager_1201_, 0);
v_monoPasses_1209_ = lean_ctor_get(v_manager_1201_, 1);
v_monoPassesNoLambda_1210_ = lean_ctor_get(v_manager_1201_, 2);
v_impurePasses_1211_ = lean_ctor_get(v_manager_1201_, 3);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_manager_1201_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1213_ = v_manager_1201_;
v_isShared_1214_ = v_isSharedCheck_1235_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_impurePasses_1211_);
lean_inc(v_monoPassesNoLambda_1210_);
lean_inc(v_monoPasses_1209_);
lean_inc(v_basePasses_1208_);
lean_dec(v_manager_1201_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1235_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; 
lean_inc(v_a_1204_);
lean_inc_ref(v_a_1203_);
v___x_1215_ = lean_apply_4(v_install_1207_, v_basePasses_1208_, v_a_1203_, v_a_1204_, lean_box(0));
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1226_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1226_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1226_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_a_1216_);
v___x_1221_ = v___x_1213_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1216_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_monoPasses_1209_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_monoPassesNoLambda_1210_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_impurePasses_1211_);
v___x_1221_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1223_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1221_);
v___x_1223_ = v___x_1218_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_del_object(v___x_1213_);
lean_dec_ref(v_impurePasses_1211_);
lean_dec_ref(v_monoPassesNoLambda_1210_);
lean_dec_ref(v_monoPasses_1209_);
v_a_1227_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1215_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1215_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
case 1:
{
lean_object* v_install_1236_; lean_object* v_basePasses_1237_; lean_object* v_monoPasses_1238_; lean_object* v_monoPassesNoLambda_1239_; lean_object* v_impurePasses_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1264_; 
v_install_1236_ = lean_ctor_get(v_installer_1202_, 0);
lean_inc_ref(v_install_1236_);
lean_dec_ref(v_installer_1202_);
v_basePasses_1237_ = lean_ctor_get(v_manager_1201_, 0);
v_monoPasses_1238_ = lean_ctor_get(v_manager_1201_, 1);
v_monoPassesNoLambda_1239_ = lean_ctor_get(v_manager_1201_, 2);
v_impurePasses_1240_ = lean_ctor_get(v_manager_1201_, 3);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_manager_1201_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1242_ = v_manager_1201_;
v_isShared_1243_ = v_isSharedCheck_1264_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_impurePasses_1240_);
lean_inc(v_monoPassesNoLambda_1239_);
lean_inc(v_monoPasses_1238_);
lean_inc(v_basePasses_1237_);
lean_dec(v_manager_1201_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1264_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; 
lean_inc(v_a_1204_);
lean_inc_ref(v_a_1203_);
v___x_1244_ = lean_apply_4(v_install_1236_, v_monoPasses_1238_, v_a_1203_, v_a_1204_, lean_box(0));
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1255_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1255_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v_a_1245_);
v___x_1250_ = v___x_1242_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_basePasses_1237_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_a_1245_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_monoPassesNoLambda_1239_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_impurePasses_1240_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_del_object(v___x_1242_);
lean_dec_ref(v_impurePasses_1240_);
lean_dec_ref(v_monoPassesNoLambda_1239_);
lean_dec_ref(v_basePasses_1237_);
v_a_1256_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1244_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1244_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
default: 
{
lean_object* v_install_1265_; lean_object* v_basePasses_1266_; lean_object* v_monoPasses_1267_; lean_object* v_monoPassesNoLambda_1268_; lean_object* v_impurePasses_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1293_; 
v_install_1265_ = lean_ctor_get(v_installer_1202_, 0);
lean_inc_ref(v_install_1265_);
lean_dec_ref(v_installer_1202_);
v_basePasses_1266_ = lean_ctor_get(v_manager_1201_, 0);
v_monoPasses_1267_ = lean_ctor_get(v_manager_1201_, 1);
v_monoPassesNoLambda_1268_ = lean_ctor_get(v_manager_1201_, 2);
v_impurePasses_1269_ = lean_ctor_get(v_manager_1201_, 3);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_manager_1201_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1271_ = v_manager_1201_;
v_isShared_1272_ = v_isSharedCheck_1293_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_impurePasses_1269_);
lean_inc(v_monoPassesNoLambda_1268_);
lean_inc(v_monoPasses_1267_);
lean_inc(v_basePasses_1266_);
lean_dec(v_manager_1201_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1293_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; 
lean_inc(v_a_1204_);
lean_inc_ref(v_a_1203_);
v___x_1273_ = lean_apply_4(v_install_1265_, v_impurePasses_1269_, v_a_1203_, v_a_1204_, lean_box(0));
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1284_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1284_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1284_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 3, v_a_1274_);
v___x_1279_ = v___x_1271_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_basePasses_1266_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_monoPasses_1267_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_monoPassesNoLambda_1268_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1281_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1279_);
v___x_1281_ = v___x_1276_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_del_object(v___x_1271_);
lean_dec_ref(v_monoPassesNoLambda_1268_);
lean_dec_ref(v_monoPasses_1267_);
lean_dec_ref(v_basePasses_1266_);
v_a_1285_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1273_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1273_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run___boxed(lean_object* v_manager_1294_, lean_object* v_installer_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1294_, v_installer_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(lean_object* v_x_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_a_1304_ = lean_ctor_get(v_x_1300_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v_x_1300_, 1);
v___x_1305_ = l_Lean_stringToMessageData(v_a_1304_);
v___x_1306_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1305_, v___y_1301_, v___y_1302_);
return v___x_1306_;
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_a_1307_ = lean_ctor_get(v_x_1300_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_x_1300_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v_x_1300_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v_x_1300_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 0);
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg___boxed(lean_object* v_x_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(lean_object* v_declName_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_){
_start:
{
lean_object* v___x_1332_; lean_object* v_toCold_1333_; lean_object* v_env_1334_; lean_object* v_options_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1332_ = lean_st_ref_get(v_a_1330_);
v_toCold_1333_ = lean_ctor_get(v_a_1329_, 0);
v_env_1334_ = lean_ctor_get(v___x_1332_, 0);
lean_inc_ref(v_env_1334_);
lean_dec(v___x_1332_);
v_options_1335_ = lean_ctor_get(v_toCold_1333_, 2);
v___x_1336_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3));
v___x_1337_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1334_, v_options_1335_, v___x_1336_, v_declName_1328_);
v___x_1338_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v___x_1337_, v_a_1329_, v_a_1330_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___boxed(lean_object* v_declName_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1339_, v_a_1340_, v_a_1341_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(lean_object* v_00_u03b1_1344_, lean_object* v_x_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1345_, v___y_1346_, v___y_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_x_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(v_00_u03b1_1350_, v_x_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object* v_manager_1356_, lean_object* v_declName_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1357_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1363_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1356_, v_a_1362_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = l_Lean_Compiler_LCNF_PassManager_validate(v_a_1364_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v___x_1365_, 0);
lean_dec(v_unused_1373_);
v___x_1367_ = v___x_1365_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_dec(v___x_1365_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v_a_1364_);
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1364_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v_a_1364_);
v_a_1374_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1365_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1365_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
return v___x_1363_;
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v_manager_1356_);
v_a_1382_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1361_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1361_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl___boxed(lean_object* v_manager_1390_, lean_object* v_declName_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_manager_1390_, v_declName_1391_, v_a_1392_, v_a_1393_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
return v_res_1395_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_instLTPhase = _init_l_Lean_Compiler_LCNF_instLTPhase();
lean_mark_persistent(l_Lean_Compiler_LCNF_instLTPhase);
l_Lean_Compiler_LCNF_instLEPhase = _init_l_Lean_Compiler_LCNF_instLEPhase();
lean_mark_persistent(l_Lean_Compiler_LCNF_instLEPhase);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam = _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam();
lean_mark_persistent(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_PassManager(builtin);
}
#ifdef __cplusplus
}
#endif
