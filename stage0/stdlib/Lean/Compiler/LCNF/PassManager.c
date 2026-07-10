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
uint8_t l_Lean_Compiler_LCNF_instDecidableEqPhase(uint8_t, uint8_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
uint8_t l_Lean_Compiler_LCNF_instDecidableEqPurity(uint8_t, uint8_t);
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
uint8_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_pp_27_);
v___x_31_ = l_Lean_Compiler_LCNF_instDecidableEqPurity(v___x_30_, v_ip_28_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___y_37_; lean_object* v___y_38_; lean_object* v___x_44_; lean_object* v___y_46_; 
lean_dec(v_x_29_);
v___x_32_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0));
v___x_33_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1));
v___x_34_ = lean_unsigned_to_nat(33u);
v___x_35_ = lean_unsigned_to_nat(4u);
v___x_44_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3));
switch(v_pp_27_)
{
case 0:
{
lean_object* v___x_52_; 
v___x_52_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_46_ = v___x_52_;
goto v___jp_45_;
}
case 1:
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_46_ = v___x_53_;
goto v___jp_45_;
}
default: 
{
lean_object* v___x_54_; 
v___x_54_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_46_ = v___x_54_;
goto v___jp_45_;
}
}
v___jp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_39_ = lean_string_append(v___y_37_, v___y_38_);
v___x_40_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2));
v___x_41_ = lean_string_append(v___x_39_, v___x_40_);
v___x_42_ = l_mkPanicMessageWithDecl(v___x_32_, v___x_33_, v___x_34_, v___x_35_, v___x_41_);
lean_dec_ref(v___x_41_);
v___x_43_ = l_panic___redArg(v_inst_26_, v___x_42_);
return v___x_43_;
}
v___jp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_string_append(v___x_44_, v___y_46_);
v___x_48_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4));
v___x_49_ = lean_string_append(v___x_47_, v___x_48_);
if (v_ip_28_ == 0)
{
lean_object* v___x_50_; 
v___x_50_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5));
v___y_37_ = v___x_49_;
v___y_38_ = v___x_50_;
goto v___jp_36_;
}
else
{
lean_object* v___x_51_; 
v___x_51_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_37_ = v___x_49_;
v___y_38_ = v___x_51_;
goto v___jp_36_;
}
}
}
else
{
lean_object* v___x_55_; 
v___x_55_ = lean_apply_1(v_x_29_, lean_box(0));
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___boxed(lean_object* v_inst_56_, lean_object* v_pp_57_, lean_object* v_ip_58_, lean_object* v_x_59_){
_start:
{
uint8_t v_pp_boxed_60_; uint8_t v_ip_boxed_61_; lean_object* v_res_62_; 
v_pp_boxed_60_ = lean_unbox(v_pp_57_);
v_ip_boxed_61_ = lean_unbox(v_ip_58_);
v_res_62_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v_inst_56_, v_pp_boxed_60_, v_ip_boxed_61_, v_x_59_);
lean_dec(v_inst_56_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck(lean_object* v_00_u03b1_63_, lean_object* v_inst_64_, uint8_t v_pp_65_, uint8_t v_ip_66_, lean_object* v_x_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v_inst_64_, v_pp_65_, v_ip_66_, v_x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___boxed(lean_object* v_00_u03b1_69_, lean_object* v_inst_70_, lean_object* v_pp_71_, lean_object* v_ip_72_, lean_object* v_x_73_){
_start:
{
uint8_t v_pp_boxed_74_; uint8_t v_ip_boxed_75_; lean_object* v_res_76_; 
v_pp_boxed_74_ = lean_unbox(v_pp_71_);
v_ip_boxed_75_ = lean_unbox(v_ip_72_);
v_res_76_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck(v_00_u03b1_69_, v_inst_70_, v_pp_boxed_74_, v_ip_boxed_75_, v_x_73_);
lean_dec(v_inst_70_);
return v_res_76_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instLTPhase(void){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instLEPhase(void){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
return v___x_78_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableLtPhase(uint8_t v_p1_79_, uint8_t v_p2_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_81_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p1_79_);
v___x_82_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p2_80_);
v___x_83_ = lean_nat_dec_lt(v___x_81_, v___x_82_);
lean_dec(v___x_82_);
lean_dec(v___x_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableLtPhase___boxed(lean_object* v_p1_84_, lean_object* v_p2_85_){
_start:
{
uint8_t v_p1_boxed_86_; uint8_t v_p2_boxed_87_; uint8_t v_res_88_; lean_object* v_r_89_; 
v_p1_boxed_86_ = lean_unbox(v_p1_84_);
v_p2_boxed_87_ = lean_unbox(v_p2_85_);
v_res_88_ = l_Lean_Compiler_LCNF_instDecidableLtPhase(v_p1_boxed_86_, v_p2_boxed_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableLePhase(uint8_t v_p1_90_, uint8_t v_p2_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_92_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p1_90_);
v___x_93_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p2_91_);
v___x_94_ = lean_nat_dec_le(v___x_92_, v___x_93_);
lean_dec(v___x_93_);
lean_dec(v___x_92_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableLePhase___boxed(lean_object* v_p1_95_, lean_object* v_p2_96_){
_start:
{
uint8_t v_p1_boxed_97_; uint8_t v_p2_boxed_98_; uint8_t v_res_99_; lean_object* v_r_100_; 
v_p1_boxed_97_ = lean_unbox(v_p1_95_);
v_p2_boxed_98_ = lean_unbox(v_p2_96_);
v_res_99_ = l_Lean_Compiler_LCNF_instDecidableLePhase(v_p1_boxed_97_, v_p2_boxed_98_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10));
v___x_128_ = l_Lean_mkAtom(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12);
v___x_130_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_131_ = lean_array_push(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20));
v___x_152_ = l_Lean_mkAtom(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21);
v___x_154_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_155_ = lean_array_push(v___x_154_, v___x_153_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23));
v___x_158_ = lean_string_utf8_byte_size(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_159_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23));
v___x_162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
lean_ctor_set(v___x_162_, 2, v___x_159_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_165_ = lean_box(0);
v___x_166_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26));
v___x_167_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25);
v___x_168_ = lean_box(2);
v___x_169_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_166_);
lean_ctor_set(v___x_169_, 3, v___x_165_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27);
v___x_171_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22);
v___x_172_ = lean_array_push(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28);
v___x_174_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19));
v___x_175_ = lean_box(2);
v___x_176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_173_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29);
v___x_178_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_179_ = lean_array_push(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30);
v___x_181_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17));
v___x_182_ = lean_box(2);
v___x_183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
lean_ctor_set(v___x_183_, 2, v___x_180_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31);
v___x_185_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_186_ = lean_array_push(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33));
v___x_189_ = lean_string_utf8_byte_size(v___x_188_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_190_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33));
v___x_193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_191_);
lean_ctor_set(v___x_193_, 2, v___x_190_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_196_ = lean_box(0);
v___x_197_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36));
v___x_198_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35);
v___x_199_ = lean_box(2);
v___x_200_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v___x_198_);
lean_ctor_set(v___x_200_, 2, v___x_197_);
lean_ctor_set(v___x_200_, 3, v___x_196_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37);
v___x_202_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22);
v___x_203_ = lean_array_push(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_204_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38);
v___x_205_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19));
v___x_206_ = lean_box(2);
v___x_207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_205_);
lean_ctor_set(v___x_207_, 2, v___x_204_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39);
v___x_209_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_210_ = lean_array_push(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_211_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40);
v___x_212_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17));
v___x_213_ = lean_box(2);
v___x_214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
lean_ctor_set(v___x_214_, 2, v___x_211_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41);
v___x_216_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32);
v___x_217_ = lean_array_push(v___x_216_, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_218_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42);
v___x_219_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9));
v___x_220_ = lean_box(2);
v___x_221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
lean_ctor_set(v___x_221_, 2, v___x_218_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43);
v___x_223_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_224_ = lean_array_push(v___x_223_, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_225_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44);
v___x_226_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15));
v___x_227_ = lean_box(2);
v___x_228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
lean_ctor_set(v___x_228_, 2, v___x_225_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45);
v___x_230_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13);
v___x_231_ = lean_array_push(v___x_230_, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47));
v___x_237_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46);
v___x_238_ = lean_array_push(v___x_237_, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47));
v___x_240_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48);
v___x_241_ = lean_array_push(v___x_240_, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47));
v___x_243_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49);
v___x_244_ = lean_array_push(v___x_243_, v___x_242_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47));
v___x_246_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50);
v___x_247_ = lean_array_push(v___x_246_, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_248_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51);
v___x_249_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11));
v___x_250_ = lean_box(2);
v___x_251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
lean_ctor_set(v___x_251_, 2, v___x_248_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52);
v___x_253_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_254_ = lean_array_push(v___x_253_, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_255_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53);
v___x_256_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9));
v___x_257_ = lean_box(2);
v___x_258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
lean_ctor_set(v___x_258_, 2, v___x_255_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54);
v___x_260_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_261_ = lean_array_push(v___x_260_, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_262_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55);
v___x_263_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7));
v___x_264_ = lean_box(2);
v___x_265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
lean_ctor_set(v___x_265_, 2, v___x_262_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56);
v___x_267_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_268_ = lean_array_push(v___x_267_, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_269_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__57);
v___x_270_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4));
v___x_271_ = lean_box(2);
v___x_272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
lean_ctor_set(v___x_272_, 2, v___x_269_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__58);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(lean_object* v_decls_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v_decls_274_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___lam__0___boxed(lean_object* v_decls_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(v_decls_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___y_296_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___boxed(lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(lean_object* v_run_319_, size_t v_sz_320_, size_t v_i_321_, lean_object* v_bs_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_lt(v_i_321_, v_sz_320_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
lean_dec_ref(v_run_319_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v_bs_322_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0));
v___x_331_ = l_Lean_Core_checkSystem(v___x_330_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_v_332_; lean_object* v___x_333_; 
lean_dec_ref_known(v___x_331_, 1);
v_v_332_ = lean_array_uget_borrowed(v_bs_322_, v_i_321_);
lean_inc_ref(v_run_319_);
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
lean_inc(v___y_324_);
lean_inc_ref(v___y_323_);
lean_inc(v_v_332_);
v___x_333_ = lean_apply_6(v_run_319_, v_v_332_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, lean_box(0));
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v_bs_x27_336_; size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = lean_unsigned_to_nat(0u);
v_bs_x27_336_ = lean_array_uset(v_bs_322_, v_i_321_, v___x_335_);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_321_, v___x_337_);
v___x_339_ = lean_array_uset(v_bs_x27_336_, v_i_321_, v_a_334_);
v_i_321_ = v___x_338_;
v_bs_322_ = v___x_339_;
goto _start;
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec_ref(v_bs_322_);
lean_dec_ref(v_run_319_);
v_a_341_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_333_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_333_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v_bs_322_);
lean_dec_ref(v_run_319_);
v_a_349_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_331_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_331_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___boxed(lean_object* v_run_357_, lean_object* v_sz_358_, lean_object* v_i_359_, lean_object* v_bs_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
size_t v_sz_boxed_366_; size_t v_i_boxed_367_; lean_object* v_res_368_; 
v_sz_boxed_366_ = lean_unbox_usize(v_sz_358_);
lean_dec(v_sz_358_);
v_i_boxed_367_ = lean_unbox_usize(v_i_359_);
lean_dec(v_i_359_);
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_357_, v_sz_boxed_366_, v_i_boxed_367_, v_bs_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(lean_object* v_run_369_, lean_object* v_xs_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
size_t v_sz_376_; size_t v___x_377_; lean_object* v___x_378_; 
v_sz_376_ = lean_array_size(v_xs_370_);
v___x_377_ = ((size_t)0ULL);
v___x_378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_369_, v_sz_376_, v___x_377_, v_xs_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed(lean_object* v_run_379_, lean_object* v_xs_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(v_run_379_, v_xs_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object* v_name_387_, uint8_t v_phase_388_, lean_object* v_run_389_, lean_object* v_occurrence_390_){
_start:
{
lean_object* v___f_391_; uint8_t v___x_392_; lean_object* v___x_393_; 
v___f_391_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed), 7, 1);
lean_closure_set(v___f_391_, 0, v_run_389_);
v___x_392_ = 0;
v___x_393_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_393_, 0, v_occurrence_390_);
lean_ctor_set(v___x_393_, 1, v_name_387_);
lean_ctor_set(v___x_393_, 2, v___f_391_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*3, v_phase_388_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*3 + 1, v_phase_388_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*3 + 2, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___boxed(lean_object* v_name_394_, lean_object* v_phase_395_, lean_object* v_run_396_, lean_object* v_occurrence_397_){
_start:
{
uint8_t v_phase_boxed_398_; lean_object* v_res_399_; 
v_phase_boxed_398_ = lean_unbox(v_phase_395_);
v_res_399_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v_name_394_, v_phase_boxed_398_, v_run_396_, v_occurrence_397_);
return v_res_399_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_400_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0);
v___x_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
lean_ctor_set(v___x_405_, 2, v___x_404_);
lean_ctor_set(v___x_405_, 3, v___x_404_);
lean_ctor_set(v___x_405_, 4, v___x_403_);
lean_ctor_set(v___x_405_, 5, v___x_403_);
lean_ctor_set(v___x_405_, 6, v___x_403_);
lean_ctor_set(v___x_405_, 7, v___x_403_);
lean_ctor_set(v___x_405_, 8, v___x_403_);
lean_ctor_set(v___x_405_, 9, v___x_403_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_unsigned_to_nat(32u);
v___x_407_ = lean_mk_empty_array_with_capacity(v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_409_ = ((size_t)5ULL);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_unsigned_to_nat(32u);
v___x_412_ = lean_mk_empty_array_with_capacity(v___x_411_);
v___x_413_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3);
v___x_414_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_412_);
lean_ctor_set(v___x_414_, 2, v___x_410_);
lean_ctor_set(v___x_414_, 3, v___x_410_);
lean_ctor_set_usize(v___x_414_, 4, v___x_409_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = lean_box(1);
v___x_416_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4);
v___x_417_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
v___x_418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
lean_ctor_set(v___x_418_, 2, v___x_415_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(lean_object* v_msgData_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; lean_object* v_env_424_; lean_object* v_options_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_423_ = lean_st_ref_get(v___y_421_);
v_env_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_env_424_);
lean_dec(v___x_423_);
v_options_425_ = lean_ctor_get(v___y_420_, 2);
v___x_426_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2);
v___x_427_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_425_);
v___x_428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_428_, 0, v_env_424_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_427_);
lean_ctor_set(v___x_428_, 3, v_options_425_);
v___x_429_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_msgData_419_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___boxed(lean_object* v_msgData_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msgData_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(lean_object* v_msg_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_ref_440_; lean_object* v___x_441_; lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_ref_440_ = lean_ctor_get(v___y_437_, 5);
v___x_441_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msg_436_, v___y_437_, v___y_438_);
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
lean_inc(v_ref_440_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_ref_440_);
lean_ctor_set(v___x_446_, 1, v_a_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 1);
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg___boxed(lean_object* v_msg_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(uint8_t v_phase_458_, lean_object* v_as_459_, size_t v_sz_460_, size_t v_i_461_, lean_object* v_b_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_a_467_; uint8_t v___x_471_; 
v___x_471_ = lean_usize_dec_lt(v_i_461_, v_sz_460_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v_b_462_);
return v___x_472_;
}
else
{
lean_object* v_a_473_; uint8_t v_phase_474_; lean_object* v_name_475_; lean_object* v___x_476_; lean_object* v___y_478_; lean_object* v___y_479_; uint8_t v___x_484_; uint8_t v___x_485_; 
v_a_473_ = lean_array_uget_borrowed(v_as_459_, v_i_461_);
v_phase_474_ = lean_ctor_get_uint8(v_a_473_, sizeof(void*)*3);
v_name_475_ = lean_ctor_get(v_a_473_, 1);
v___x_476_ = lean_box(0);
v___x_484_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_phase_474_, v_phase_458_);
v___x_485_ = lean_bool_not(v___x_484_);
if (v___x_485_ == 0)
{
v_a_467_ = v___x_476_;
goto v___jp_466_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___y_490_; 
lean_inc(v_name_475_);
v___x_486_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_475_, v___x_485_);
v___x_487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0));
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
switch(v_phase_474_)
{
case 0:
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_490_ = v___x_497_;
goto v___jp_489_;
}
case 1:
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_490_ = v___x_498_;
goto v___jp_489_;
}
default: 
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_490_ = v___x_499_;
goto v___jp_489_;
}
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_string_append(v___x_488_, v___y_490_);
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1));
v___x_493_ = lean_string_append(v___x_491_, v___x_492_);
switch(v_phase_458_)
{
case 0:
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_478_ = v___x_493_;
v___y_479_ = v___x_494_;
goto v___jp_477_;
}
case 1:
{
lean_object* v___x_495_; 
v___x_495_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_478_ = v___x_493_;
v___y_479_ = v___x_495_;
goto v___jp_477_;
}
default: 
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_478_ = v___x_493_;
v___y_479_ = v___x_496_;
goto v___jp_477_;
}
}
}
}
v___jp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_480_ = lean_string_append(v___y_478_, v___y_479_);
v___x_481_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
v___x_482_ = l_Lean_MessageData_ofFormat(v___x_481_);
v___x_483_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_482_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_dec_ref_known(v___x_483_, 1);
v_a_467_ = v___x_476_;
goto v___jp_466_;
}
else
{
return v___x_483_;
}
}
}
v___jp_466_:
{
size_t v___x_468_; size_t v___x_469_; 
v___x_468_ = ((size_t)1ULL);
v___x_469_ = lean_usize_add(v_i_461_, v___x_468_);
v_i_461_ = v___x_469_;
v_b_462_ = v_a_467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___boxed(lean_object* v_phase_500_, lean_object* v_as_501_, lean_object* v_sz_502_, lean_object* v_i_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v_phase_boxed_508_; size_t v_sz_boxed_509_; size_t v_i_boxed_510_; lean_object* v_res_511_; 
v_phase_boxed_508_ = lean_unbox(v_phase_500_);
v_sz_boxed_509_ = lean_unbox_usize(v_sz_502_);
lean_dec(v_sz_502_);
v_i_boxed_510_ = lean_unbox_usize(v_i_503_);
lean_dec(v_i_503_);
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_boxed_508_, v_as_501_, v_sz_boxed_509_, v_i_boxed_510_, v_b_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec_ref(v_as_501_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(uint8_t v_phase_512_, lean_object* v_passes_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___x_517_; size_t v_sz_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_517_ = lean_box(0);
v_sz_518_ = lean_array_size(v_passes_513_);
v___x_519_ = ((size_t)0ULL);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_512_, v_passes_513_, v_sz_518_, v___x_519_, v___x_517_, v_a_514_, v_a_515_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v___x_520_, 0);
lean_dec(v_unused_528_);
v___x_522_ = v___x_520_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_dec(v___x_520_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_517_);
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_517_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses___boxed(lean_object* v_phase_529_, lean_object* v_passes_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
uint8_t v_phase_boxed_534_; lean_object* v_res_535_; 
v_phase_boxed_534_ = lean_unbox(v_phase_529_);
v_res_535_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v_phase_boxed_534_, v_passes_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec_ref(v_passes_530_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(lean_object* v_00_u03b1_536_, lean_object* v_msg_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_537_, v___y_538_, v___y_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___boxed(lean_object* v_00_u03b1_542_, lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(v_00_u03b1_542_, v_msg_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_validate(lean_object* v_manager_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_basePasses_552_; lean_object* v_monoPasses_553_; lean_object* v_monoPassesNoLambda_554_; uint8_t v___x_555_; lean_object* v___x_556_; 
v_basePasses_552_ = lean_ctor_get(v_manager_548_, 0);
v_monoPasses_553_ = lean_ctor_get(v_manager_548_, 1);
v_monoPassesNoLambda_554_ = lean_ctor_get(v_manager_548_, 2);
v___x_555_ = 0;
v___x_556_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_555_, v_basePasses_552_, v_a_549_, v_a_550_);
if (lean_obj_tag(v___x_556_) == 0)
{
uint8_t v___x_557_; lean_object* v___x_558_; 
lean_dec_ref_known(v___x_556_, 1);
v___x_557_ = 1;
v___x_558_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_557_, v_monoPasses_553_, v_a_549_, v_a_550_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; 
lean_dec_ref_known(v___x_558_, 1);
v___x_559_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_557_, v_monoPassesNoLambda_554_, v_a_549_, v_a_550_);
return v___x_559_;
}
else
{
return v___x_558_;
}
}
else
{
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_validate___boxed(lean_object* v_manager_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Compiler_LCNF_PassManager_validate(v_manager_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec_ref(v_manager_560_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(lean_object* v_targetName_565_, lean_object* v_as_566_, size_t v_sz_567_, size_t v_i_568_, lean_object* v_b_569_){
_start:
{
lean_object* v_a_572_; uint8_t v___x_576_; 
v___x_576_ = lean_usize_dec_lt(v_i_568_, v_sz_567_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v_b_569_);
return v___x_577_;
}
else
{
lean_object* v_fst_578_; lean_object* v_snd_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_596_; 
v_fst_578_ = lean_ctor_get(v_b_569_, 0);
v_snd_579_ = lean_ctor_get(v_b_569_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_b_569_);
if (v_isSharedCheck_596_ == 0)
{
v___x_581_ = v_b_569_;
v_isShared_582_ = v_isSharedCheck_596_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_snd_579_);
lean_inc(v_fst_578_);
lean_dec(v_b_569_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_596_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_a_583_; lean_object* v___y_585_; lean_object* v_occurrence_591_; lean_object* v_name_592_; uint8_t v___x_593_; 
v_a_583_ = lean_array_uget_borrowed(v_as_566_, v_i_568_);
v_occurrence_591_ = lean_ctor_get(v_a_583_, 0);
v_name_592_ = lean_ctor_get(v_a_583_, 1);
v___x_593_ = lean_name_eq(v_name_592_, v_targetName_565_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
lean_del_object(v___x_581_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_fst_578_);
lean_ctor_set(v___x_594_, 1, v_snd_579_);
v_a_572_ = v___x_594_;
goto v___jp_571_;
}
else
{
lean_dec(v_snd_579_);
if (lean_obj_tag(v_fst_578_) == 0)
{
if (v___x_593_ == 0)
{
v___y_585_ = v_fst_578_;
goto v___jp_584_;
}
else
{
lean_object* v___x_595_; 
lean_inc(v_occurrence_591_);
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v_occurrence_591_);
v___y_585_ = v___x_595_;
goto v___jp_584_;
}
}
else
{
v___y_585_ = v_fst_578_;
goto v___jp_584_;
}
}
v___jp_584_:
{
lean_object* v_occurrence_586_; lean_object* v___x_587_; lean_object* v___x_589_; 
v_occurrence_586_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_occurrence_586_);
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v_occurrence_586_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v___x_587_);
lean_ctor_set(v___x_581_, 0, v___y_585_);
v___x_589_ = v___x_581_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___y_585_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
v_a_572_ = v___x_589_;
goto v___jp_571_;
}
}
}
}
v___jp_571_:
{
size_t v___x_573_; size_t v___x_574_; 
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_568_, v___x_573_);
v_i_568_ = v___x_574_;
v_b_569_ = v_a_572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg___boxed(lean_object* v_targetName_597_, lean_object* v_as_598_, lean_object* v_sz_599_, lean_object* v_i_600_, lean_object* v_b_601_, lean_object* v___y_602_){
_start:
{
size_t v_sz_boxed_603_; size_t v_i_boxed_604_; lean_object* v_res_605_; 
v_sz_boxed_603_ = lean_unbox_usize(v_sz_599_);
lean_dec(v_sz_599_);
v_i_boxed_604_ = lean_unbox_usize(v_i_600_);
lean_dec(v_i_600_);
v_res_605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_597_, v_as_598_, v_sz_boxed_603_, v_i_boxed_604_, v_b_601_);
lean_dec_ref(v_as_598_);
lean_dec(v_targetName_597_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(lean_object* v_targetName_609_, lean_object* v_passes_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___x_624_; size_t v_sz_625_; size_t v___x_626_; lean_object* v___x_627_; 
v___x_624_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1));
v_sz_625_ = lean_array_size(v_passes_610_);
v___x_626_ = ((size_t)0ULL);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_609_, v_passes_610_, v_sz_625_, v___x_626_, v___x_624_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_647_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_647_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_647_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_647_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_fst_632_; 
v_fst_632_ = lean_ctor_get(v_a_628_, 0);
lean_inc(v_fst_632_);
if (lean_obj_tag(v_fst_632_) == 1)
{
lean_object* v_snd_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_645_; 
v_snd_633_ = lean_ctor_get(v_a_628_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_a_628_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v_a_628_, 0);
lean_dec(v_unused_646_);
v___x_635_ = v_a_628_;
v_isShared_636_ = v_isSharedCheck_645_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_snd_633_);
lean_dec(v_a_628_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_645_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
if (lean_obj_tag(v_snd_633_) == 1)
{
lean_object* v_val_637_; lean_object* v_val_638_; lean_object* v___x_640_; 
lean_dec(v_targetName_609_);
v_val_637_ = lean_ctor_get(v_fst_632_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v_fst_632_, 1);
v_val_638_ = lean_ctor_get(v_snd_633_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v_snd_633_, 1);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v_val_638_);
lean_ctor_set(v___x_635_, 0, v_val_637_);
v___x_640_ = v___x_635_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_val_637_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_val_638_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_640_);
v___x_642_ = v___x_630_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
else
{
lean_del_object(v___x_635_);
lean_dec_ref_known(v_fst_632_, 1);
lean_dec(v_snd_633_);
lean_del_object(v___x_630_);
v___y_615_ = v_a_611_;
v___y_616_ = v_a_612_;
goto v___jp_614_;
}
}
}
else
{
lean_dec(v_fst_632_);
lean_del_object(v___x_630_);
lean_dec(v_a_628_);
v___y_615_ = v_a_611_;
v___y_616_ = v_a_612_;
goto v___jp_614_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_targetName_609_);
v_a_648_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_627_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_627_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
v___jp_614_:
{
lean_object* v___x_617_; uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_617_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0));
v___x_618_ = 1;
v___x_619_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_609_, v___x_618_);
v___x_620_ = lean_string_append(v___x_617_, v___x_619_);
lean_dec_ref(v___x_619_);
v___x_621_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
v___x_622_ = l_Lean_MessageData_ofFormat(v___x_621_);
v___x_623_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_622_, v___y_615_, v___y_616_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___boxed(lean_object* v_targetName_656_, lean_object* v_passes_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(v_targetName_656_, v_passes_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec_ref(v_passes_657_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(lean_object* v_targetName_662_, lean_object* v_as_663_, size_t v_sz_664_, size_t v_i_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_662_, v_as_663_, v_sz_664_, v_i_665_, v_b_666_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___boxed(lean_object* v_targetName_671_, lean_object* v_as_672_, lean_object* v_sz_673_, lean_object* v_i_674_, lean_object* v_b_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
size_t v_sz_boxed_679_; size_t v_i_boxed_680_; lean_object* v_res_681_; 
v_sz_boxed_679_ = lean_unbox_usize(v_sz_673_);
lean_dec(v_sz_673_);
v_i_boxed_680_ = lean_unbox_usize(v_i_674_);
lean_dec(v_i_674_);
v_res_681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(v_targetName_671_, v_as_672_, v_sz_boxed_679_, v_i_boxed_680_, v_b_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v_as_672_);
lean_dec(v_targetName_671_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(lean_object* v_p_682_, lean_object* v_passes_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_array_push(v_passes_683_, v_p_682_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed(lean_object* v_p_689_, lean_object* v_passes_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(v_p_689_, v_passes_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(uint8_t v_phase_695_, lean_object* v_p_696_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; 
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_697_, 0, v_p_696_);
v___x_698_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_698_, 0, v___f_697_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*1, v_phase_695_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___boxed(lean_object* v_phase_699_, lean_object* v_p_700_){
_start:
{
uint8_t v_phase_boxed_701_; lean_object* v_res_702_; 
v_phase_boxed_701_ = lean_unbox(v_phase_699_);
v_res_702_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(v_phase_boxed_701_, v_p_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(lean_object* v_passesNew_703_, lean_object* v_passes_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = l_Array_append___redArg(v_passes_704_, v_passesNew_703_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed(lean_object* v_passesNew_710_, lean_object* v_passes_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(v_passesNew_710_, v_passes_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec_ref(v_passesNew_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append(uint8_t v_phase_716_, lean_object* v_passesNew_717_){
_start:
{
lean_object* v___f_718_; lean_object* v___x_719_; 
v___f_718_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed), 5, 1);
lean_closure_set(v___f_718_, 0, v_passesNew_717_);
v___x_719_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_719_, 0, v___f_718_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*1, v_phase_716_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___boxed(lean_object* v_phase_720_, lean_object* v_passesNew_721_){
_start:
{
uint8_t v_phase_boxed_722_; lean_object* v_res_723_; 
v_phase_boxed_722_ = lean_unbox(v_phase_720_);
v_res_723_ = l_Lean_Compiler_LCNF_PassInstaller_append(v_phase_boxed_722_, v_passesNew_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(lean_object* v_msg_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___f_729_; lean_object* v___x_1608__overap_730_; lean_object* v___x_731_; 
v___f_729_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0));
v___x_1608__overap_730_ = lean_panic_fn_borrowed(v___f_729_, v_msg_725_);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
v___x_731_ = lean_apply_3(v___x_1608__overap_730_, v___y_726_, v___y_727_, lean_box(0));
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___boxed(lean_object* v_msg_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v_msg_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(lean_object* v_install_737_, lean_object* v_b_738_, lean_object* v_____r_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
v___x_743_ = lean_apply_4(v_install_737_, v_b_738_, v___y_740_, v___y_741_, lean_box(0));
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_752_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v_a_744_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
v_a_753_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_743_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_743_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0___boxed(lean_object* v_install_761_, lean_object* v_b_762_, lean_object* v_____r_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_761_, v_b_762_, v_____r_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_767_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_770_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1));
v___x_771_ = lean_unsigned_to_nat(8u);
v___x_772_ = lean_unsigned_to_nat(170u);
v___x_773_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0));
v___x_774_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0));
v___x_775_ = l_mkPanicMessageWithDecl(v___x_774_, v___x_773_, v___x_772_, v___x_771_, v___x_770_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(lean_object* v_upperBound_776_, lean_object* v_f_777_, uint8_t v_phase_778_, lean_object* v_a_779_, lean_object* v_b_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___y_785_; uint8_t v___x_807_; 
v___x_807_ = lean_nat_dec_le(v_a_779_, v_upperBound_776_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec(v_a_779_);
lean_dec_ref(v_f_777_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_b_780_);
return v___x_808_;
}
else
{
lean_object* v___x_809_; uint8_t v_phase_810_; lean_object* v_install_811_; uint8_t v___x_812_; uint8_t v___x_813_; 
lean_inc_ref(v_f_777_);
lean_inc(v_a_779_);
v___x_809_ = lean_apply_1(v_f_777_, v_a_779_);
v_phase_810_ = lean_ctor_get_uint8(v___x_809_, sizeof(void*)*1);
v_install_811_ = lean_ctor_get(v___x_809_, 0);
lean_inc_ref(v_install_811_);
lean_dec_ref(v___x_809_);
v___x_812_ = l_Lean_Compiler_LCNF_instDecidableEqPhase(v_phase_810_, v_phase_778_);
v___x_813_ = lean_bool_not(v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_box(0);
v___x_815_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_811_, v_b_780_, v___x_814_, v___y_781_, v___y_782_);
v___y_785_ = v___x_815_;
goto v___jp_784_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2);
v___x_817_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v___x_816_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_819_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v___x_819_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_811_, v_b_780_, v_a_818_, v___y_781_, v___y_782_);
v___y_785_ = v___x_819_;
goto v___jp_784_;
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v_install_811_);
lean_dec_ref(v_b_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_f_777_);
v_a_820_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_817_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_817_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
v___jp_784_:
{
if (lean_obj_tag(v___y_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_798_; 
v_a_786_ = lean_ctor_get(v___y_785_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___y_785_);
if (v_isSharedCheck_798_ == 0)
{
v___x_788_ = v___y_785_;
v_isShared_789_ = v_isSharedCheck_798_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___y_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_798_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
if (lean_obj_tag(v_a_786_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; 
lean_dec(v_a_779_);
lean_dec_ref(v_f_777_);
v_a_790_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v_a_786_, 1);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v_a_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_del_object(v___x_788_);
v_a_794_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v_a_786_, 1);
v___x_795_ = lean_unsigned_to_nat(1u);
v___x_796_ = lean_nat_add(v_a_779_, v___x_795_);
lean_dec(v_a_779_);
v_a_779_ = v___x_796_;
v_b_780_ = v_a_794_;
goto _start;
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_a_779_);
lean_dec_ref(v_f_777_);
v_a_799_ = lean_ctor_get(v___y_785_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___y_785_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___y_785_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___y_785_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___boxed(lean_object* v_upperBound_828_, lean_object* v_f_829_, lean_object* v_phase_830_, lean_object* v_a_831_, lean_object* v_b_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v_phase_boxed_836_; lean_object* v_res_837_; 
v_phase_boxed_836_ = lean_unbox(v_phase_830_);
v_res_837_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_828_, v_f_829_, v_phase_boxed_836_, v_a_831_, v_b_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v_upperBound_828_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(lean_object* v_targetName_838_, lean_object* v_f_839_, uint8_t v_phase_840_, lean_object* v_passes_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(v_targetName_838_, v_passes_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v_fst_847_; lean_object* v_snd_848_; lean_object* v___x_849_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v_fst_847_ = lean_ctor_get(v_a_846_, 0);
lean_inc(v_fst_847_);
v_snd_848_ = lean_ctor_get(v_a_846_, 1);
lean_inc(v_snd_848_);
lean_dec(v_a_846_);
v___x_849_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_snd_848_, v_f_839_, v_phase_840_, v_fst_847_, v_passes_841_, v___y_842_, v___y_843_);
lean_dec(v_snd_848_);
return v___x_849_;
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref(v_passes_841_);
lean_dec_ref(v_f_839_);
v_a_850_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_845_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_845_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed(lean_object* v_targetName_858_, lean_object* v_f_859_, lean_object* v_phase_860_, lean_object* v_passes_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint8_t v_phase_boxed_865_; lean_object* v_res_866_; 
v_phase_boxed_865_ = lean_unbox(v_phase_860_);
v_res_866_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(v_targetName_858_, v_f_859_, v_phase_boxed_865_, v_passes_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(uint8_t v_phase_867_, lean_object* v_targetName_868_, lean_object* v_f_869_){
_start:
{
lean_object* v___x_870_; lean_object* v___f_871_; lean_object* v___x_872_; 
v___x_870_ = lean_box(v_phase_867_);
v___f_871_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed), 7, 3);
lean_closure_set(v___f_871_, 0, v_targetName_868_);
lean_closure_set(v___f_871_, 1, v_f_869_);
lean_closure_set(v___f_871_, 2, v___x_870_);
v___x_872_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_872_, 0, v___f_871_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*1, v_phase_867_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___boxed(lean_object* v_phase_873_, lean_object* v_targetName_874_, lean_object* v_f_875_){
_start:
{
uint8_t v_phase_boxed_876_; lean_object* v_res_877_; 
v_phase_boxed_876_ = lean_unbox(v_phase_873_);
v_res_877_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_boxed_876_, v_targetName_874_, v_f_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(lean_object* v_upperBound_878_, lean_object* v_f_879_, uint8_t v_phase_880_, lean_object* v_inst_881_, lean_object* v_R_882_, lean_object* v_a_883_, lean_object* v_b_884_, lean_object* v_c_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_878_, v_f_879_, v_phase_880_, v_a_883_, v_b_884_, v___y_886_, v___y_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___boxed(lean_object* v_upperBound_890_, lean_object* v_f_891_, lean_object* v_phase_892_, lean_object* v_inst_893_, lean_object* v_R_894_, lean_object* v_a_895_, lean_object* v_b_896_, lean_object* v_c_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
uint8_t v_phase_boxed_901_; lean_object* v_res_902_; 
v_phase_boxed_901_ = lean_unbox(v_phase_892_);
v_res_902_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(v_upperBound_890_, v_f_891_, v_phase_boxed_901_, v_inst_893_, v_R_894_, v_a_895_, v_b_896_, v_c_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v_upperBound_890_);
return v_res_902_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(lean_object* v_targetName_903_, lean_object* v_occurrence_904_, lean_object* v_p_905_){
_start:
{
lean_object* v_occurrence_906_; lean_object* v_name_907_; uint8_t v___x_908_; 
v_occurrence_906_ = lean_ctor_get(v_p_905_, 0);
v_name_907_ = lean_ctor_get(v_p_905_, 1);
v___x_908_ = lean_name_eq(v_name_907_, v_targetName_903_);
if (v___x_908_ == 0)
{
return v___x_908_;
}
else
{
uint8_t v___x_909_; 
v___x_909_ = lean_nat_dec_eq(v_occurrence_906_, v_occurrence_904_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed(lean_object* v_targetName_910_, lean_object* v_occurrence_911_, lean_object* v_p_912_){
_start:
{
uint8_t v_res_913_; lean_object* v_r_914_; 
v_res_913_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(v_targetName_910_, v_occurrence_911_, v_p_912_);
lean_dec_ref(v_p_912_);
lean_dec(v_occurrence_911_);
lean_dec(v_targetName_910_);
v_r_914_ = lean_box(v_res_913_);
return v_r_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(lean_object* v___f_919_, lean_object* v_p_920_, lean_object* v_targetName_921_, lean_object* v_occurrence_922_, lean_object* v_passes_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_919_, v_passes_923_, v___x_927_);
if (lean_obj_tag(v___x_928_) == 1)
{
lean_object* v_val_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_occurrence_922_);
lean_dec(v_targetName_921_);
v_val_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_943_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_943_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_val_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_943_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_passUnderTest_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v_j_937_; lean_object* v_as_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v_passUnderTest_933_ = lean_array_fget_borrowed(v_passes_923_, v_val_929_);
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_add(v_val_929_, v___x_934_);
lean_dec(v_val_929_);
lean_inc(v_passUnderTest_933_);
v___x_936_ = lean_apply_1(v_p_920_, v_passUnderTest_933_);
v_j_937_ = lean_array_get_size(v_passes_923_);
v_as_938_ = lean_array_push(v_passes_923_, v___x_936_);
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_935_, v_as_938_, v_j_937_);
lean_dec(v___x_935_);
if (v_isShared_932_ == 0)
{
lean_ctor_set_tag(v___x_931_, 0);
lean_ctor_set(v___x_931_, 0, v___x_939_);
v___x_941_ = v___x_931_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v___x_928_);
lean_dec_ref(v_passes_923_);
lean_dec_ref(v_p_920_);
v___x_944_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0));
v___x_945_ = 1;
v___x_946_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_921_, v___x_945_);
v___x_947_ = lean_string_append(v___x_944_, v___x_946_);
v___x_948_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_949_ = lean_string_append(v___x_947_, v___x_948_);
v___x_950_ = l_Nat_reprFast(v_occurrence_922_);
v___x_951_ = lean_string_append(v___x_949_, v___x_950_);
lean_dec_ref(v___x_950_);
v___x_952_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_953_ = lean_string_append(v___x_951_, v___x_952_);
v___x_954_ = lean_string_append(v___x_953_, v___x_946_);
lean_dec_ref(v___x_946_);
v___x_955_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_956_ = lean_string_append(v___x_954_, v___x_955_);
v___x_957_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
v___x_958_ = l_Lean_MessageData_ofFormat(v___x_957_);
v___x_959_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_958_, v___y_924_, v___y_925_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed(lean_object* v___f_960_, lean_object* v_p_961_, lean_object* v_targetName_962_, lean_object* v_occurrence_963_, lean_object* v_passes_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(v___f_960_, v_p_961_, v_targetName_962_, v_occurrence_963_, v_passes_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter(uint8_t v_phase_969_, lean_object* v_targetName_970_, lean_object* v_p_971_, lean_object* v_occurrence_972_){
_start:
{
lean_object* v___f_973_; lean_object* v___f_974_; lean_object* v___x_975_; 
lean_inc(v_occurrence_972_);
lean_inc(v_targetName_970_);
v___f_973_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed), 3, 2);
lean_closure_set(v___f_973_, 0, v_targetName_970_);
lean_closure_set(v___f_973_, 1, v_occurrence_972_);
v___f_974_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed), 8, 4);
lean_closure_set(v___f_974_, 0, v___f_973_);
lean_closure_set(v___f_974_, 1, v_p_971_);
lean_closure_set(v___f_974_, 2, v_targetName_970_);
lean_closure_set(v___f_974_, 3, v_occurrence_972_);
v___x_975_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_975_, 0, v___f_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*1, v_phase_969_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___boxed(lean_object* v_phase_976_, lean_object* v_targetName_977_, lean_object* v_p_978_, lean_object* v_occurrence_979_){
_start:
{
uint8_t v_phase_boxed_980_; lean_object* v_res_981_; 
v_phase_boxed_980_ = lean_unbox(v_phase_976_);
v_res_981_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_boxed_980_, v_targetName_977_, v_p_978_, v_occurrence_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(uint8_t v_phase_982_, lean_object* v_targetName_983_, lean_object* v_p_984_, lean_object* v_x_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_982_, v_targetName_983_, v_p_984_, v_x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed(lean_object* v_phase_987_, lean_object* v_targetName_988_, lean_object* v_p_989_, lean_object* v_x_990_){
_start:
{
uint8_t v_phase_boxed_991_; lean_object* v_res_992_; 
v_phase_boxed_991_ = lean_unbox(v_phase_987_);
v_res_992_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(v_phase_boxed_991_, v_targetName_988_, v_p_989_, v_x_990_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(uint8_t v_phase_993_, lean_object* v_targetName_994_, lean_object* v_p_995_){
_start:
{
lean_object* v___x_996_; lean_object* v___f_997_; lean_object* v___x_998_; 
v___x_996_ = lean_box(v_phase_993_);
lean_inc(v_targetName_994_);
v___f_997_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed), 4, 3);
lean_closure_set(v___f_997_, 0, v___x_996_);
lean_closure_set(v___f_997_, 1, v_targetName_994_);
lean_closure_set(v___f_997_, 2, v_p_995_);
v___x_998_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_993_, v_targetName_994_, v___f_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___boxed(lean_object* v_phase_999_, lean_object* v_targetName_1000_, lean_object* v_p_1001_){
_start:
{
uint8_t v_phase_boxed_1002_; lean_object* v_res_1003_; 
v_phase_boxed_1002_ = lean_unbox(v_phase_999_);
v_res_1003_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(v_phase_boxed_1002_, v_targetName_1000_, v_p_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(lean_object* v___f_1004_, lean_object* v_p_1005_, lean_object* v_targetName_1006_, lean_object* v_occurrence_1007_, lean_object* v_passes_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1004_, v_passes_1008_, v___x_1012_);
if (lean_obj_tag(v___x_1013_) == 1)
{
lean_object* v_val_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v_occurrence_1007_);
lean_dec(v_targetName_1006_);
v_val_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1026_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_val_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1026_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_passUnderTest_1018_; lean_object* v___x_1019_; lean_object* v_j_1020_; lean_object* v_as_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v_passUnderTest_1018_ = lean_array_fget_borrowed(v_passes_1008_, v_val_1014_);
lean_inc(v_passUnderTest_1018_);
v___x_1019_ = lean_apply_1(v_p_1005_, v_passUnderTest_1018_);
v_j_1020_ = lean_array_get_size(v_passes_1008_);
v_as_1021_ = lean_array_push(v_passes_1008_, v___x_1019_);
v___x_1022_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_val_1014_, v_as_1021_, v_j_1020_);
lean_dec(v_val_1014_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1022_);
v___x_1024_ = v___x_1016_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_object* v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec(v___x_1013_);
lean_dec_ref(v_passes_1008_);
lean_dec_ref(v_p_1005_);
v___x_1027_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0));
v___x_1028_ = 1;
v___x_1029_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_1006_, v___x_1028_);
v___x_1030_ = lean_string_append(v___x_1027_, v___x_1029_);
v___x_1031_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_1032_ = lean_string_append(v___x_1030_, v___x_1031_);
v___x_1033_ = l_Nat_reprFast(v_occurrence_1007_);
v___x_1034_ = lean_string_append(v___x_1032_, v___x_1033_);
lean_dec_ref(v___x_1033_);
v___x_1035_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_1036_ = lean_string_append(v___x_1034_, v___x_1035_);
v___x_1037_ = lean_string_append(v___x_1036_, v___x_1029_);
lean_dec_ref(v___x_1029_);
v___x_1038_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_1039_ = lean_string_append(v___x_1037_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
v___x_1041_ = l_Lean_MessageData_ofFormat(v___x_1040_);
v___x_1042_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1041_, v___y_1009_, v___y_1010_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed(lean_object* v___f_1043_, lean_object* v_p_1044_, lean_object* v_targetName_1045_, lean_object* v_occurrence_1046_, lean_object* v_passes_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(v___f_1043_, v_p_1044_, v_targetName_1045_, v_occurrence_1046_, v_passes_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore(uint8_t v_phase_1052_, lean_object* v_targetName_1053_, lean_object* v_p_1054_, lean_object* v_occurrence_1055_){
_start:
{
lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; 
lean_inc(v_occurrence_1055_);
lean_inc(v_targetName_1053_);
v___f_1056_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1056_, 0, v_targetName_1053_);
lean_closure_set(v___f_1056_, 1, v_occurrence_1055_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1057_, 0, v___f_1056_);
lean_closure_set(v___f_1057_, 1, v_p_1054_);
lean_closure_set(v___f_1057_, 2, v_targetName_1053_);
lean_closure_set(v___f_1057_, 3, v_occurrence_1055_);
v___x_1058_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1058_, 0, v___f_1057_);
lean_ctor_set_uint8(v___x_1058_, sizeof(void*)*1, v_phase_1052_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___boxed(lean_object* v_phase_1059_, lean_object* v_targetName_1060_, lean_object* v_p_1061_, lean_object* v_occurrence_1062_){
_start:
{
uint8_t v_phase_boxed_1063_; lean_object* v_res_1064_; 
v_phase_boxed_1063_ = lean_unbox(v_phase_1059_);
v_res_1064_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_boxed_1063_, v_targetName_1060_, v_p_1061_, v_occurrence_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(uint8_t v_phase_1065_, lean_object* v_targetName_1066_, lean_object* v_p_1067_, lean_object* v_x_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_1065_, v_targetName_1066_, v_p_1067_, v_x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed(lean_object* v_phase_1070_, lean_object* v_targetName_1071_, lean_object* v_p_1072_, lean_object* v_x_1073_){
_start:
{
uint8_t v_phase_boxed_1074_; lean_object* v_res_1075_; 
v_phase_boxed_1074_ = lean_unbox(v_phase_1070_);
v_res_1075_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(v_phase_boxed_1074_, v_targetName_1071_, v_p_1072_, v_x_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(uint8_t v_phase_1076_, lean_object* v_targetName_1077_, lean_object* v_p_1078_){
_start:
{
lean_object* v___x_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(v_phase_1076_);
lean_inc(v_targetName_1077_);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1080_, 0, v___x_1079_);
lean_closure_set(v___f_1080_, 1, v_targetName_1077_);
lean_closure_set(v___f_1080_, 2, v_p_1078_);
v___x_1081_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1076_, v_targetName_1077_, v___f_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___boxed(lean_object* v_phase_1082_, lean_object* v_targetName_1083_, lean_object* v_p_1084_){
_start:
{
uint8_t v_phase_boxed_1085_; lean_object* v_res_1086_; 
v_phase_boxed_1085_ = lean_unbox(v_phase_1082_);
v_res_1086_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(v_phase_boxed_1085_, v_targetName_1083_, v_p_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(lean_object* v_targetName_1087_, lean_object* v_occurrence_1088_, lean_object* v_as_1089_, lean_object* v_j_1090_){
_start:
{
uint8_t v___y_1092_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_array_get_size(v_as_1089_);
v___x_1098_ = lean_nat_dec_lt(v_j_1090_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec(v_j_1090_);
v___x_1099_ = lean_box(0);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; lean_object* v_occurrence_1101_; lean_object* v_name_1102_; uint8_t v___x_1103_; 
v___x_1100_ = lean_array_fget_borrowed(v_as_1089_, v_j_1090_);
v_occurrence_1101_ = lean_ctor_get(v___x_1100_, 0);
v_name_1102_ = lean_ctor_get(v___x_1100_, 1);
v___x_1103_ = lean_name_eq(v_name_1102_, v_targetName_1087_);
if (v___x_1103_ == 0)
{
v___y_1092_ = v___x_1103_;
goto v___jp_1091_;
}
else
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_nat_dec_eq(v_occurrence_1101_, v_occurrence_1088_);
v___y_1092_ = v___x_1104_;
goto v___jp_1091_;
}
}
v___jp_1091_:
{
if (v___y_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_j_1090_, v___x_1093_);
lean_dec(v_j_1090_);
v_j_1090_ = v___x_1094_;
goto _start;
}
else
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_j_1090_);
return v___x_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0___boxed(lean_object* v_targetName_1105_, lean_object* v_occurrence_1106_, lean_object* v_as_1107_, lean_object* v_j_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_1105_, v_occurrence_1106_, v_as_1107_, v_j_1108_);
lean_dec_ref(v_as_1107_);
lean_dec(v_occurrence_1106_);
lean_dec(v_targetName_1105_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(lean_object* v_targetName_1111_, lean_object* v_occurrence_1112_, lean_object* v_p_1113_, lean_object* v_passes_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_unsigned_to_nat(0u);
v___x_1119_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_1111_, v_occurrence_1112_, v_passes_1114_, v___x_1118_);
if (lean_obj_tag(v___x_1119_) == 1)
{
lean_object* v_val_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_occurrence_1112_);
lean_dec(v_targetName_1111_);
v_val_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1137_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_val_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1137_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = lean_array_get_size(v_passes_1114_);
v___x_1125_ = lean_nat_dec_lt(v_val_1120_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1127_; 
lean_dec(v_val_1120_);
lean_dec_ref(v_p_1113_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 0);
lean_ctor_set(v___x_1122_, 0, v_passes_1114_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_passes_1114_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
lean_object* v_v_1129_; lean_object* v___x_1130_; lean_object* v_xs_x27_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v_v_1129_ = lean_array_fget(v_passes_1114_, v_val_1120_);
v___x_1130_ = lean_box(0);
v_xs_x27_1131_ = lean_array_fset(v_passes_1114_, v_val_1120_, v___x_1130_);
v___x_1132_ = lean_apply_1(v_p_1113_, v_v_1129_);
v___x_1133_ = lean_array_fset(v_xs_x27_1131_, v_val_1120_, v___x_1132_);
lean_dec(v_val_1120_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1133_);
v___x_1135_ = v___x_1122_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_object* v___x_1138_; uint8_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v___x_1119_);
lean_dec_ref(v_passes_1114_);
lean_dec_ref(v_p_1113_);
v___x_1138_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0));
v___x_1139_ = 1;
v___x_1140_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_1111_, v___x_1139_);
v___x_1141_ = lean_string_append(v___x_1138_, v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_1143_ = lean_string_append(v___x_1141_, v___x_1142_);
v___x_1144_ = l_Nat_reprFast(v_occurrence_1112_);
v___x_1145_ = lean_string_append(v___x_1143_, v___x_1144_);
lean_dec_ref(v___x_1144_);
v___x_1146_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_1147_ = lean_string_append(v___x_1145_, v___x_1146_);
v___x_1148_ = lean_string_append(v___x_1147_, v___x_1140_);
lean_dec_ref(v___x_1140_);
v___x_1149_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_1150_ = lean_string_append(v___x_1148_, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
v___x_1152_ = l_Lean_MessageData_ofFormat(v___x_1151_);
v___x_1153_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1152_, v___y_1115_, v___y_1116_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed(lean_object* v_targetName_1154_, lean_object* v_occurrence_1155_, lean_object* v_p_1156_, lean_object* v_passes_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(v_targetName_1154_, v_occurrence_1155_, v_p_1156_, v_passes_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass(uint8_t v_phase_1162_, lean_object* v_targetName_1163_, lean_object* v_p_1164_, lean_object* v_occurrence_1165_){
_start:
{
lean_object* v___f_1166_; lean_object* v___x_1167_; 
v___f_1166_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1166_, 0, v_targetName_1163_);
lean_closure_set(v___f_1166_, 1, v_occurrence_1165_);
lean_closure_set(v___f_1166_, 2, v_p_1164_);
v___x_1167_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1167_, 0, v___f_1166_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*1, v_phase_1162_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___boxed(lean_object* v_phase_1168_, lean_object* v_targetName_1169_, lean_object* v_p_1170_, lean_object* v_occurrence_1171_){
_start:
{
uint8_t v_phase_boxed_1172_; lean_object* v_res_1173_; 
v_phase_boxed_1172_ = lean_unbox(v_phase_1168_);
v_res_1173_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_boxed_1172_, v_targetName_1169_, v_p_1170_, v_occurrence_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(uint8_t v_phase_1174_, lean_object* v_targetName_1175_, lean_object* v_p_1176_, lean_object* v_x_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_1174_, v_targetName_1175_, v_p_1176_, v_x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed(lean_object* v_phase_1179_, lean_object* v_targetName_1180_, lean_object* v_p_1181_, lean_object* v_x_1182_){
_start:
{
uint8_t v_phase_boxed_1183_; lean_object* v_res_1184_; 
v_phase_boxed_1183_ = lean_unbox(v_phase_1179_);
v_res_1184_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(v_phase_boxed_1183_, v_targetName_1180_, v_p_1181_, v_x_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(uint8_t v_phase_1185_, lean_object* v_targetName_1186_, lean_object* v_p_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___f_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_box(v_phase_1185_);
lean_inc(v_targetName_1186_);
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1189_, 0, v___x_1188_);
lean_closure_set(v___f_1189_, 1, v_targetName_1186_);
lean_closure_set(v___f_1189_, 2, v_p_1187_);
v___x_1190_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1185_, v_targetName_1186_, v___f_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___boxed(lean_object* v_phase_1191_, lean_object* v_targetName_1192_, lean_object* v_p_1193_){
_start:
{
uint8_t v_phase_boxed_1194_; lean_object* v_res_1195_; 
v_phase_boxed_1194_ = lean_unbox(v_phase_1191_);
v_res_1195_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(v_phase_boxed_1194_, v_targetName_1192_, v_p_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run(lean_object* v_manager_1196_, lean_object* v_installer_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_){
_start:
{
uint8_t v_phase_1201_; 
v_phase_1201_ = lean_ctor_get_uint8(v_installer_1197_, sizeof(void*)*1);
switch(v_phase_1201_)
{
case 0:
{
lean_object* v_install_1202_; lean_object* v_basePasses_1203_; lean_object* v_monoPasses_1204_; lean_object* v_monoPassesNoLambda_1205_; lean_object* v_impurePasses_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1230_; 
v_install_1202_ = lean_ctor_get(v_installer_1197_, 0);
lean_inc_ref(v_install_1202_);
lean_dec_ref(v_installer_1197_);
v_basePasses_1203_ = lean_ctor_get(v_manager_1196_, 0);
v_monoPasses_1204_ = lean_ctor_get(v_manager_1196_, 1);
v_monoPassesNoLambda_1205_ = lean_ctor_get(v_manager_1196_, 2);
v_impurePasses_1206_ = lean_ctor_get(v_manager_1196_, 3);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_manager_1196_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1208_ = v_manager_1196_;
v_isShared_1209_ = v_isSharedCheck_1230_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_impurePasses_1206_);
lean_inc(v_monoPassesNoLambda_1205_);
lean_inc(v_monoPasses_1204_);
lean_inc(v_basePasses_1203_);
lean_dec(v_manager_1196_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1230_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; 
lean_inc(v_a_1199_);
lean_inc_ref(v_a_1198_);
v___x_1210_ = lean_apply_4(v_install_1202_, v_basePasses_1203_, v_a_1198_, v_a_1199_, lean_box(0));
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1221_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v_a_1211_);
v___x_1216_ = v___x_1208_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1211_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_monoPasses_1204_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_monoPassesNoLambda_1205_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v_impurePasses_1206_);
v___x_1216_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1218_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1216_);
v___x_1218_ = v___x_1213_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_del_object(v___x_1208_);
lean_dec_ref(v_impurePasses_1206_);
lean_dec_ref(v_monoPassesNoLambda_1205_);
lean_dec_ref(v_monoPasses_1204_);
v_a_1222_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1210_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1210_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
case 1:
{
lean_object* v_install_1231_; lean_object* v_basePasses_1232_; lean_object* v_monoPasses_1233_; lean_object* v_monoPassesNoLambda_1234_; lean_object* v_impurePasses_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1259_; 
v_install_1231_ = lean_ctor_get(v_installer_1197_, 0);
lean_inc_ref(v_install_1231_);
lean_dec_ref(v_installer_1197_);
v_basePasses_1232_ = lean_ctor_get(v_manager_1196_, 0);
v_monoPasses_1233_ = lean_ctor_get(v_manager_1196_, 1);
v_monoPassesNoLambda_1234_ = lean_ctor_get(v_manager_1196_, 2);
v_impurePasses_1235_ = lean_ctor_get(v_manager_1196_, 3);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_manager_1196_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1237_ = v_manager_1196_;
v_isShared_1238_ = v_isSharedCheck_1259_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_impurePasses_1235_);
lean_inc(v_monoPassesNoLambda_1234_);
lean_inc(v_monoPasses_1233_);
lean_inc(v_basePasses_1232_);
lean_dec(v_manager_1196_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1259_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; 
lean_inc(v_a_1199_);
lean_inc_ref(v_a_1198_);
v___x_1239_ = lean_apply_4(v_install_1231_, v_monoPasses_1233_, v_a_1198_, v_a_1199_, lean_box(0));
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1250_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v_a_1240_);
v___x_1245_ = v___x_1237_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_basePasses_1232_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_a_1240_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_monoPassesNoLambda_1234_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v_impurePasses_1235_);
v___x_1245_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1247_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1245_);
v___x_1247_ = v___x_1242_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_del_object(v___x_1237_);
lean_dec_ref(v_impurePasses_1235_);
lean_dec_ref(v_monoPassesNoLambda_1234_);
lean_dec_ref(v_basePasses_1232_);
v_a_1251_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1239_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1239_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
default: 
{
lean_object* v_install_1260_; lean_object* v_basePasses_1261_; lean_object* v_monoPasses_1262_; lean_object* v_monoPassesNoLambda_1263_; lean_object* v_impurePasses_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1288_; 
v_install_1260_ = lean_ctor_get(v_installer_1197_, 0);
lean_inc_ref(v_install_1260_);
lean_dec_ref(v_installer_1197_);
v_basePasses_1261_ = lean_ctor_get(v_manager_1196_, 0);
v_monoPasses_1262_ = lean_ctor_get(v_manager_1196_, 1);
v_monoPassesNoLambda_1263_ = lean_ctor_get(v_manager_1196_, 2);
v_impurePasses_1264_ = lean_ctor_get(v_manager_1196_, 3);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_manager_1196_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1266_ = v_manager_1196_;
v_isShared_1267_ = v_isSharedCheck_1288_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_impurePasses_1264_);
lean_inc(v_monoPassesNoLambda_1263_);
lean_inc(v_monoPasses_1262_);
lean_inc(v_basePasses_1261_);
lean_dec(v_manager_1196_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1288_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; 
lean_inc(v_a_1199_);
lean_inc_ref(v_a_1198_);
v___x_1268_ = lean_apply_4(v_install_1260_, v_impurePasses_1264_, v_a_1198_, v_a_1199_, lean_box(0));
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1279_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1279_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1279_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 3, v_a_1269_);
v___x_1274_ = v___x_1266_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_basePasses_1261_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_monoPasses_1262_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_monoPassesNoLambda_1263_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1276_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1274_);
v___x_1276_ = v___x_1271_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_del_object(v___x_1266_);
lean_dec_ref(v_monoPassesNoLambda_1263_);
lean_dec_ref(v_monoPasses_1262_);
lean_dec_ref(v_basePasses_1261_);
v_a_1280_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1268_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1268_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run___boxed(lean_object* v_manager_1289_, lean_object* v_installer_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1289_, v_installer_1290_, v_a_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(lean_object* v_x_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
if (lean_obj_tag(v_x_1295_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v_a_1299_ = lean_ctor_get(v_x_1295_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v_x_1295_, 1);
v___x_1300_ = l_Lean_stringToMessageData(v_a_1299_);
v___x_1301_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1300_, v___y_1296_, v___y_1297_);
return v___x_1301_;
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
v_a_1302_ = lean_ctor_get(v_x_1295_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_x_1295_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v_x_1295_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v_x_1295_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set_tag(v___x_1304_, 0);
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg___boxed(lean_object* v_x_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(lean_object* v_declName_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v___x_1327_; lean_object* v_env_1328_; lean_object* v_options_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1327_ = lean_st_ref_get(v_a_1325_);
v_env_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc_ref(v_env_1328_);
lean_dec(v___x_1327_);
v_options_1329_ = lean_ctor_get(v_a_1324_, 2);
v___x_1330_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3));
v___x_1331_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1328_, v_options_1329_, v___x_1330_, v_declName_1323_);
v___x_1332_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v___x_1331_, v_a_1324_, v_a_1325_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___boxed(lean_object* v_declName_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1333_, v_a_1334_, v_a_1335_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(lean_object* v_00_u03b1_1338_, lean_object* v_x_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1339_, v___y_1340_, v___y_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_1344_, lean_object* v_x_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(v_00_u03b1_1344_, v_x_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object* v_manager_1350_, lean_object* v_declName_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1350_, v_a_1356_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = l_Lean_Compiler_LCNF_PassManager_validate(v_a_1358_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v___x_1359_, 0);
lean_dec(v_unused_1367_);
v___x_1361_ = v___x_1359_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_dec(v___x_1359_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v_a_1358_);
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1358_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_a_1358_);
v_a_1368_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1359_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1359_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
return v___x_1357_;
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v_manager_1350_);
v_a_1376_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1355_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1355_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl___boxed(lean_object* v_manager_1384_, lean_object* v_declName_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_manager_1384_, v_declName_1385_, v_a_1386_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
return v_res_1389_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
