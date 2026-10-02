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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Phase_ctorIdx(uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Purity_ctorIdx(uint8_t);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__23_value),LEAN_SCALAR_PTR_LITERAL(72, 221, 106, 103, 22, 21, 224, 51)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__24_value),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_string_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__32_value),LEAN_SCALAR_PTR_LITERAL(236, 252, 83, 10, 217, 228, 80, 149)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__33_value),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36;
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
static const lean_ctor_object l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45 = (const lean_object*)&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46;
static lean_once_cell_t l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47;
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
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26));
v___x_171_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22);
v___x_172_ = lean_array_push(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_173_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27);
v___x_174_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19));
v___x_175_ = lean_box(2);
v___x_176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_173_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28);
v___x_178_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_179_ = lean_array_push(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29);
v___x_181_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17));
v___x_182_ = lean_box(2);
v___x_183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
lean_ctor_set(v___x_183_, 2, v___x_180_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30);
v___x_185_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_186_ = lean_array_push(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35));
v___x_200_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22);
v___x_201_ = lean_array_push(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_202_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36);
v___x_203_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19));
v___x_204_ = lean_box(2);
v___x_205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_ctor_set(v___x_205_, 2, v___x_202_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37);
v___x_207_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_208_ = lean_array_push(v___x_207_, v___x_206_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_209_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38);
v___x_210_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17));
v___x_211_ = lean_box(2);
v___x_212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
lean_ctor_set(v___x_212_, 2, v___x_209_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39);
v___x_214_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31);
v___x_215_ = lean_array_push(v___x_214_, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_216_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40);
v___x_217_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9));
v___x_218_ = lean_box(2);
v___x_219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_217_);
lean_ctor_set(v___x_219_, 2, v___x_216_);
return v___x_219_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_220_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41);
v___x_221_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_222_ = lean_array_push(v___x_221_, v___x_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42);
v___x_224_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15));
v___x_225_ = lean_box(2);
v___x_226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_224_);
lean_ctor_set(v___x_226_, 2, v___x_223_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43);
v___x_228_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13);
v___x_229_ = lean_array_push(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_235_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44);
v___x_236_ = lean_array_push(v___x_235_, v___x_234_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_238_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46);
v___x_239_ = lean_array_push(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_241_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47);
v___x_242_ = lean_array_push(v___x_241_, v___x_240_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_244_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48);
v___x_245_ = lean_array_push(v___x_244_, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49);
v___x_247_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11));
v___x_248_ = lean_box(2);
v___x_249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
lean_ctor_set(v___x_249_, 2, v___x_246_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50);
v___x_251_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_252_ = lean_array_push(v___x_251_, v___x_250_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_253_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51);
v___x_254_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9));
v___x_255_ = lean_box(2);
v___x_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_254_);
lean_ctor_set(v___x_256_, 2, v___x_253_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52);
v___x_258_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_259_ = lean_array_push(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53);
v___x_261_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7));
v___x_262_ = lean_box(2);
v___x_263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
lean_ctor_set(v___x_263_, 2, v___x_260_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54);
v___x_265_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_266_ = lean_array_push(v___x_265_, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55);
v___x_268_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4));
v___x_269_ = lean_box(2);
v___x_270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_268_);
lean_ctor_set(v___x_270_, 2, v___x_267_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam(void){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(lean_object* v_decls_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v_decls_272_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___lam__0___boxed(lean_object* v_decls_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(v_decls_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_298_, 0, v___y_294_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___boxed(lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(lean_object* v_run_317_, size_t v_sz_318_, size_t v_i_319_, lean_object* v_bs_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_lt(v_i_319_, v_sz_318_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
lean_dec_ref(v_run_317_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v_bs_320_);
return v___x_327_;
}
else
{
lean_object* v_v_328_; lean_object* v___x_329_; lean_object* v_bs_x27_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_v_328_ = lean_array_uget(v_bs_320_, v_i_319_);
v___x_329_ = lean_unsigned_to_nat(0u);
v_bs_x27_330_ = lean_array_uset(v_bs_320_, v_i_319_, v___x_329_);
v___x_331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0));
v___x_332_ = l_Lean_Core_checkSystem(v___x_331_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v___x_333_; 
lean_dec_ref_known(v___x_332_, 1);
lean_inc_ref(v_run_317_);
lean_inc(v___y_324_);
lean_inc_ref(v___y_323_);
lean_inc(v___y_322_);
lean_inc_ref(v___y_321_);
v___x_333_ = lean_apply_6(v_run_317_, v_v_328_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, lean_box(0));
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; size_t v___x_335_; size_t v___x_336_; lean_object* v___x_337_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_319_, v___x_335_);
v___x_337_ = lean_array_uset(v_bs_x27_330_, v_i_319_, v_a_334_);
v_i_319_ = v___x_336_;
v_bs_320_ = v___x_337_;
goto _start;
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec_ref(v_bs_x27_330_);
lean_dec_ref(v_run_317_);
v_a_339_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_333_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_333_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v_bs_x27_330_);
lean_dec(v_v_328_);
lean_dec_ref(v_run_317_);
v_a_347_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_332_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_332_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___boxed(lean_object* v_run_355_, lean_object* v_sz_356_, lean_object* v_i_357_, lean_object* v_bs_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
size_t v_sz_boxed_364_; size_t v_i_boxed_365_; lean_object* v_res_366_; 
v_sz_boxed_364_ = lean_unbox_usize(v_sz_356_);
lean_dec(v_sz_356_);
v_i_boxed_365_ = lean_unbox_usize(v_i_357_);
lean_dec(v_i_357_);
v_res_366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_355_, v_sz_boxed_364_, v_i_boxed_365_, v_bs_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(lean_object* v_run_367_, lean_object* v_xs_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
size_t v_sz_374_; size_t v___x_375_; lean_object* v___x_376_; 
v_sz_374_ = lean_array_size(v_xs_368_);
v___x_375_ = ((size_t)0ULL);
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_367_, v_sz_374_, v___x_375_, v_xs_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed(lean_object* v_run_377_, lean_object* v_xs_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(v_run_377_, v_xs_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object* v_name_385_, uint8_t v_phase_386_, lean_object* v_run_387_, lean_object* v_occurrence_388_){
_start:
{
lean_object* v___f_389_; uint8_t v___x_390_; lean_object* v___x_391_; 
v___f_389_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed), 7, 1);
lean_closure_set(v___f_389_, 0, v_run_387_);
v___x_390_ = 0;
v___x_391_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_391_, 0, v_occurrence_388_);
lean_ctor_set(v___x_391_, 1, v_name_385_);
lean_ctor_set(v___x_391_, 2, v___f_389_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*3, v_phase_386_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*3 + 1, v_phase_386_);
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*3 + 2, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___boxed(lean_object* v_name_392_, lean_object* v_phase_393_, lean_object* v_run_394_, lean_object* v_occurrence_395_){
_start:
{
uint8_t v_phase_boxed_396_; lean_object* v_res_397_; 
v_phase_boxed_396_ = lean_unbox(v_phase_393_);
v_res_397_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v_name_392_, v_phase_boxed_396_, v_run_394_, v_occurrence_395_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_398_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
lean_ctor_set(v___x_403_, 2, v___x_402_);
lean_ctor_set(v___x_403_, 3, v___x_402_);
lean_ctor_set(v___x_403_, 4, v___x_401_);
lean_ctor_set(v___x_403_, 5, v___x_401_);
lean_ctor_set(v___x_403_, 6, v___x_401_);
lean_ctor_set(v___x_403_, 7, v___x_401_);
lean_ctor_set(v___x_403_, 8, v___x_401_);
lean_ctor_set(v___x_403_, 9, v___x_401_);
lean_ctor_set(v___x_403_, 10, v___x_401_);
return v___x_403_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_unsigned_to_nat(32u);
v___x_405_ = lean_mk_empty_array_with_capacity(v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_407_ = ((size_t)5ULL);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_unsigned_to_nat(32u);
v___x_410_ = lean_mk_empty_array_with_capacity(v___x_409_);
v___x_411_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3);
v___x_412_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_408_);
lean_ctor_set(v___x_412_, 3, v___x_408_);
lean_ctor_set_usize(v___x_412_, 4, v___x_407_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_box(1);
v___x_414_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4);
v___x_415_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
v___x_416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_414_);
lean_ctor_set(v___x_416_, 2, v___x_413_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(lean_object* v_msgData_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; lean_object* v_toCold_422_; lean_object* v_env_423_; lean_object* v_options_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_421_ = lean_st_ref_get(v___y_419_);
v_toCold_422_ = lean_ctor_get(v___y_418_, 0);
v_env_423_ = lean_ctor_get(v___x_421_, 0);
lean_inc_ref(v_env_423_);
lean_dec(v___x_421_);
v_options_424_ = lean_ctor_get(v_toCold_422_, 2);
v___x_425_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2);
v___x_426_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_424_);
v___x_427_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_427_, 0, v_env_423_);
lean_ctor_set(v___x_427_, 1, v___x_425_);
lean_ctor_set(v___x_427_, 2, v___x_426_);
lean_ctor_set(v___x_427_, 3, v_options_424_);
v___x_428_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_msgData_417_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___boxed(lean_object* v_msgData_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msgData_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_ref_439_; lean_object* v___x_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
v_ref_439_ = lean_ctor_get(v___y_436_, 2);
v___x_440_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msg_435_, v___y_436_, v___y_437_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_449_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
lean_inc(v_ref_439_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_ref_439_);
lean_ctor_set(v___x_445_, 1, v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set_tag(v___x_443_, 1);
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg___boxed(lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(uint8_t v_phase_457_, lean_object* v_as_458_, size_t v_sz_459_, size_t v_i_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_a_466_; uint8_t v___x_470_; 
v___x_470_ = lean_usize_dec_lt(v_i_460_, v_sz_459_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_b_461_);
return v___x_471_;
}
else
{
lean_object* v_a_472_; uint8_t v_phase_473_; lean_object* v_name_474_; lean_object* v___x_475_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_a_472_ = lean_array_uget_borrowed(v_as_458_, v_i_460_);
v_phase_473_ = lean_ctor_get_uint8(v_a_472_, sizeof(void*)*3);
v_name_474_ = lean_ctor_get(v_a_472_, 1);
v___x_475_ = lean_box(0);
v___x_483_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_phase_473_);
v___x_484_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_phase_457_);
v___x_485_ = lean_nat_dec_eq(v___x_483_, v___x_484_);
lean_dec(v___x_484_);
lean_dec(v___x_483_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___y_490_; 
lean_inc(v_name_474_);
v___x_486_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_474_, v___x_470_);
v___x_487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0));
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
switch(v_phase_473_)
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
switch(v_phase_457_)
{
case 0:
{
lean_object* v___x_494_; 
v___x_494_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_477_ = v___x_493_;
v___y_478_ = v___x_494_;
goto v___jp_476_;
}
case 1:
{
lean_object* v___x_495_; 
v___x_495_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_477_ = v___x_493_;
v___y_478_ = v___x_495_;
goto v___jp_476_;
}
default: 
{
lean_object* v___x_496_; 
v___x_496_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_477_ = v___x_493_;
v___y_478_ = v___x_496_;
goto v___jp_476_;
}
}
}
}
else
{
v_a_466_ = v___x_475_;
goto v___jp_465_;
}
v___jp_476_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_479_ = lean_string_append(v___y_477_, v___y_478_);
v___x_480_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
v___x_481_ = l_Lean_MessageData_ofFormat(v___x_480_);
v___x_482_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_481_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_dec_ref_known(v___x_482_, 1);
v_a_466_ = v___x_475_;
goto v___jp_465_;
}
else
{
return v___x_482_;
}
}
}
v___jp_465_:
{
size_t v___x_467_; size_t v___x_468_; 
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_add(v_i_460_, v___x_467_);
v_i_460_ = v___x_468_;
v_b_461_ = v_a_466_;
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
lean_object* v___f_729_; lean_object* v___x_1599__overap_730_; lean_object* v___x_731_; 
v___f_729_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0));
v___x_1599__overap_730_ = lean_panic_fn_borrowed(v___f_729_, v_msg_725_);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
v___x_731_ = lean_apply_3(v___x_1599__overap_730_, v___y_726_, v___y_727_, lean_box(0));
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
lean_object* v___x_809_; uint8_t v_phase_810_; lean_object* v_install_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
lean_inc_ref(v_f_777_);
lean_inc(v_a_779_);
v___x_809_ = lean_apply_1(v_f_777_, v_a_779_);
v_phase_810_ = lean_ctor_get_uint8(v___x_809_, sizeof(void*)*1);
v_install_811_ = lean_ctor_get(v___x_809_, 0);
lean_inc_ref(v_install_811_);
lean_dec_ref(v___x_809_);
v___x_812_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_phase_810_);
v___x_813_ = l_Lean_Compiler_LCNF_Phase_ctorIdx(v_phase_778_);
v___x_814_ = lean_nat_dec_eq(v___x_812_, v___x_813_);
lean_dec(v___x_813_);
lean_dec(v___x_812_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2);
v___x_816_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v___x_815_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_811_, v_b_780_, v_a_817_, v___y_781_, v___y_782_);
v___y_785_ = v___x_818_;
goto v___jp_784_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_install_811_);
lean_dec_ref(v_b_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_f_777_);
v_a_819_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_816_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_box(0);
v___x_828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_811_, v_b_780_, v___x_827_, v___y_781_, v___y_782_);
v___y_785_ = v___x_828_;
goto v___jp_784_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___boxed(lean_object* v_upperBound_829_, lean_object* v_f_830_, lean_object* v_phase_831_, lean_object* v_a_832_, lean_object* v_b_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v_phase_boxed_837_; lean_object* v_res_838_; 
v_phase_boxed_837_ = lean_unbox(v_phase_831_);
v_res_838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_829_, v_f_830_, v_phase_boxed_837_, v_a_832_, v_b_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v_upperBound_829_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(lean_object* v_targetName_839_, lean_object* v_f_840_, uint8_t v_phase_841_, lean_object* v_passes_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(v_targetName_839_, v_passes_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_850_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v_fst_848_ = lean_ctor_get(v_a_847_, 0);
lean_inc(v_fst_848_);
v_snd_849_ = lean_ctor_get(v_a_847_, 1);
lean_inc(v_snd_849_);
lean_dec(v_a_847_);
v___x_850_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_snd_849_, v_f_840_, v_phase_841_, v_fst_848_, v_passes_842_, v___y_843_, v___y_844_);
lean_dec(v_snd_849_);
return v___x_850_;
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v_passes_842_);
lean_dec_ref(v_f_840_);
v_a_851_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_846_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_846_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed(lean_object* v_targetName_859_, lean_object* v_f_860_, lean_object* v_phase_861_, lean_object* v_passes_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v_phase_boxed_866_; lean_object* v_res_867_; 
v_phase_boxed_866_ = lean_unbox(v_phase_861_);
v_res_867_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(v_targetName_859_, v_f_860_, v_phase_boxed_866_, v_passes_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(uint8_t v_phase_868_, lean_object* v_targetName_869_, lean_object* v_f_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___f_872_; lean_object* v___x_873_; 
v___x_871_ = lean_box(v_phase_868_);
v___f_872_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed), 7, 3);
lean_closure_set(v___f_872_, 0, v_targetName_869_);
lean_closure_set(v___f_872_, 1, v_f_870_);
lean_closure_set(v___f_872_, 2, v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_873_, 0, v___f_872_);
lean_ctor_set_uint8(v___x_873_, sizeof(void*)*1, v_phase_868_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___boxed(lean_object* v_phase_874_, lean_object* v_targetName_875_, lean_object* v_f_876_){
_start:
{
uint8_t v_phase_boxed_877_; lean_object* v_res_878_; 
v_phase_boxed_877_ = lean_unbox(v_phase_874_);
v_res_878_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_boxed_877_, v_targetName_875_, v_f_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(lean_object* v_upperBound_879_, lean_object* v_f_880_, uint8_t v_phase_881_, lean_object* v_inst_882_, lean_object* v_R_883_, lean_object* v_a_884_, lean_object* v_b_885_, lean_object* v_c_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_879_, v_f_880_, v_phase_881_, v_a_884_, v_b_885_, v___y_887_, v___y_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___boxed(lean_object* v_upperBound_891_, lean_object* v_f_892_, lean_object* v_phase_893_, lean_object* v_inst_894_, lean_object* v_R_895_, lean_object* v_a_896_, lean_object* v_b_897_, lean_object* v_c_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
uint8_t v_phase_boxed_902_; lean_object* v_res_903_; 
v_phase_boxed_902_ = lean_unbox(v_phase_893_);
v_res_903_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(v_upperBound_891_, v_f_892_, v_phase_boxed_902_, v_inst_894_, v_R_895_, v_a_896_, v_b_897_, v_c_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v_upperBound_891_);
return v_res_903_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(lean_object* v_targetName_904_, lean_object* v_occurrence_905_, lean_object* v_p_906_){
_start:
{
lean_object* v_occurrence_907_; lean_object* v_name_908_; uint8_t v___x_909_; 
v_occurrence_907_ = lean_ctor_get(v_p_906_, 0);
v_name_908_ = lean_ctor_get(v_p_906_, 1);
v___x_909_ = lean_name_eq(v_name_908_, v_targetName_904_);
if (v___x_909_ == 0)
{
return v___x_909_;
}
else
{
uint8_t v___x_910_; 
v___x_910_ = lean_nat_dec_eq(v_occurrence_907_, v_occurrence_905_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed(lean_object* v_targetName_911_, lean_object* v_occurrence_912_, lean_object* v_p_913_){
_start:
{
uint8_t v_res_914_; lean_object* v_r_915_; 
v_res_914_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(v_targetName_911_, v_occurrence_912_, v_p_913_);
lean_dec_ref(v_p_913_);
lean_dec(v_occurrence_912_);
lean_dec(v_targetName_911_);
v_r_915_ = lean_box(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(lean_object* v___f_920_, lean_object* v_p_921_, lean_object* v_targetName_922_, lean_object* v_occurrence_923_, lean_object* v_passes_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_920_, v_passes_924_, v___x_928_);
if (lean_obj_tag(v___x_929_) == 1)
{
lean_object* v_val_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_occurrence_923_);
lean_dec(v_targetName_922_);
v_val_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_944_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_944_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_val_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_944_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_passUnderTest_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v_j_938_; lean_object* v_as_939_; lean_object* v___x_940_; lean_object* v___x_942_; 
v_passUnderTest_934_ = lean_array_fget_borrowed(v_passes_924_, v_val_930_);
v___x_935_ = lean_unsigned_to_nat(1u);
v___x_936_ = lean_nat_add(v_val_930_, v___x_935_);
lean_dec(v_val_930_);
lean_inc(v_passUnderTest_934_);
v___x_937_ = lean_apply_1(v_p_921_, v_passUnderTest_934_);
v_j_938_ = lean_array_get_size(v_passes_924_);
v_as_939_ = lean_array_push(v_passes_924_, v___x_937_);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_936_, v_as_939_, v_j_938_);
lean_dec(v___x_936_);
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 0);
lean_ctor_set(v___x_932_, 0, v___x_940_);
v___x_942_ = v___x_932_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
else
{
lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v___x_929_);
lean_dec_ref(v_passes_924_);
lean_dec_ref(v_p_921_);
v___x_945_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0));
v___x_946_ = 1;
v___x_947_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_922_, v___x_946_);
v___x_948_ = lean_string_append(v___x_945_, v___x_947_);
v___x_949_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_950_ = lean_string_append(v___x_948_, v___x_949_);
v___x_951_ = l_Nat_reprFast(v_occurrence_923_);
v___x_952_ = lean_string_append(v___x_950_, v___x_951_);
lean_dec_ref(v___x_951_);
v___x_953_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_954_ = lean_string_append(v___x_952_, v___x_953_);
v___x_955_ = lean_string_append(v___x_954_, v___x_947_);
lean_dec_ref(v___x_947_);
v___x_956_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
v___x_958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
v___x_959_ = l_Lean_MessageData_ofFormat(v___x_958_);
v___x_960_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_959_, v___y_925_, v___y_926_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed(lean_object* v___f_961_, lean_object* v_p_962_, lean_object* v_targetName_963_, lean_object* v_occurrence_964_, lean_object* v_passes_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(v___f_961_, v_p_962_, v_targetName_963_, v_occurrence_964_, v_passes_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter(uint8_t v_phase_970_, lean_object* v_targetName_971_, lean_object* v_p_972_, lean_object* v_occurrence_973_){
_start:
{
lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___x_976_; 
lean_inc(v_occurrence_973_);
lean_inc(v_targetName_971_);
v___f_974_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed), 3, 2);
lean_closure_set(v___f_974_, 0, v_targetName_971_);
lean_closure_set(v___f_974_, 1, v_occurrence_973_);
v___f_975_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed), 8, 4);
lean_closure_set(v___f_975_, 0, v___f_974_);
lean_closure_set(v___f_975_, 1, v_p_972_);
lean_closure_set(v___f_975_, 2, v_targetName_971_);
lean_closure_set(v___f_975_, 3, v_occurrence_973_);
v___x_976_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_976_, 0, v___f_975_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*1, v_phase_970_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___boxed(lean_object* v_phase_977_, lean_object* v_targetName_978_, lean_object* v_p_979_, lean_object* v_occurrence_980_){
_start:
{
uint8_t v_phase_boxed_981_; lean_object* v_res_982_; 
v_phase_boxed_981_ = lean_unbox(v_phase_977_);
v_res_982_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_boxed_981_, v_targetName_978_, v_p_979_, v_occurrence_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(uint8_t v_phase_983_, lean_object* v_targetName_984_, lean_object* v_p_985_, lean_object* v_x_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_983_, v_targetName_984_, v_p_985_, v_x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed(lean_object* v_phase_988_, lean_object* v_targetName_989_, lean_object* v_p_990_, lean_object* v_x_991_){
_start:
{
uint8_t v_phase_boxed_992_; lean_object* v_res_993_; 
v_phase_boxed_992_ = lean_unbox(v_phase_988_);
v_res_993_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(v_phase_boxed_992_, v_targetName_989_, v_p_990_, v_x_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(uint8_t v_phase_994_, lean_object* v_targetName_995_, lean_object* v_p_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___f_998_; lean_object* v___x_999_; 
v___x_997_ = lean_box(v_phase_994_);
lean_inc(v_targetName_995_);
v___f_998_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed), 4, 3);
lean_closure_set(v___f_998_, 0, v___x_997_);
lean_closure_set(v___f_998_, 1, v_targetName_995_);
lean_closure_set(v___f_998_, 2, v_p_996_);
v___x_999_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_994_, v_targetName_995_, v___f_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___boxed(lean_object* v_phase_1000_, lean_object* v_targetName_1001_, lean_object* v_p_1002_){
_start:
{
uint8_t v_phase_boxed_1003_; lean_object* v_res_1004_; 
v_phase_boxed_1003_ = lean_unbox(v_phase_1000_);
v_res_1004_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(v_phase_boxed_1003_, v_targetName_1001_, v_p_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(lean_object* v___f_1005_, lean_object* v_p_1006_, lean_object* v_targetName_1007_, lean_object* v_occurrence_1008_, lean_object* v_passes_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1005_, v_passes_1009_, v___x_1013_);
if (lean_obj_tag(v___x_1014_) == 1)
{
lean_object* v_val_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v_occurrence_1008_);
lean_dec(v_targetName_1007_);
v_val_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1027_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_val_1015_);
lean_dec(v___x_1014_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1027_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_passUnderTest_1019_; lean_object* v___x_1020_; lean_object* v_j_1021_; lean_object* v_as_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v_passUnderTest_1019_ = lean_array_fget_borrowed(v_passes_1009_, v_val_1015_);
lean_inc(v_passUnderTest_1019_);
v___x_1020_ = lean_apply_1(v_p_1006_, v_passUnderTest_1019_);
v_j_1021_ = lean_array_get_size(v_passes_1009_);
v_as_1022_ = lean_array_push(v_passes_1009_, v___x_1020_);
v___x_1023_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_val_1015_, v_as_1022_, v_j_1021_);
lean_dec(v_val_1015_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1023_);
v___x_1025_ = v___x_1017_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
else
{
lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec(v___x_1014_);
lean_dec_ref(v_passes_1009_);
lean_dec_ref(v_p_1006_);
v___x_1028_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0));
v___x_1029_ = 1;
v___x_1030_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_1007_, v___x_1029_);
v___x_1031_ = lean_string_append(v___x_1028_, v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_1033_ = lean_string_append(v___x_1031_, v___x_1032_);
v___x_1034_ = l_Nat_reprFast(v_occurrence_1008_);
v___x_1035_ = lean_string_append(v___x_1033_, v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_1037_ = lean_string_append(v___x_1035_, v___x_1036_);
v___x_1038_ = lean_string_append(v___x_1037_, v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1039_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_1040_ = lean_string_append(v___x_1038_, v___x_1039_);
v___x_1041_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
v___x_1042_ = l_Lean_MessageData_ofFormat(v___x_1041_);
v___x_1043_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1042_, v___y_1010_, v___y_1011_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed(lean_object* v___f_1044_, lean_object* v_p_1045_, lean_object* v_targetName_1046_, lean_object* v_occurrence_1047_, lean_object* v_passes_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(v___f_1044_, v_p_1045_, v_targetName_1046_, v_occurrence_1047_, v_passes_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore(uint8_t v_phase_1053_, lean_object* v_targetName_1054_, lean_object* v_p_1055_, lean_object* v_occurrence_1056_){
_start:
{
lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; 
lean_inc(v_occurrence_1056_);
lean_inc(v_targetName_1054_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1057_, 0, v_targetName_1054_);
lean_closure_set(v___f_1057_, 1, v_occurrence_1056_);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1058_, 0, v___f_1057_);
lean_closure_set(v___f_1058_, 1, v_p_1055_);
lean_closure_set(v___f_1058_, 2, v_targetName_1054_);
lean_closure_set(v___f_1058_, 3, v_occurrence_1056_);
v___x_1059_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1059_, 0, v___f_1058_);
lean_ctor_set_uint8(v___x_1059_, sizeof(void*)*1, v_phase_1053_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___boxed(lean_object* v_phase_1060_, lean_object* v_targetName_1061_, lean_object* v_p_1062_, lean_object* v_occurrence_1063_){
_start:
{
uint8_t v_phase_boxed_1064_; lean_object* v_res_1065_; 
v_phase_boxed_1064_ = lean_unbox(v_phase_1060_);
v_res_1065_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_boxed_1064_, v_targetName_1061_, v_p_1062_, v_occurrence_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(uint8_t v_phase_1066_, lean_object* v_targetName_1067_, lean_object* v_p_1068_, lean_object* v_x_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_1066_, v_targetName_1067_, v_p_1068_, v_x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed(lean_object* v_phase_1071_, lean_object* v_targetName_1072_, lean_object* v_p_1073_, lean_object* v_x_1074_){
_start:
{
uint8_t v_phase_boxed_1075_; lean_object* v_res_1076_; 
v_phase_boxed_1075_ = lean_unbox(v_phase_1071_);
v_res_1076_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(v_phase_boxed_1075_, v_targetName_1072_, v_p_1073_, v_x_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(uint8_t v_phase_1077_, lean_object* v_targetName_1078_, lean_object* v_p_1079_){
_start:
{
lean_object* v___x_1080_; lean_object* v___f_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_box(v_phase_1077_);
lean_inc(v_targetName_1078_);
v___f_1081_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1081_, 0, v___x_1080_);
lean_closure_set(v___f_1081_, 1, v_targetName_1078_);
lean_closure_set(v___f_1081_, 2, v_p_1079_);
v___x_1082_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1077_, v_targetName_1078_, v___f_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___boxed(lean_object* v_phase_1083_, lean_object* v_targetName_1084_, lean_object* v_p_1085_){
_start:
{
uint8_t v_phase_boxed_1086_; lean_object* v_res_1087_; 
v_phase_boxed_1086_ = lean_unbox(v_phase_1083_);
v_res_1087_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(v_phase_boxed_1086_, v_targetName_1084_, v_p_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(lean_object* v_targetName_1088_, lean_object* v_occurrence_1089_, lean_object* v_as_1090_, lean_object* v_j_1091_){
_start:
{
uint8_t v___y_1093_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = lean_array_get_size(v_as_1090_);
v___x_1099_ = lean_nat_dec_lt(v_j_1091_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_dec(v_j_1091_);
v___x_1100_ = lean_box(0);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; lean_object* v_occurrence_1102_; lean_object* v_name_1103_; uint8_t v___x_1104_; 
v___x_1101_ = lean_array_fget_borrowed(v_as_1090_, v_j_1091_);
v_occurrence_1102_ = lean_ctor_get(v___x_1101_, 0);
v_name_1103_ = lean_ctor_get(v___x_1101_, 1);
v___x_1104_ = lean_name_eq(v_name_1103_, v_targetName_1088_);
if (v___x_1104_ == 0)
{
v___y_1093_ = v___x_1104_;
goto v___jp_1092_;
}
else
{
uint8_t v___x_1105_; 
v___x_1105_ = lean_nat_dec_eq(v_occurrence_1102_, v_occurrence_1089_);
v___y_1093_ = v___x_1105_;
goto v___jp_1092_;
}
}
v___jp_1092_:
{
if (v___y_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_nat_add(v_j_1091_, v___x_1094_);
lean_dec(v_j_1091_);
v_j_1091_ = v___x_1095_;
goto _start;
}
else
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_j_1091_);
return v___x_1097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0___boxed(lean_object* v_targetName_1106_, lean_object* v_occurrence_1107_, lean_object* v_as_1108_, lean_object* v_j_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_1106_, v_occurrence_1107_, v_as_1108_, v_j_1109_);
lean_dec_ref(v_as_1108_);
lean_dec(v_occurrence_1107_);
lean_dec(v_targetName_1106_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(lean_object* v_targetName_1112_, lean_object* v_occurrence_1113_, lean_object* v_p_1114_, lean_object* v_passes_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_1112_, v_occurrence_1113_, v_passes_1115_, v___x_1119_);
if (lean_obj_tag(v___x_1120_) == 1)
{
lean_object* v_val_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_occurrence_1113_);
lean_dec(v_targetName_1112_);
v_val_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1138_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_val_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1138_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_array_get_size(v_passes_1115_);
v___x_1126_ = lean_nat_dec_lt(v_val_1121_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1128_; 
lean_dec(v_val_1121_);
lean_dec_ref(v_p_1114_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 0);
lean_ctor_set(v___x_1123_, 0, v_passes_1115_);
v___x_1128_ = v___x_1123_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_passes_1115_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
else
{
lean_object* v_v_1130_; lean_object* v___x_1131_; lean_object* v_xs_x27_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v_v_1130_ = lean_array_fget(v_passes_1115_, v_val_1121_);
v___x_1131_ = lean_box(0);
v_xs_x27_1132_ = lean_array_fset(v_passes_1115_, v_val_1121_, v___x_1131_);
v___x_1133_ = lean_apply_1(v_p_1114_, v_v_1130_);
v___x_1134_ = lean_array_fset(v_xs_x27_1132_, v_val_1121_, v___x_1133_);
lean_dec(v_val_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1134_);
v___x_1136_ = v___x_1123_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v___x_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec(v___x_1120_);
lean_dec_ref(v_passes_1115_);
lean_dec_ref(v_p_1114_);
v___x_1139_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0));
v___x_1140_ = 1;
v___x_1141_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_1112_, v___x_1140_);
v___x_1142_ = lean_string_append(v___x_1139_, v___x_1141_);
v___x_1143_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_1144_ = lean_string_append(v___x_1142_, v___x_1143_);
v___x_1145_ = l_Nat_reprFast(v_occurrence_1113_);
v___x_1146_ = lean_string_append(v___x_1144_, v___x_1145_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_1148_ = lean_string_append(v___x_1146_, v___x_1147_);
v___x_1149_ = lean_string_append(v___x_1148_, v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1150_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_1151_ = lean_string_append(v___x_1149_, v___x_1150_);
v___x_1152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
v___x_1153_ = l_Lean_MessageData_ofFormat(v___x_1152_);
v___x_1154_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1153_, v___y_1116_, v___y_1117_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed(lean_object* v_targetName_1155_, lean_object* v_occurrence_1156_, lean_object* v_p_1157_, lean_object* v_passes_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(v_targetName_1155_, v_occurrence_1156_, v_p_1157_, v_passes_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass(uint8_t v_phase_1163_, lean_object* v_targetName_1164_, lean_object* v_p_1165_, lean_object* v_occurrence_1166_){
_start:
{
lean_object* v___f_1167_; lean_object* v___x_1168_; 
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1167_, 0, v_targetName_1164_);
lean_closure_set(v___f_1167_, 1, v_occurrence_1166_);
lean_closure_set(v___f_1167_, 2, v_p_1165_);
v___x_1168_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1168_, 0, v___f_1167_);
lean_ctor_set_uint8(v___x_1168_, sizeof(void*)*1, v_phase_1163_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___boxed(lean_object* v_phase_1169_, lean_object* v_targetName_1170_, lean_object* v_p_1171_, lean_object* v_occurrence_1172_){
_start:
{
uint8_t v_phase_boxed_1173_; lean_object* v_res_1174_; 
v_phase_boxed_1173_ = lean_unbox(v_phase_1169_);
v_res_1174_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_boxed_1173_, v_targetName_1170_, v_p_1171_, v_occurrence_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(uint8_t v_phase_1175_, lean_object* v_targetName_1176_, lean_object* v_p_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_1175_, v_targetName_1176_, v_p_1177_, v_x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed(lean_object* v_phase_1180_, lean_object* v_targetName_1181_, lean_object* v_p_1182_, lean_object* v_x_1183_){
_start:
{
uint8_t v_phase_boxed_1184_; lean_object* v_res_1185_; 
v_phase_boxed_1184_ = lean_unbox(v_phase_1180_);
v_res_1185_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(v_phase_boxed_1184_, v_targetName_1181_, v_p_1182_, v_x_1183_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(uint8_t v_phase_1186_, lean_object* v_targetName_1187_, lean_object* v_p_1188_){
_start:
{
lean_object* v___x_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; 
v___x_1189_ = lean_box(v_phase_1186_);
lean_inc(v_targetName_1187_);
v___f_1190_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1190_, 0, v___x_1189_);
lean_closure_set(v___f_1190_, 1, v_targetName_1187_);
lean_closure_set(v___f_1190_, 2, v_p_1188_);
v___x_1191_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1186_, v_targetName_1187_, v___f_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___boxed(lean_object* v_phase_1192_, lean_object* v_targetName_1193_, lean_object* v_p_1194_){
_start:
{
uint8_t v_phase_boxed_1195_; lean_object* v_res_1196_; 
v_phase_boxed_1195_ = lean_unbox(v_phase_1192_);
v_res_1196_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(v_phase_boxed_1195_, v_targetName_1193_, v_p_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run(lean_object* v_manager_1197_, lean_object* v_installer_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
uint8_t v_phase_1202_; 
v_phase_1202_ = lean_ctor_get_uint8(v_installer_1198_, sizeof(void*)*1);
switch(v_phase_1202_)
{
case 0:
{
lean_object* v_install_1203_; lean_object* v_basePasses_1204_; lean_object* v_monoPasses_1205_; lean_object* v_monoPassesNoLambda_1206_; lean_object* v_impurePasses_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1231_; 
v_install_1203_ = lean_ctor_get(v_installer_1198_, 0);
lean_inc_ref(v_install_1203_);
lean_dec_ref(v_installer_1198_);
v_basePasses_1204_ = lean_ctor_get(v_manager_1197_, 0);
v_monoPasses_1205_ = lean_ctor_get(v_manager_1197_, 1);
v_monoPassesNoLambda_1206_ = lean_ctor_get(v_manager_1197_, 2);
v_impurePasses_1207_ = lean_ctor_get(v_manager_1197_, 3);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_manager_1197_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1209_ = v_manager_1197_;
v_isShared_1210_ = v_isSharedCheck_1231_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_impurePasses_1207_);
lean_inc(v_monoPassesNoLambda_1206_);
lean_inc(v_monoPasses_1205_);
lean_inc(v_basePasses_1204_);
lean_dec(v_manager_1197_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1231_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; 
lean_inc(v_a_1200_);
lean_inc_ref(v_a_1199_);
v___x_1211_ = lean_apply_4(v_install_1203_, v_basePasses_1204_, v_a_1199_, v_a_1200_, lean_box(0));
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1222_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v_a_1212_);
v___x_1217_ = v___x_1209_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1212_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_monoPasses_1205_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_monoPassesNoLambda_1206_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_impurePasses_1207_);
v___x_1217_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1219_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1217_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_del_object(v___x_1209_);
lean_dec_ref(v_impurePasses_1207_);
lean_dec_ref(v_monoPassesNoLambda_1206_);
lean_dec_ref(v_monoPasses_1205_);
v_a_1223_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1211_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1211_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
case 1:
{
lean_object* v_install_1232_; lean_object* v_basePasses_1233_; lean_object* v_monoPasses_1234_; lean_object* v_monoPassesNoLambda_1235_; lean_object* v_impurePasses_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1260_; 
v_install_1232_ = lean_ctor_get(v_installer_1198_, 0);
lean_inc_ref(v_install_1232_);
lean_dec_ref(v_installer_1198_);
v_basePasses_1233_ = lean_ctor_get(v_manager_1197_, 0);
v_monoPasses_1234_ = lean_ctor_get(v_manager_1197_, 1);
v_monoPassesNoLambda_1235_ = lean_ctor_get(v_manager_1197_, 2);
v_impurePasses_1236_ = lean_ctor_get(v_manager_1197_, 3);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_manager_1197_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1238_ = v_manager_1197_;
v_isShared_1239_ = v_isSharedCheck_1260_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_impurePasses_1236_);
lean_inc(v_monoPassesNoLambda_1235_);
lean_inc(v_monoPasses_1234_);
lean_inc(v_basePasses_1233_);
lean_dec(v_manager_1197_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1260_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; 
lean_inc(v_a_1200_);
lean_inc_ref(v_a_1199_);
v___x_1240_ = lean_apply_4(v_install_1232_, v_monoPasses_1234_, v_a_1199_, v_a_1200_, lean_box(0));
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1251_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1251_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1251_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v_a_1241_);
v___x_1246_ = v___x_1238_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_basePasses_1233_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_a_1241_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_monoPassesNoLambda_1235_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_impurePasses_1236_);
v___x_1246_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1248_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1246_);
v___x_1248_ = v___x_1243_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_del_object(v___x_1238_);
lean_dec_ref(v_impurePasses_1236_);
lean_dec_ref(v_monoPassesNoLambda_1235_);
lean_dec_ref(v_basePasses_1233_);
v_a_1252_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1240_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1240_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
default: 
{
lean_object* v_install_1261_; lean_object* v_basePasses_1262_; lean_object* v_monoPasses_1263_; lean_object* v_monoPassesNoLambda_1264_; lean_object* v_impurePasses_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1289_; 
v_install_1261_ = lean_ctor_get(v_installer_1198_, 0);
lean_inc_ref(v_install_1261_);
lean_dec_ref(v_installer_1198_);
v_basePasses_1262_ = lean_ctor_get(v_manager_1197_, 0);
v_monoPasses_1263_ = lean_ctor_get(v_manager_1197_, 1);
v_monoPassesNoLambda_1264_ = lean_ctor_get(v_manager_1197_, 2);
v_impurePasses_1265_ = lean_ctor_get(v_manager_1197_, 3);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_manager_1197_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1267_ = v_manager_1197_;
v_isShared_1268_ = v_isSharedCheck_1289_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_impurePasses_1265_);
lean_inc(v_monoPassesNoLambda_1264_);
lean_inc(v_monoPasses_1263_);
lean_inc(v_basePasses_1262_);
lean_dec(v_manager_1197_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1289_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; 
lean_inc(v_a_1200_);
lean_inc_ref(v_a_1199_);
v___x_1269_ = lean_apply_4(v_install_1261_, v_impurePasses_1265_, v_a_1199_, v_a_1200_, lean_box(0));
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1280_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 3, v_a_1270_);
v___x_1275_ = v___x_1267_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_basePasses_1262_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_monoPasses_1263_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_monoPassesNoLambda_1264_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1277_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1275_);
v___x_1277_ = v___x_1272_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_del_object(v___x_1267_);
lean_dec_ref(v_monoPassesNoLambda_1264_);
lean_dec_ref(v_monoPasses_1263_);
lean_dec_ref(v_basePasses_1262_);
v_a_1281_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1269_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1269_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run___boxed(lean_object* v_manager_1290_, lean_object* v_installer_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1290_, v_installer_1291_, v_a_1292_, v_a_1293_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
if (lean_obj_tag(v_x_1296_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_a_1300_ = lean_ctor_get(v_x_1296_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v_x_1296_, 1);
v___x_1301_ = l_Lean_stringToMessageData(v_a_1300_);
v___x_1302_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1301_, v___y_1297_, v___y_1298_);
return v___x_1302_;
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v_x_1296_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_x_1296_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v_x_1296_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v_x_1296_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 0);
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg___boxed(lean_object* v_x_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(lean_object* v_declName_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v_env_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1328_ = lean_st_ref_get(v_a_1326_);
v_env_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc_ref(v_env_1329_);
lean_dec(v___x_1328_);
v___x_1330_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1325_);
v___x_1331_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3));
v___x_1332_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1329_, v___x_1330_, v___x_1331_, v_declName_1324_);
lean_dec_ref(v___x_1330_);
v___x_1333_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v___x_1332_, v_a_1325_, v_a_1326_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___boxed(lean_object* v_declName_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1334_, v_a_1335_, v_a_1336_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(lean_object* v_00_u03b1_1339_, lean_object* v_x_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1340_, v___y_1341_, v___y_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(v_00_u03b1_1345_, v_x_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object* v_manager_1351_, lean_object* v_declName_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1358_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___x_1358_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1351_, v_a_1357_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1360_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v___x_1360_ = l_Lean_Compiler_LCNF_PassManager_validate(v_a_1359_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v___x_1360_, 0);
lean_dec(v_unused_1368_);
v___x_1362_ = v___x_1360_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v___x_1360_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_a_1359_);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1359_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v_a_1359_);
v_a_1369_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1360_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1360_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
else
{
return v___x_1358_;
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_manager_1351_);
v_a_1377_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1356_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1356_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl___boxed(lean_object* v_manager_1385_, lean_object* v_declName_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_manager_1385_, v_declName_1386_, v_a_1387_, v_a_1388_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
return v_res_1390_;
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
