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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instInhabitedCoreM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
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
lean_object* l_Lean_Compiler_LCNF_Phase_toNat(uint8_t v_x_1_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Phase_toNat_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_5_;
v_res_5_ = l_Lean_Compiler_LCNF_Phase_toNat(v_x_1_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_toNat___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_34__boxed_7_; lean_object* v_res_8_; 
v_x_34__boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = l_Lean_Compiler_LCNF_Phase_toNat(v_x_34__boxed_7_);
return v_res_8_;
}
}
lean_object* l_Lean_Compiler_LCNF_instToStringPhase___lam__0(uint8_t v_x_12_){
_start:
{
switch(v_x_12_)
{
case 0:
{
lean_object* v___x_13_; 
v___x_13_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
return v___x_13_;
}
case 1:
{
lean_object* v___x_14_; 
v___x_14_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
return v___x_14_;
}
default: 
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
return v___x_15_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instToStringPhase___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_12_ = stack[0].m_num;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0(v_x_12_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instToStringPhase___lam__0___boxed(lean_object* v_x_17_){
_start:
{
uint8_t v_x_36__boxed_18_; lean_object* v_res_19_; 
v_x_36__boxed_18_ = lean_unbox(v_x_17_);
v_res_19_ = l_Lean_Compiler_LCNF_instToStringPhase___lam__0(v_x_36__boxed_18_);
return v_res_19_;
}
}
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object* v_inst_28_, uint8_t v_pp_29_, uint8_t v_ip_30_, lean_object* v_x_31_){
_start:
{
uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_32_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_pp_29_);
v___x_33_ = lean_box(v___x_32_);
v___x_34_ = lean_obj_tag_nat(v___x_33_);
lean_dec(v___x_33_);
v___x_35_ = lean_box(v_ip_30_);
v___x_36_ = lean_obj_tag_nat(v___x_35_);
lean_dec(v___x_35_);
v___x_37_ = lean_nat_dec_eq(v___x_34_, v___x_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___y_43_; lean_object* v___y_44_; lean_object* v___x_50_; lean_object* v___y_52_; 
lean_dec(v_x_31_);
v___x_38_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0));
v___x_39_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1));
v___x_40_ = lean_unsigned_to_nat(33u);
v___x_41_ = lean_unsigned_to_nat(4u);
v___x_50_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3));
switch(v_pp_29_)
{
case 0:
{
lean_object* v___x_58_; 
v___x_58_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_52_ = v___x_58_;
goto v___jp_51_;
}
case 1:
{
lean_object* v___x_59_; 
v___x_59_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_52_ = v___x_59_;
goto v___jp_51_;
}
default: 
{
lean_object* v___x_60_; 
v___x_60_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_52_ = v___x_60_;
goto v___jp_51_;
}
}
v___jp_42_:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_45_ = lean_string_append(v___y_43_, v___y_44_);
v___x_46_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2));
v___x_47_ = lean_string_append(v___x_45_, v___x_46_);
v___x_48_ = l_mkPanicMessageWithDecl(v___x_38_, v___x_39_, v___x_40_, v___x_41_, v___x_47_);
lean_dec_ref(v___x_47_);
v___x_49_ = l_panic___redArg(v_inst_28_, v___x_48_);
return v___x_49_;
}
v___jp_51_:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_string_append(v___x_50_, v___y_52_);
v___x_54_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4));
v___x_55_ = lean_string_append(v___x_53_, v___x_54_);
if (v_ip_30_ == 0)
{
lean_object* v___x_56_; 
v___x_56_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5));
v___y_43_ = v___x_55_;
v___y_44_ = v___x_56_;
goto v___jp_42_;
}
else
{
lean_object* v___x_57_; 
v___x_57_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_43_ = v___x_55_;
v___y_44_ = v___x_57_;
goto v___jp_42_;
}
}
}
else
{
lean_object* v___x_61_; 
v___x_61_ = lean_apply_1(v_x_31_, lean_box(0));
return v___x_61_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_28_ = stack[0].m_obj;
uint8_t v_pp_29_ = stack[1].m_num;
uint8_t v_ip_30_ = stack[2].m_num;
lean_object* v_x_31_ = stack[3].m_obj;
lean_object* v_res_62_;
v_res_62_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v_inst_28_, v_pp_29_, v_ip_30_, v_x_31_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___boxed(lean_object* v_inst_63_, lean_object* v_pp_64_, lean_object* v_ip_65_, lean_object* v_x_66_){
_start:
{
uint8_t v_pp_boxed_67_; uint8_t v_ip_boxed_68_; lean_object* v_res_69_; 
v_pp_boxed_67_ = lean_unbox(v_pp_64_);
v_ip_boxed_68_ = lean_unbox(v_ip_65_);
v_res_69_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v_inst_63_, v_pp_boxed_67_, v_ip_boxed_68_, v_x_66_);
lean_dec(v_inst_63_);
return v_res_69_;
}
}
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck(lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, uint8_t v_pp_72_, uint8_t v_ip_73_, lean_object* v_x_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v_inst_71_, v_pp_72_, v_ip_73_, v_x_74_);
return v___x_75_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Phase_withPurityCheck_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_71_ = stack[1].m_obj;
uint8_t v_pp_72_ = stack[2].m_num;
uint8_t v_ip_73_ = stack[3].m_num;
lean_object* v_x_74_ = stack[4].m_obj;
lean_object* v_res_76_;
v_res_76_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck(lean_box(0), v_inst_71_, v_pp_72_, v_ip_73_, v_x_74_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___boxed(lean_object* v_00_u03b1_77_, lean_object* v_inst_78_, lean_object* v_pp_79_, lean_object* v_ip_80_, lean_object* v_x_81_){
_start:
{
uint8_t v_pp_boxed_82_; uint8_t v_ip_boxed_83_; lean_object* v_res_84_; 
v_pp_boxed_82_ = lean_unbox(v_pp_79_);
v_ip_boxed_83_ = lean_unbox(v_ip_80_);
v_res_84_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck(v_00_u03b1_77_, v_inst_78_, v_pp_boxed_82_, v_ip_boxed_83_, v_x_81_);
lean_dec(v_inst_78_);
return v_res_84_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instLTPhase(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_box(0);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instLEPhase(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
uint8_t l_Lean_Compiler_LCNF_instDecidableLtPhase(uint8_t v_p1_87_, uint8_t v_p2_88_){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_89_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p1_87_);
v___x_90_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p2_88_);
v___x_91_ = lean_nat_dec_lt(v___x_89_, v___x_90_);
lean_dec(v___x_90_);
lean_dec(v___x_89_);
return v___x_91_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instDecidableLtPhase_0interp(lean_interpreter_value* stack)
{
uint8_t v_p1_87_ = stack[0].m_num;
uint8_t v_p2_88_ = stack[1].m_num;
uint8_t v_res_92_;
v_res_92_ = l_Lean_Compiler_LCNF_instDecidableLtPhase(v_p1_87_, v_p2_88_);
stack->m_num = v_res_92_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableLtPhase___boxed(lean_object* v_p1_93_, lean_object* v_p2_94_){
_start:
{
uint8_t v_p1_boxed_95_; uint8_t v_p2_boxed_96_; uint8_t v_res_97_; lean_object* v_r_98_; 
v_p1_boxed_95_ = lean_unbox(v_p1_93_);
v_p2_boxed_96_ = lean_unbox(v_p2_94_);
v_res_97_ = l_Lean_Compiler_LCNF_instDecidableLtPhase(v_p1_boxed_95_, v_p2_boxed_96_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
uint8_t l_Lean_Compiler_LCNF_instDecidableLePhase(uint8_t v_p1_99_, uint8_t v_p2_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_101_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p1_99_);
v___x_102_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p2_100_);
v___x_103_ = lean_nat_dec_le(v___x_101_, v___x_102_);
lean_dec(v___x_102_);
lean_dec(v___x_101_);
return v___x_103_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instDecidableLePhase_0interp(lean_interpreter_value* stack)
{
uint8_t v_p1_99_ = stack[0].m_num;
uint8_t v_p2_100_ = stack[1].m_num;
uint8_t v_res_104_;
v_res_104_ = l_Lean_Compiler_LCNF_instDecidableLePhase(v_p1_99_, v_p2_100_);
stack->m_num = v_res_104_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableLePhase___boxed(lean_object* v_p1_105_, lean_object* v_p2_106_){
_start:
{
uint8_t v_p1_boxed_107_; uint8_t v_p2_boxed_108_; uint8_t v_res_109_; lean_object* v_r_110_; 
v_p1_boxed_107_ = lean_unbox(v_p1_105_);
v_p2_boxed_108_ = lean_unbox(v_p2_106_);
v_res_109_ = l_Lean_Compiler_LCNF_instDecidableLePhase(v_p1_boxed_107_, v_p2_boxed_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10));
v___x_138_ = l_Lean_mkAtom(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12);
v___x_140_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_141_ = lean_array_push(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20));
v___x_162_ = l_Lean_mkAtom(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21);
v___x_164_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_165_ = lean_array_push(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26));
v___x_179_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22);
v___x_180_ = lean_array_push(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27);
v___x_182_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19));
v___x_183_ = lean_box(2);
v___x_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_181_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28);
v___x_186_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_187_ = lean_array_push(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29);
v___x_189_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17));
v___x_190_ = lean_box(2);
v___x_191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30);
v___x_193_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_194_ = lean_array_push(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35));
v___x_208_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22);
v___x_209_ = lean_array_push(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36);
v___x_211_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19));
v___x_212_ = lean_box(2);
v___x_213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___x_211_);
lean_ctor_set(v___x_213_, 2, v___x_210_);
return v___x_213_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37);
v___x_215_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_216_ = lean_array_push(v___x_215_, v___x_214_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_217_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38);
v___x_218_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17));
v___x_219_ = lean_box(2);
v___x_220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___x_218_);
lean_ctor_set(v___x_220_, 2, v___x_217_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39);
v___x_222_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31);
v___x_223_ = lean_array_push(v___x_222_, v___x_221_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_224_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40);
v___x_225_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9));
v___x_226_ = lean_box(2);
v___x_227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_225_);
lean_ctor_set(v___x_227_, 2, v___x_224_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_228_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41);
v___x_229_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_230_ = lean_array_push(v___x_229_, v___x_228_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_231_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42);
v___x_232_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15));
v___x_233_ = lean_box(2);
v___x_234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set(v___x_234_, 1, v___x_232_);
lean_ctor_set(v___x_234_, 2, v___x_231_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43);
v___x_236_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13);
v___x_237_ = lean_array_push(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_243_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44);
v___x_244_ = lean_array_push(v___x_243_, v___x_242_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_246_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46);
v___x_247_ = lean_array_push(v___x_246_, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_249_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47);
v___x_250_ = lean_array_push(v___x_249_, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_252_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48);
v___x_253_ = lean_array_push(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_254_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49);
v___x_255_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11));
v___x_256_ = lean_box(2);
v___x_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___x_254_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50);
v___x_259_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_260_ = lean_array_push(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51);
v___x_262_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9));
v___x_263_ = lean_box(2);
v___x_264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_261_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52);
v___x_266_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_267_ = lean_array_push(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53);
v___x_269_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7));
v___x_270_ = lean_box(2);
v___x_271_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
lean_ctor_set(v___x_271_, 2, v___x_268_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54);
v___x_273_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_274_ = lean_array_push(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55);
v___x_276_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__4));
v___x_277_ = lean_box(2);
v___x_278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
lean_ctor_set(v___x_278_, 2, v___x_275_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56);
return v___x_279_;
}
}
lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(lean_object* v_decls_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_decls_280_);
return v___x_286_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instInhabitedPass___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_280_ = stack[0].m_obj;
lean_object* v___y_281_ = stack[1].m_obj;
lean_object* v___y_282_ = stack[2].m_obj;
lean_object* v___y_283_ = stack[3].m_obj;
lean_object* v___y_284_ = stack[4].m_obj;
lean_object* v_res_287_;
v_res_287_ = l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(v_decls_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPass___lam__0___boxed(lean_object* v_decls_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Compiler_LCNF_instInhabitedPass___lam__0(v_decls_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_294_;
}
}
lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_307_, 0, v___y_303_);
return v___x_307_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_303_ = stack[0].m_obj;
lean_object* v___y_304_ = stack[1].m_obj;
lean_object* v___y_305_ = stack[2].m_obj;
lean_object* v_res_308_;
v_res_308_ = l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(v___y_303_, v___y_304_, v___y_305_);
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___boxed(lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_313_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(lean_object* v_run_327_, size_t v_sz_328_, size_t v_i_329_, lean_object* v_bs_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = lean_usize_dec_lt(v_i_329_, v_sz_328_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_dec_ref(v_run_327_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v_bs_330_);
return v___x_337_;
}
else
{
lean_object* v_v_338_; lean_object* v___x_339_; lean_object* v_bs_x27_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_v_338_ = lean_array_uget(v_bs_330_, v_i_329_);
v___x_339_ = lean_unsigned_to_nat(0u);
v_bs_x27_340_ = lean_array_uset(v_bs_330_, v_i_329_, v___x_339_);
v___x_341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0));
v___x_342_ = l_Lean_Core_checkSystem(v___x_341_, v___y_333_, v___y_334_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v___x_343_; 
lean_dec_ref_known(v___x_342_, 1);
lean_inc_ref(v_run_327_);
lean_inc(v___y_334_);
lean_inc_ref(v___y_333_);
lean_inc(v___y_332_);
lean_inc_ref(v___y_331_);
v___x_343_ = lean_apply_6(v_run_327_, v_v_338_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, lean_box(0));
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; size_t v___x_345_; size_t v___x_346_; lean_object* v___x_347_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_add(v_i_329_, v___x_345_);
v___x_347_ = lean_array_uset(v_bs_x27_340_, v_i_329_, v_a_344_);
v_i_329_ = v___x_346_;
v_bs_330_ = v___x_347_;
goto _start;
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v_bs_x27_340_);
lean_dec_ref(v_run_327_);
v_a_349_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_343_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_343_);
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
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec_ref(v_bs_x27_340_);
lean_dec(v_v_338_);
lean_dec_ref(v_run_327_);
v_a_357_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_342_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_342_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_run_327_ = stack[0].m_obj;
size_t v_sz_328_ = stack[1].m_num;
size_t v_i_329_ = stack[2].m_num;
lean_object* v_bs_330_ = stack[3].m_obj;
lean_object* v___y_331_ = stack[4].m_obj;
lean_object* v___y_332_ = stack[5].m_obj;
lean_object* v___y_333_ = stack[6].m_obj;
lean_object* v___y_334_ = stack[7].m_obj;
lean_object* v_res_365_;
v_res_365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_327_, v_sz_328_, v_i_329_, v_bs_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
stack->m_obj
 = v_res_365_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___boxed(lean_object* v_run_366_, lean_object* v_sz_367_, lean_object* v_i_368_, lean_object* v_bs_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
size_t v_sz_boxed_375_; size_t v_i_boxed_376_; lean_object* v_res_377_; 
v_sz_boxed_375_ = lean_unbox_usize(v_sz_367_);
lean_dec(v_sz_367_);
v_i_boxed_376_ = lean_unbox_usize(v_i_368_);
lean_dec(v_i_368_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_366_, v_sz_boxed_375_, v_i_boxed_376_, v_bs_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_377_;
}
}
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(lean_object* v_run_378_, lean_object* v_xs_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
size_t v_sz_385_; size_t v___x_386_; lean_object* v___x_387_; 
v_sz_385_ = lean_array_size(v_xs_379_);
v___x_386_ = ((size_t)0ULL);
v___x_387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_378_, v_sz_385_, v___x_386_, v_xs_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
return v___x_387_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_run_378_ = stack[0].m_obj;
lean_object* v_xs_379_ = stack[1].m_obj;
lean_object* v___y_380_ = stack[2].m_obj;
lean_object* v___y_381_ = stack[3].m_obj;
lean_object* v___y_382_ = stack[4].m_obj;
lean_object* v___y_383_ = stack[5].m_obj;
lean_object* v_res_388_;
v_res_388_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(v_run_378_, v_xs_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed(lean_object* v_run_389_, lean_object* v_xs_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(v_run_389_, v_xs_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_396_;
}
}
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object* v_name_397_, uint8_t v_phase_398_, lean_object* v_run_399_, lean_object* v_occurrence_400_){
_start:
{
lean_object* v___f_401_; uint8_t v___x_402_; lean_object* v___x_403_; 
v___f_401_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed), 7, 1);
lean_closure_set(v___f_401_, 0, v_run_399_);
v___x_402_ = 0;
v___x_403_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_403_, 0, v_occurrence_400_);
lean_ctor_set(v___x_403_, 1, v_name_397_);
lean_ctor_set(v___x_403_, 2, v___f_401_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*3, v_phase_398_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*3 + 1, v_phase_398_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*3 + 2, v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Pass_mkPerDeclaration_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_397_ = stack[0].m_obj;
uint8_t v_phase_398_ = stack[1].m_num;
lean_object* v_run_399_ = stack[2].m_obj;
lean_object* v_occurrence_400_ = stack[3].m_obj;
lean_object* v_res_404_;
v_res_404_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v_name_397_, v_phase_398_, v_run_399_, v_occurrence_400_);
stack->m_obj
 = v_res_404_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___boxed(lean_object* v_name_405_, lean_object* v_phase_406_, lean_object* v_run_407_, lean_object* v_occurrence_408_){
_start:
{
uint8_t v_phase_boxed_409_; lean_object* v_res_410_; 
v_phase_boxed_409_ = lean_unbox(v_phase_406_);
v_res_410_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v_name_405_, v_phase_boxed_409_, v_run_407_, v_occurrence_408_);
return v_res_410_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_411_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_415_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
lean_ctor_set(v___x_417_, 2, v___x_416_);
lean_ctor_set(v___x_417_, 3, v___x_416_);
lean_ctor_set(v___x_417_, 4, v___x_415_);
lean_ctor_set(v___x_417_, 5, v___x_415_);
lean_ctor_set(v___x_417_, 6, v___x_415_);
lean_ctor_set(v___x_417_, 7, v___x_415_);
lean_ctor_set(v___x_417_, 8, v___x_415_);
lean_ctor_set(v___x_417_, 9, v___x_415_);
lean_ctor_set(v___x_417_, 10, v___x_415_);
lean_ctor_set(v___x_417_, 11, v___x_414_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_unsigned_to_nat(32u);
v___x_419_ = lean_mk_empty_array_with_capacity(v___x_418_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_421_ = ((size_t)5ULL);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_unsigned_to_nat(32u);
v___x_424_ = lean_mk_empty_array_with_capacity(v___x_423_);
v___x_425_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3);
v___x_426_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_424_);
lean_ctor_set(v___x_426_, 2, v___x_422_);
lean_ctor_set(v___x_426_, 3, v___x_422_);
lean_ctor_set_usize(v___x_426_, 4, v___x_421_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_427_ = lean_box(1);
v___x_428_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4);
v___x_429_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
v___x_430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
lean_ctor_set(v___x_430_, 2, v___x_427_);
return v___x_430_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(lean_object* v_msgData_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; lean_object* v_toCold_436_; lean_object* v_env_437_; lean_object* v_options_438_; uint8_t v___x_439_; lean_object* v_env_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_435_ = lean_st_ref_get(v___y_433_);
v_toCold_436_ = lean_ctor_get(v___y_432_, 0);
v_env_437_ = lean_ctor_get(v___x_435_, 0);
lean_inc_ref(v_env_437_);
lean_dec(v___x_435_);
v_options_438_ = lean_ctor_get(v_toCold_436_, 2);
v___x_439_ = 0;
v_env_440_ = l_Lean_Environment_setRecordingDeps(v_env_437_, v___x_439_);
v___x_441_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2);
v___x_442_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_438_);
v___x_443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_443_, 0, v_env_440_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_ctor_set(v___x_443_, 2, v___x_442_);
lean_ctor_set(v___x_443_, 3, v_options_438_);
v___x_444_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v_msgData_431_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_431_ = stack[0].m_obj;
lean_object* v___y_432_ = stack[1].m_obj;
lean_object* v___y_433_ = stack[2].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msgData_431_, v___y_432_, v___y_433_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___boxed(lean_object* v_msgData_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msgData_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_451_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_ref_456_; lean_object* v___x_457_; lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
v_ref_456_ = lean_ctor_get(v___y_453_, 2);
v___x_457_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msg_452_, v___y_453_, v___y_454_);
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_466_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
lean_inc(v_ref_456_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v_ref_456_);
lean_ctor_set(v___x_462_, 1, v_a_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 1);
lean_ctor_set(v___x_460_, 0, v___x_462_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_452_ = stack[0].m_obj;
lean_object* v___y_453_ = stack[1].m_obj;
lean_object* v___y_454_ = stack[2].m_obj;
lean_object* v_res_467_;
v_res_467_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_452_, v___y_453_, v___y_454_);
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg___boxed(lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
return v_res_472_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(uint8_t v_phase_475_, lean_object* v_as_476_, size_t v_sz_477_, size_t v_i_478_, lean_object* v_b_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_a_484_; uint8_t v___x_488_; 
v___x_488_ = lean_usize_dec_lt(v_i_478_, v_sz_477_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v_b_479_);
return v___x_489_;
}
else
{
lean_object* v_a_490_; uint8_t v_phase_491_; lean_object* v_name_492_; lean_object* v___x_493_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_a_490_ = lean_array_uget_borrowed(v_as_476_, v_i_478_);
v_phase_491_ = lean_ctor_get_uint8(v_a_490_, sizeof(void*)*3);
v_name_492_ = lean_ctor_get(v_a_490_, 1);
v___x_493_ = lean_box(0);
v___x_501_ = lean_box(v_phase_491_);
v___x_502_ = lean_obj_tag_nat(v___x_501_);
lean_dec(v___x_501_);
v___x_503_ = lean_box(v_phase_475_);
v___x_504_ = lean_obj_tag_nat(v___x_503_);
lean_dec(v___x_503_);
v___x_505_ = lean_nat_dec_eq(v___x_502_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___y_510_; 
lean_inc(v_name_492_);
v___x_506_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_492_, v___x_488_);
v___x_507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0));
v___x_508_ = lean_string_append(v___x_506_, v___x_507_);
switch(v_phase_491_)
{
case 0:
{
lean_object* v___x_517_; 
v___x_517_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_510_ = v___x_517_;
goto v___jp_509_;
}
case 1:
{
lean_object* v___x_518_; 
v___x_518_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_510_ = v___x_518_;
goto v___jp_509_;
}
default: 
{
lean_object* v___x_519_; 
v___x_519_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_510_ = v___x_519_;
goto v___jp_509_;
}
}
v___jp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_string_append(v___x_508_, v___y_510_);
v___x_512_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1));
v___x_513_ = lean_string_append(v___x_511_, v___x_512_);
switch(v_phase_475_)
{
case 0:
{
lean_object* v___x_514_; 
v___x_514_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_495_ = v___x_513_;
v___y_496_ = v___x_514_;
goto v___jp_494_;
}
case 1:
{
lean_object* v___x_515_; 
v___x_515_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_495_ = v___x_513_;
v___y_496_ = v___x_515_;
goto v___jp_494_;
}
default: 
{
lean_object* v___x_516_; 
v___x_516_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_495_ = v___x_513_;
v___y_496_ = v___x_516_;
goto v___jp_494_;
}
}
}
}
else
{
v_a_484_ = v___x_493_;
goto v___jp_483_;
}
v___jp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = lean_string_append(v___y_495_, v___y_496_);
v___x_498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
v___x_499_ = l_Lean_MessageData_ofFormat(v___x_498_);
v___x_500_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_499_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_dec_ref_known(v___x_500_, 1);
v_a_484_ = v___x_493_;
goto v___jp_483_;
}
else
{
return v___x_500_;
}
}
}
v___jp_483_:
{
size_t v___x_485_; size_t v___x_486_; 
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_add(v_i_478_, v___x_485_);
v_i_478_ = v___x_486_;
v_b_479_ = v_a_484_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_475_ = stack[0].m_num;
lean_object* v_as_476_ = stack[1].m_obj;
size_t v_sz_477_ = stack[2].m_num;
size_t v_i_478_ = stack[3].m_num;
lean_object* v_b_479_ = stack[4].m_obj;
lean_object* v___y_480_ = stack[5].m_obj;
lean_object* v___y_481_ = stack[6].m_obj;
lean_object* v_res_520_;
v_res_520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_475_, v_as_476_, v_sz_477_, v_i_478_, v_b_479_, v___y_480_, v___y_481_);
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___boxed(lean_object* v_phase_521_, lean_object* v_as_522_, lean_object* v_sz_523_, lean_object* v_i_524_, lean_object* v_b_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
uint8_t v_phase_boxed_529_; size_t v_sz_boxed_530_; size_t v_i_boxed_531_; lean_object* v_res_532_; 
v_phase_boxed_529_ = lean_unbox(v_phase_521_);
v_sz_boxed_530_ = lean_unbox_usize(v_sz_523_);
lean_dec(v_sz_523_);
v_i_boxed_531_ = lean_unbox_usize(v_i_524_);
lean_dec(v_i_524_);
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_boxed_529_, v_as_522_, v_sz_boxed_530_, v_i_boxed_531_, v_b_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec_ref(v_as_522_);
return v_res_532_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(uint8_t v_phase_533_, lean_object* v_passes_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; size_t v_sz_539_; size_t v___x_540_; lean_object* v___x_541_; 
v___x_538_ = lean_box(0);
v_sz_539_ = lean_array_size(v_passes_534_);
v___x_540_ = ((size_t)0ULL);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_533_, v_passes_534_, v_sz_539_, v___x_540_, v___x_538_, v_a_535_, v_a_536_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v___x_541_, 0);
lean_dec(v_unused_549_);
v___x_543_ = v___x_541_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_dec(v___x_541_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_538_);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_538_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
return v___x_541_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_533_ = stack[0].m_num;
lean_object* v_passes_534_ = stack[1].m_obj;
lean_object* v_a_535_ = stack[2].m_obj;
lean_object* v_a_536_ = stack[3].m_obj;
lean_object* v_res_550_;
v_res_550_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v_phase_533_, v_passes_534_, v_a_535_, v_a_536_);
stack->m_obj
 = v_res_550_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses___boxed(lean_object* v_phase_551_, lean_object* v_passes_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
uint8_t v_phase_boxed_556_; lean_object* v_res_557_; 
v_phase_boxed_556_ = lean_unbox(v_phase_551_);
v_res_557_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v_phase_boxed_556_, v_passes_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec_ref(v_passes_552_);
return v_res_557_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(lean_object* v_00_u03b1_558_, lean_object* v_msg_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_559_, v___y_560_, v___y_561_);
return v___x_563_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_559_ = stack[1].m_obj;
lean_object* v___y_560_ = stack[2].m_obj;
lean_object* v___y_561_ = stack[3].m_obj;
lean_object* v_res_564_;
v_res_564_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(lean_box(0), v_msg_559_, v___y_560_, v___y_561_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___boxed(lean_object* v_00_u03b1_565_, lean_object* v_msg_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(v_00_u03b1_565_, v_msg_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_570_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassManager_validate(lean_object* v_manager_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_basePasses_575_; lean_object* v_monoPasses_576_; lean_object* v_monoPassesNoLambda_577_; uint8_t v___x_578_; lean_object* v___x_579_; 
v_basePasses_575_ = lean_ctor_get(v_manager_571_, 0);
v_monoPasses_576_ = lean_ctor_get(v_manager_571_, 1);
v_monoPassesNoLambda_577_ = lean_ctor_get(v_manager_571_, 2);
v___x_578_ = 0;
v___x_579_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_578_, v_basePasses_575_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_579_) == 0)
{
uint8_t v___x_580_; lean_object* v___x_581_; 
lean_dec_ref_known(v___x_579_, 1);
v___x_580_ = 1;
v___x_581_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_580_, v_monoPasses_576_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_582_; 
lean_dec_ref_known(v___x_581_, 1);
v___x_582_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_580_, v_monoPassesNoLambda_577_, v_a_572_, v_a_573_);
return v___x_582_;
}
else
{
return v___x_581_;
}
}
else
{
return v___x_579_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassManager_validate_0interp(lean_interpreter_value* stack)
{
lean_object* v_manager_571_ = stack[0].m_obj;
lean_object* v_a_572_ = stack[1].m_obj;
lean_object* v_a_573_ = stack[2].m_obj;
lean_object* v_res_583_;
v_res_583_ = l_Lean_Compiler_LCNF_PassManager_validate(v_manager_571_, v_a_572_, v_a_573_);
stack->m_obj
 = v_res_583_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_validate___boxed(lean_object* v_manager_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Compiler_LCNF_PassManager_validate(v_manager_584_, v_a_585_, v_a_586_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec_ref(v_manager_584_);
return v_res_588_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(lean_object* v_targetName_589_, lean_object* v_as_590_, size_t v_sz_591_, size_t v_i_592_, lean_object* v_b_593_){
_start:
{
lean_object* v_a_596_; uint8_t v___x_600_; 
v___x_600_ = lean_usize_dec_lt(v_i_592_, v_sz_591_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v_b_593_);
return v___x_601_;
}
else
{
lean_object* v_fst_602_; lean_object* v_snd_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_620_; 
v_fst_602_ = lean_ctor_get(v_b_593_, 0);
v_snd_603_ = lean_ctor_get(v_b_593_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_b_593_);
if (v_isSharedCheck_620_ == 0)
{
v___x_605_ = v_b_593_;
v_isShared_606_ = v_isSharedCheck_620_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_snd_603_);
lean_inc(v_fst_602_);
lean_dec(v_b_593_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_620_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_a_607_; lean_object* v___y_609_; lean_object* v_occurrence_615_; lean_object* v_name_616_; uint8_t v___x_617_; 
v_a_607_ = lean_array_uget_borrowed(v_as_590_, v_i_592_);
v_occurrence_615_ = lean_ctor_get(v_a_607_, 0);
v_name_616_ = lean_ctor_get(v_a_607_, 1);
v___x_617_ = lean_name_eq(v_name_616_, v_targetName_589_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_del_object(v___x_605_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_fst_602_);
lean_ctor_set(v___x_618_, 1, v_snd_603_);
v_a_596_ = v___x_618_;
goto v___jp_595_;
}
else
{
lean_dec(v_snd_603_);
if (lean_obj_tag(v_fst_602_) == 0)
{
if (v___x_617_ == 0)
{
v___y_609_ = v_fst_602_;
goto v___jp_608_;
}
else
{
lean_object* v___x_619_; 
lean_inc(v_occurrence_615_);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v_occurrence_615_);
v___y_609_ = v___x_619_;
goto v___jp_608_;
}
}
else
{
v___y_609_ = v_fst_602_;
goto v___jp_608_;
}
}
v___jp_608_:
{
lean_object* v_occurrence_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v_occurrence_610_ = lean_ctor_get(v_a_607_, 0);
lean_inc(v_occurrence_610_);
v___x_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_611_, 0, v_occurrence_610_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v___x_611_);
lean_ctor_set(v___x_605_, 0, v___y_609_);
v___x_613_ = v___x_605_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___y_609_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v_a_596_ = v___x_613_;
goto v___jp_595_;
}
}
}
}
v___jp_595_:
{
size_t v___x_597_; size_t v___x_598_; 
v___x_597_ = ((size_t)1ULL);
v___x_598_ = lean_usize_add(v_i_592_, v___x_597_);
v_i_592_ = v___x_598_;
v_b_593_ = v_a_596_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetName_589_ = stack[0].m_obj;
lean_object* v_as_590_ = stack[1].m_obj;
size_t v_sz_591_ = stack[2].m_num;
size_t v_i_592_ = stack[3].m_num;
lean_object* v_b_593_ = stack[4].m_obj;
lean_object* v_res_621_;
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_589_, v_as_590_, v_sz_591_, v_i_592_, v_b_593_);
stack->m_obj
 = v_res_621_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg___boxed(lean_object* v_targetName_622_, lean_object* v_as_623_, lean_object* v_sz_624_, lean_object* v_i_625_, lean_object* v_b_626_, lean_object* v___y_627_){
_start:
{
size_t v_sz_boxed_628_; size_t v_i_boxed_629_; lean_object* v_res_630_; 
v_sz_boxed_628_ = lean_unbox_usize(v_sz_624_);
lean_dec(v_sz_624_);
v_i_boxed_629_ = lean_unbox_usize(v_i_625_);
lean_dec(v_i_625_);
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_622_, v_as_623_, v_sz_boxed_628_, v_i_boxed_629_, v_b_626_);
lean_dec_ref(v_as_623_);
lean_dec(v_targetName_622_);
return v_res_630_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(lean_object* v_targetName_634_, lean_object* v_passes_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___x_649_; size_t v_sz_650_; size_t v___x_651_; lean_object* v___x_652_; 
v___x_649_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1));
v_sz_650_ = lean_array_size(v_passes_635_);
v___x_651_ = ((size_t)0ULL);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_634_, v_passes_635_, v_sz_650_, v___x_651_, v___x_649_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_672_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_672_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_672_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_672_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_fst_657_; 
v_fst_657_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_fst_657_);
if (lean_obj_tag(v_fst_657_) == 1)
{
lean_object* v_snd_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_670_; 
v_snd_658_ = lean_ctor_get(v_a_653_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_a_653_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v_a_653_, 0);
lean_dec(v_unused_671_);
v___x_660_ = v_a_653_;
v_isShared_661_ = v_isSharedCheck_670_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snd_658_);
lean_dec(v_a_653_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_670_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
if (lean_obj_tag(v_snd_658_) == 1)
{
lean_object* v_val_662_; lean_object* v_val_663_; lean_object* v___x_665_; 
lean_dec(v_targetName_634_);
v_val_662_ = lean_ctor_get(v_fst_657_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v_fst_657_, 1);
v_val_663_ = lean_ctor_get(v_snd_658_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v_snd_658_, 1);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v_val_663_);
lean_ctor_set(v___x_660_, 0, v_val_662_);
v___x_665_ = v___x_660_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_val_662_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_val_663_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_667_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_665_);
v___x_667_ = v___x_655_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec_ref_known(v_fst_657_, 1);
lean_del_object(v___x_655_);
v___y_640_ = v_a_636_;
v___y_641_ = v_a_637_;
goto v___jp_639_;
}
}
}
else
{
lean_dec(v_fst_657_);
lean_del_object(v___x_655_);
lean_dec(v_a_653_);
v___y_640_ = v_a_636_;
v___y_641_ = v_a_637_;
goto v___jp_639_;
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec(v_targetName_634_);
v_a_673_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_652_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_652_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
v___jp_639_:
{
lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_642_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0));
v___x_643_ = 1;
v___x_644_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_634_, v___x_643_);
v___x_645_ = lean_string_append(v___x_642_, v___x_644_);
lean_dec_ref(v___x_644_);
v___x_646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___x_647_ = l_Lean_MessageData_ofFormat(v___x_646_);
v___x_648_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_647_, v___y_640_, v___y_641_);
return v___x_648_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetName_634_ = stack[0].m_obj;
lean_object* v_passes_635_ = stack[1].m_obj;
lean_object* v_a_636_ = stack[2].m_obj;
lean_object* v_a_637_ = stack[3].m_obj;
lean_object* v_res_681_;
v_res_681_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(v_targetName_634_, v_passes_635_, v_a_636_, v_a_637_);
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___boxed(lean_object* v_targetName_682_, lean_object* v_passes_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(v_targetName_682_, v_passes_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec_ref(v_passes_683_);
return v_res_687_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(lean_object* v_targetName_688_, lean_object* v_as_689_, size_t v_sz_690_, size_t v_i_691_, lean_object* v_b_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_688_, v_as_689_, v_sz_690_, v_i_691_, v_b_692_);
return v___x_696_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetName_688_ = stack[0].m_obj;
lean_object* v_as_689_ = stack[1].m_obj;
size_t v_sz_690_ = stack[2].m_num;
size_t v_i_691_ = stack[3].m_num;
lean_object* v_b_692_ = stack[4].m_obj;
lean_object* v___y_693_ = stack[5].m_obj;
lean_object* v___y_694_ = stack[6].m_obj;
lean_object* v_res_697_;
v_res_697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(v_targetName_688_, v_as_689_, v_sz_690_, v_i_691_, v_b_692_, v___y_693_, v___y_694_);
stack->m_obj
 = v_res_697_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___boxed(lean_object* v_targetName_698_, lean_object* v_as_699_, lean_object* v_sz_700_, lean_object* v_i_701_, lean_object* v_b_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
size_t v_sz_boxed_706_; size_t v_i_boxed_707_; lean_object* v_res_708_; 
v_sz_boxed_706_ = lean_unbox_usize(v_sz_700_);
lean_dec(v_sz_700_);
v_i_boxed_707_ = lean_unbox_usize(v_i_701_);
lean_dec(v_i_701_);
v_res_708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(v_targetName_698_, v_as_699_, v_sz_boxed_706_, v_i_boxed_707_, v_b_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec_ref(v_as_699_);
lean_dec(v_targetName_698_);
return v_res_708_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(lean_object* v_p_709_, lean_object* v_passes_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_array_push(v_passes_710_, v_p_709_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_709_ = stack[0].m_obj;
lean_object* v_passes_710_ = stack[1].m_obj;
lean_object* v___y_711_ = stack[2].m_obj;
lean_object* v___y_712_ = stack[3].m_obj;
lean_object* v_res_716_;
v_res_716_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(v_p_709_, v_passes_710_, v___y_711_, v___y_712_);
stack->m_obj
 = v_res_716_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed(lean_object* v_p_717_, lean_object* v_passes_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(v_p_717_, v_passes_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
return v_res_722_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(uint8_t v_phase_723_, lean_object* v_p_724_){
_start:
{
lean_object* v___f_725_; lean_object* v___x_726_; 
v___f_725_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_725_, 0, v_p_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_726_, 0, v___f_725_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*1, v_phase_723_);
return v___x_726_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installAtEnd_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_723_ = stack[0].m_num;
lean_object* v_p_724_ = stack[1].m_obj;
lean_object* v_res_727_;
v_res_727_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(v_phase_723_, v_p_724_);
stack->m_obj
 = v_res_727_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___boxed(lean_object* v_phase_728_, lean_object* v_p_729_){
_start:
{
uint8_t v_phase_boxed_730_; lean_object* v_res_731_; 
v_phase_boxed_730_ = lean_unbox(v_phase_728_);
v_res_731_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(v_phase_boxed_730_, v_p_729_);
return v_res_731_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(lean_object* v_passesNew_732_, lean_object* v_passes_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = l_Array_append___redArg(v_passes_733_, v_passesNew_732_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_append___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_passesNew_732_ = stack[0].m_obj;
lean_object* v_passes_733_ = stack[1].m_obj;
lean_object* v___y_734_ = stack[2].m_obj;
lean_object* v___y_735_ = stack[3].m_obj;
lean_object* v_res_739_;
v_res_739_ = l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(v_passesNew_732_, v_passes_733_, v___y_734_, v___y_735_);
stack->m_obj
 = v_res_739_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed(lean_object* v_passesNew_740_, lean_object* v_passes_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(v_passesNew_740_, v_passes_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec_ref(v_passesNew_740_);
return v_res_745_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_append(uint8_t v_phase_746_, lean_object* v_passesNew_747_){
_start:
{
lean_object* v___f_748_; lean_object* v___x_749_; 
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed), 5, 1);
lean_closure_set(v___f_748_, 0, v_passesNew_747_);
v___x_749_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_749_, 0, v___f_748_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*1, v_phase_746_);
return v___x_749_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_append_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_746_ = stack[0].m_num;
lean_object* v_passesNew_747_ = stack[1].m_obj;
lean_object* v_res_750_;
v_res_750_ = l_Lean_Compiler_LCNF_PassInstaller_append(v_phase_746_, v_passesNew_747_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___boxed(lean_object* v_phase_751_, lean_object* v_passesNew_752_){
_start:
{
uint8_t v_phase_boxed_753_; lean_object* v_res_754_; 
v_phase_boxed_753_ = lean_unbox(v_phase_751_);
v_res_754_ = l_Lean_Compiler_LCNF_PassInstaller_append(v_phase_boxed_753_, v_passesNew_752_);
return v_res_754_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(lean_object* v_msg_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___f_760_; lean_object* v___x_1599__overap_761_; lean_object* v___x_762_; 
v___f_760_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0));
v___x_1599__overap_761_ = lean_panic_fn_borrowed(v___f_760_, v_msg_756_);
lean_inc(v___y_758_);
lean_inc_ref(v___y_757_);
v___x_762_ = lean_apply_3(v___x_1599__overap_761_, v___y_757_, v___y_758_, lean_box(0));
return v___x_762_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_756_ = stack[0].m_obj;
lean_object* v___y_757_ = stack[1].m_obj;
lean_object* v___y_758_ = stack[2].m_obj;
lean_object* v_res_763_;
v_res_763_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v_msg_756_, v___y_757_, v___y_758_);
stack->m_obj
 = v_res_763_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___boxed(lean_object* v_msg_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v_msg_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_768_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(lean_object* v_install_769_, lean_object* v_b_770_, lean_object* v_____r_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; 
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
v___x_775_ = lean_apply_4(v_install_769_, v_b_770_, v___y_772_, v___y_773_, lean_box(0));
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_784_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_784_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_784_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v_a_776_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_a_785_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_775_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_775_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_install_769_ = stack[0].m_obj;
lean_object* v_b_770_ = stack[1].m_obj;
lean_object* v_____r_771_ = stack[2].m_obj;
lean_object* v___y_772_ = stack[3].m_obj;
lean_object* v___y_773_ = stack[4].m_obj;
lean_object* v_res_793_;
v_res_793_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_769_, v_b_770_, v_____r_771_, v___y_772_, v___y_773_);
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0___boxed(lean_object* v_install_794_, lean_object* v_b_795_, lean_object* v_____r_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_794_, v_b_795_, v_____r_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
return v_res_800_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_803_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1));
v___x_804_ = lean_unsigned_to_nat(8u);
v___x_805_ = lean_unsigned_to_nat(170u);
v___x_806_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0));
v___x_807_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0));
v___x_808_ = l_mkPanicMessageWithDecl(v___x_807_, v___x_806_, v___x_805_, v___x_804_, v___x_803_);
return v___x_808_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(lean_object* v_upperBound_809_, lean_object* v_f_810_, uint8_t v_phase_811_, lean_object* v_a_812_, lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___y_818_; uint8_t v___x_840_; 
v___x_840_ = lean_nat_dec_le(v_a_812_, v_upperBound_809_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v_a_812_);
lean_dec_ref(v_f_810_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v_b_813_);
return v___x_841_;
}
else
{
lean_object* v___x_842_; uint8_t v_phase_843_; lean_object* v_install_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
lean_inc_ref(v_f_810_);
lean_inc(v_a_812_);
v___x_842_ = lean_apply_1(v_f_810_, v_a_812_);
v_phase_843_ = lean_ctor_get_uint8(v___x_842_, sizeof(void*)*1);
v_install_844_ = lean_ctor_get(v___x_842_, 0);
lean_inc_ref(v_install_844_);
lean_dec_ref(v___x_842_);
v___x_845_ = lean_box(v_phase_843_);
v___x_846_ = lean_obj_tag_nat(v___x_845_);
lean_dec(v___x_845_);
v___x_847_ = lean_box(v_phase_811_);
v___x_848_ = lean_obj_tag_nat(v___x_847_);
lean_dec(v___x_847_);
v___x_849_ = lean_nat_dec_eq(v___x_846_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2);
v___x_851_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v___x_850_, v___y_814_, v___y_815_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
v___x_853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_844_, v_b_813_, v_a_852_, v___y_814_, v___y_815_);
v___y_818_ = v___x_853_;
goto v___jp_817_;
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec_ref(v_install_844_);
lean_dec_ref(v_b_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_f_810_);
v_a_854_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_851_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_851_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_box(0);
v___x_863_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_844_, v_b_813_, v___x_862_, v___y_814_, v___y_815_);
v___y_818_ = v___x_863_;
goto v___jp_817_;
}
}
v___jp_817_:
{
if (lean_obj_tag(v___y_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_831_; 
v_a_819_ = lean_ctor_get(v___y_818_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___y_818_);
if (v_isSharedCheck_831_ == 0)
{
v___x_821_ = v___y_818_;
v_isShared_822_ = v_isSharedCheck_831_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___y_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_831_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
if (lean_obj_tag(v_a_819_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; 
lean_dec(v_a_812_);
lean_dec_ref(v_f_810_);
v_a_823_ = lean_ctor_get(v_a_819_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v_a_819_, 1);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v_a_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_del_object(v___x_821_);
v_a_827_ = lean_ctor_get(v_a_819_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v_a_819_, 1);
v___x_828_ = lean_unsigned_to_nat(1u);
v___x_829_ = lean_nat_add(v_a_812_, v___x_828_);
lean_dec(v_a_812_);
v_a_812_ = v___x_829_;
v_b_813_ = v_a_827_;
goto _start;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_a_812_);
lean_dec_ref(v_f_810_);
v_a_832_ = lean_ctor_get(v___y_818_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___y_818_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___y_818_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___y_818_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_809_ = stack[0].m_obj;
lean_object* v_f_810_ = stack[1].m_obj;
uint8_t v_phase_811_ = stack[2].m_num;
lean_object* v_a_812_ = stack[3].m_obj;
lean_object* v_b_813_ = stack[4].m_obj;
lean_object* v___y_814_ = stack[5].m_obj;
lean_object* v___y_815_ = stack[6].m_obj;
lean_object* v_res_864_;
v_res_864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_809_, v_f_810_, v_phase_811_, v_a_812_, v_b_813_, v___y_814_, v___y_815_);
stack->m_obj
 = v_res_864_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___boxed(lean_object* v_upperBound_865_, lean_object* v_f_866_, lean_object* v_phase_867_, lean_object* v_a_868_, lean_object* v_b_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
uint8_t v_phase_boxed_873_; lean_object* v_res_874_; 
v_phase_boxed_873_ = lean_unbox(v_phase_867_);
v_res_874_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_865_, v_f_866_, v_phase_boxed_873_, v_a_868_, v_b_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v_upperBound_865_);
return v_res_874_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(lean_object* v_targetName_875_, lean_object* v_f_876_, uint8_t v_phase_877_, lean_object* v_passes_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(v_targetName_875_, v_passes_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v_fst_884_; lean_object* v_snd_885_; lean_object* v___x_886_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v_fst_884_ = lean_ctor_get(v_a_883_, 0);
lean_inc(v_fst_884_);
v_snd_885_ = lean_ctor_get(v_a_883_, 1);
lean_inc(v_snd_885_);
lean_dec(v_a_883_);
v___x_886_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_snd_885_, v_f_876_, v_phase_877_, v_fst_884_, v_passes_878_, v___y_879_, v___y_880_);
lean_dec(v_snd_885_);
return v___x_886_;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v_passes_878_);
lean_dec_ref(v_f_876_);
v_a_887_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_882_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_882_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetName_875_ = stack[0].m_obj;
lean_object* v_f_876_ = stack[1].m_obj;
uint8_t v_phase_877_ = stack[2].m_num;
lean_object* v_passes_878_ = stack[3].m_obj;
lean_object* v___y_879_ = stack[4].m_obj;
lean_object* v___y_880_ = stack[5].m_obj;
lean_object* v_res_895_;
v_res_895_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(v_targetName_875_, v_f_876_, v_phase_877_, v_passes_878_, v___y_879_, v___y_880_);
stack->m_obj
 = v_res_895_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed(lean_object* v_targetName_896_, lean_object* v_f_897_, lean_object* v_phase_898_, lean_object* v_passes_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
uint8_t v_phase_boxed_903_; lean_object* v_res_904_; 
v_phase_boxed_903_ = lean_unbox(v_phase_898_);
v_res_904_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(v_targetName_896_, v_f_897_, v_phase_boxed_903_, v_passes_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_904_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(uint8_t v_phase_905_, lean_object* v_targetName_906_, lean_object* v_f_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___x_910_; 
v___x_908_ = lean_box(v_phase_905_);
v___f_909_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed), 7, 3);
lean_closure_set(v___f_909_, 0, v_targetName_906_);
lean_closure_set(v___f_909_, 1, v_f_907_);
lean_closure_set(v___f_909_, 2, v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_910_, 0, v___f_909_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*1, v_phase_905_);
return v___x_910_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_905_ = stack[0].m_num;
lean_object* v_targetName_906_ = stack[1].m_obj;
lean_object* v_f_907_ = stack[2].m_obj;
lean_object* v_res_911_;
v_res_911_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_905_, v_targetName_906_, v_f_907_);
stack->m_obj
 = v_res_911_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___boxed(lean_object* v_phase_912_, lean_object* v_targetName_913_, lean_object* v_f_914_){
_start:
{
uint8_t v_phase_boxed_915_; lean_object* v_res_916_; 
v_phase_boxed_915_ = lean_unbox(v_phase_912_);
v_res_916_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_boxed_915_, v_targetName_913_, v_f_914_);
return v_res_916_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(lean_object* v_upperBound_917_, lean_object* v_f_918_, uint8_t v_phase_919_, lean_object* v_inst_920_, lean_object* v_R_921_, lean_object* v_a_922_, lean_object* v_b_923_, lean_object* v_c_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_917_, v_f_918_, v_phase_919_, v_a_922_, v_b_923_, v___y_925_, v___y_926_);
return v___x_928_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_917_ = stack[0].m_obj;
lean_object* v_f_918_ = stack[1].m_obj;
uint8_t v_phase_919_ = stack[2].m_num;
lean_object* v_a_922_ = stack[5].m_obj;
lean_object* v_b_923_ = stack[6].m_obj;
lean_object* v___y_925_ = stack[8].m_obj;
lean_object* v___y_926_ = stack[9].m_obj;
lean_object* v_res_929_;
v_res_929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(v_upperBound_917_, v_f_918_, v_phase_919_, lean_box(0), lean_box(0), v_a_922_, v_b_923_, lean_box(0), v___y_925_, v___y_926_);
stack->m_obj
 = v_res_929_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___boxed(lean_object* v_upperBound_930_, lean_object* v_f_931_, lean_object* v_phase_932_, lean_object* v_inst_933_, lean_object* v_R_934_, lean_object* v_a_935_, lean_object* v_b_936_, lean_object* v_c_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v_phase_boxed_941_; lean_object* v_res_942_; 
v_phase_boxed_941_ = lean_unbox(v_phase_932_);
v_res_942_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(v_upperBound_930_, v_f_931_, v_phase_boxed_941_, v_inst_933_, v_R_934_, v_a_935_, v_b_936_, v_c_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v_upperBound_930_);
return v_res_942_;
}
}
uint8_t l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(lean_object* v_targetName_943_, lean_object* v_occurrence_944_, lean_object* v_p_945_){
_start:
{
lean_object* v_occurrence_946_; lean_object* v_name_947_; uint8_t v___x_948_; 
v_occurrence_946_ = lean_ctor_get(v_p_945_, 0);
v_name_947_ = lean_ctor_get(v_p_945_, 1);
v___x_948_ = lean_name_eq(v_name_947_, v_targetName_943_);
if (v___x_948_ == 0)
{
return v___x_948_;
}
else
{
uint8_t v___x_949_; 
v___x_949_ = lean_nat_dec_eq(v_occurrence_946_, v_occurrence_944_);
return v___x_949_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetName_943_ = stack[0].m_obj;
lean_object* v_occurrence_944_ = stack[1].m_obj;
lean_object* v_p_945_ = stack[2].m_obj;
uint8_t v_res_950_;
v_res_950_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(v_targetName_943_, v_occurrence_944_, v_p_945_);
stack->m_num = v_res_950_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed(lean_object* v_targetName_951_, lean_object* v_occurrence_952_, lean_object* v_p_953_){
_start:
{
uint8_t v_res_954_; lean_object* v_r_955_; 
v_res_954_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(v_targetName_951_, v_occurrence_952_, v_p_953_);
lean_dec_ref(v_p_953_);
lean_dec(v_occurrence_952_);
lean_dec(v_targetName_951_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(lean_object* v___f_960_, lean_object* v_p_961_, lean_object* v_targetName_962_, lean_object* v_occurrence_963_, lean_object* v_passes_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_960_, v_passes_964_, v___x_968_);
if (lean_obj_tag(v___x_969_) == 1)
{
lean_object* v_val_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_occurrence_963_);
lean_dec(v_targetName_962_);
v_val_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_984_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_984_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_val_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_984_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_passUnderTest_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v_j_978_; lean_object* v_as_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v_passUnderTest_974_ = lean_array_fget_borrowed(v_passes_964_, v_val_970_);
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_nat_add(v_val_970_, v___x_975_);
lean_dec(v_val_970_);
lean_inc(v_passUnderTest_974_);
v___x_977_ = lean_apply_1(v_p_961_, v_passUnderTest_974_);
v_j_978_ = lean_array_get_size(v_passes_964_);
v_as_979_ = lean_array_push(v_passes_964_, v___x_977_);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_976_, v_as_979_, v_j_978_);
lean_dec(v___x_976_);
if (v_isShared_973_ == 0)
{
lean_ctor_set_tag(v___x_972_, 0);
lean_ctor_set(v___x_972_, 0, v___x_980_);
v___x_982_ = v___x_972_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
else
{
lean_object* v___x_985_; uint8_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v___x_969_);
lean_dec_ref(v_passes_964_);
lean_dec_ref(v_p_961_);
v___x_985_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0));
v___x_986_ = 1;
v___x_987_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_962_, v___x_986_);
v___x_988_ = lean_string_append(v___x_985_, v___x_987_);
v___x_989_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
v___x_991_ = l_Nat_reprFast(v_occurrence_963_);
v___x_992_ = lean_string_append(v___x_990_, v___x_991_);
lean_dec_ref(v___x_991_);
v___x_993_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_994_ = lean_string_append(v___x_992_, v___x_993_);
v___x_995_ = lean_string_append(v___x_994_, v___x_987_);
lean_dec_ref(v___x_987_);
v___x_996_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_997_ = lean_string_append(v___x_995_, v___x_996_);
v___x_998_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
v___x_999_ = l_Lean_MessageData_ofFormat(v___x_998_);
v___x_1000_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_999_, v___y_965_, v___y_966_);
return v___x_1000_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_960_ = stack[0].m_obj;
lean_object* v_p_961_ = stack[1].m_obj;
lean_object* v_targetName_962_ = stack[2].m_obj;
lean_object* v_occurrence_963_ = stack[3].m_obj;
lean_object* v_passes_964_ = stack[4].m_obj;
lean_object* v___y_965_ = stack[5].m_obj;
lean_object* v___y_966_ = stack[6].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(v___f_960_, v_p_961_, v_targetName_962_, v_occurrence_963_, v_passes_964_, v___y_965_, v___y_966_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed(lean_object* v___f_1002_, lean_object* v_p_1003_, lean_object* v_targetName_1004_, lean_object* v_occurrence_1005_, lean_object* v_passes_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(v___f_1002_, v_p_1003_, v_targetName_1004_, v_occurrence_1005_, v_passes_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1010_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter(uint8_t v_phase_1011_, lean_object* v_targetName_1012_, lean_object* v_p_1013_, lean_object* v_occurrence_1014_){
_start:
{
lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; 
lean_inc(v_occurrence_1014_);
lean_inc(v_targetName_1012_);
v___f_1015_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1015_, 0, v_targetName_1012_);
lean_closure_set(v___f_1015_, 1, v_occurrence_1014_);
v___f_1016_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1016_, 0, v___f_1015_);
lean_closure_set(v___f_1016_, 1, v_p_1013_);
lean_closure_set(v___f_1016_, 2, v_targetName_1012_);
lean_closure_set(v___f_1016_, 3, v_occurrence_1014_);
v___x_1017_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1017_, 0, v___f_1016_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*1, v_phase_1011_);
return v___x_1017_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installAfter_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_1011_ = stack[0].m_num;
lean_object* v_targetName_1012_ = stack[1].m_obj;
lean_object* v_p_1013_ = stack[2].m_obj;
lean_object* v_occurrence_1014_ = stack[3].m_obj;
lean_object* v_res_1018_;
v_res_1018_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_1011_, v_targetName_1012_, v_p_1013_, v_occurrence_1014_);
stack->m_obj
 = v_res_1018_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___boxed(lean_object* v_phase_1019_, lean_object* v_targetName_1020_, lean_object* v_p_1021_, lean_object* v_occurrence_1022_){
_start:
{
uint8_t v_phase_boxed_1023_; lean_object* v_res_1024_; 
v_phase_boxed_1023_ = lean_unbox(v_phase_1019_);
v_res_1024_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_boxed_1023_, v_targetName_1020_, v_p_1021_, v_occurrence_1022_);
return v_res_1024_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(uint8_t v_phase_1025_, lean_object* v_targetName_1026_, lean_object* v_p_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_1025_, v_targetName_1026_, v_p_1027_, v_x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_1025_ = stack[0].m_num;
lean_object* v_targetName_1026_ = stack[1].m_obj;
lean_object* v_p_1027_ = stack[2].m_obj;
lean_object* v_x_1028_ = stack[3].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(v_phase_1025_, v_targetName_1026_, v_p_1027_, v_x_1028_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed(lean_object* v_phase_1031_, lean_object* v_targetName_1032_, lean_object* v_p_1033_, lean_object* v_x_1034_){
_start:
{
uint8_t v_phase_boxed_1035_; lean_object* v_res_1036_; 
v_phase_boxed_1035_ = lean_unbox(v_phase_1031_);
v_res_1036_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(v_phase_boxed_1035_, v_targetName_1032_, v_p_1033_, v_x_1034_);
return v_res_1036_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(uint8_t v_phase_1037_, lean_object* v_targetName_1038_, lean_object* v_p_1039_){
_start:
{
lean_object* v___x_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; 
v___x_1040_ = lean_box(v_phase_1037_);
lean_inc(v_targetName_1038_);
v___f_1041_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1041_, 0, v___x_1040_);
lean_closure_set(v___f_1041_, 1, v_targetName_1038_);
lean_closure_set(v___f_1041_, 2, v_p_1039_);
v___x_1042_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1037_, v_targetName_1038_, v___f_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installAfterEach_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_1037_ = stack[0].m_num;
lean_object* v_targetName_1038_ = stack[1].m_obj;
lean_object* v_p_1039_ = stack[2].m_obj;
lean_object* v_res_1043_;
v_res_1043_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(v_phase_1037_, v_targetName_1038_, v_p_1039_);
stack->m_obj
 = v_res_1043_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___boxed(lean_object* v_phase_1044_, lean_object* v_targetName_1045_, lean_object* v_p_1046_){
_start:
{
uint8_t v_phase_boxed_1047_; lean_object* v_res_1048_; 
v_phase_boxed_1047_ = lean_unbox(v_phase_1044_);
v_res_1048_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(v_phase_boxed_1047_, v_targetName_1045_, v_p_1046_);
return v_res_1048_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(lean_object* v___f_1049_, lean_object* v_p_1050_, lean_object* v_targetName_1051_, lean_object* v_occurrence_1052_, lean_object* v_passes_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1049_, v_passes_1053_, v___x_1057_);
if (lean_obj_tag(v___x_1058_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_occurrence_1052_);
lean_dec(v_targetName_1051_);
v_val_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1071_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1071_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_passUnderTest_1063_; lean_object* v___x_1064_; lean_object* v_j_1065_; lean_object* v_as_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
v_passUnderTest_1063_ = lean_array_fget_borrowed(v_passes_1053_, v_val_1059_);
lean_inc(v_passUnderTest_1063_);
v___x_1064_ = lean_apply_1(v_p_1050_, v_passUnderTest_1063_);
v_j_1065_ = lean_array_get_size(v_passes_1053_);
v_as_1066_ = lean_array_push(v_passes_1053_, v___x_1064_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_val_1059_, v_as_1066_, v_j_1065_);
lean_dec(v_val_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1067_);
v___x_1069_ = v___x_1061_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v___x_1058_);
lean_dec_ref(v_passes_1053_);
lean_dec_ref(v_p_1050_);
v___x_1072_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0));
v___x_1073_ = 1;
v___x_1074_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_1051_, v___x_1073_);
v___x_1075_ = lean_string_append(v___x_1072_, v___x_1074_);
v___x_1076_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_1077_ = lean_string_append(v___x_1075_, v___x_1076_);
v___x_1078_ = l_Nat_reprFast(v_occurrence_1052_);
v___x_1079_ = lean_string_append(v___x_1077_, v___x_1078_);
lean_dec_ref(v___x_1078_);
v___x_1080_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_1081_ = lean_string_append(v___x_1079_, v___x_1080_);
v___x_1082_ = lean_string_append(v___x_1081_, v___x_1074_);
lean_dec_ref(v___x_1074_);
v___x_1083_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_1084_ = lean_string_append(v___x_1082_, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
v___x_1086_ = l_Lean_MessageData_ofFormat(v___x_1085_);
v___x_1087_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1086_, v___y_1054_, v___y_1055_);
return v___x_1087_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1049_ = stack[0].m_obj;
lean_object* v_p_1050_ = stack[1].m_obj;
lean_object* v_targetName_1051_ = stack[2].m_obj;
lean_object* v_occurrence_1052_ = stack[3].m_obj;
lean_object* v_passes_1053_ = stack[4].m_obj;
lean_object* v___y_1054_ = stack[5].m_obj;
lean_object* v___y_1055_ = stack[6].m_obj;
lean_object* v_res_1088_;
v_res_1088_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(v___f_1049_, v_p_1050_, v_targetName_1051_, v_occurrence_1052_, v_passes_1053_, v___y_1054_, v___y_1055_);
stack->m_obj
 = v_res_1088_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed(lean_object* v___f_1089_, lean_object* v_p_1090_, lean_object* v_targetName_1091_, lean_object* v_occurrence_1092_, lean_object* v_passes_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(v___f_1089_, v_p_1090_, v_targetName_1091_, v_occurrence_1092_, v_passes_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1097_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore(uint8_t v_phase_1098_, lean_object* v_targetName_1099_, lean_object* v_p_1100_, lean_object* v_occurrence_1101_){
_start:
{
lean_object* v___f_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; 
lean_inc(v_occurrence_1101_);
lean_inc(v_targetName_1099_);
v___f_1102_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1102_, 0, v_targetName_1099_);
lean_closure_set(v___f_1102_, 1, v_occurrence_1101_);
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1103_, 0, v___f_1102_);
lean_closure_set(v___f_1103_, 1, v_p_1100_);
lean_closure_set(v___f_1103_, 2, v_targetName_1099_);
lean_closure_set(v___f_1103_, 3, v_occurrence_1101_);
v___x_1104_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1104_, 0, v___f_1103_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*1, v_phase_1098_);
return v___x_1104_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installBefore_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_1098_ = stack[0].m_num;
lean_object* v_targetName_1099_ = stack[1].m_obj;
lean_object* v_p_1100_ = stack[2].m_obj;
lean_object* v_occurrence_1101_ = stack[3].m_obj;
lean_object* v_res_1105_;
v_res_1105_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_1098_, v_targetName_1099_, v_p_1100_, v_occurrence_1101_);
stack->m_obj
 = v_res_1105_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___boxed(lean_object* v_phase_1106_, lean_object* v_targetName_1107_, lean_object* v_p_1108_, lean_object* v_occurrence_1109_){
_start:
{
uint8_t v_phase_boxed_1110_; lean_object* v_res_1111_; 
v_phase_boxed_1110_ = lean_unbox(v_phase_1106_);
v_res_1111_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_boxed_1110_, v_targetName_1107_, v_p_1108_, v_occurrence_1109_);
return v_res_1111_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(uint8_t v_phase_1112_, lean_object* v_targetName_1113_, lean_object* v_p_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_1112_, v_targetName_1113_, v_p_1114_, v_x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_1112_ = stack[0].m_num;
lean_object* v_targetName_1113_ = stack[1].m_obj;
lean_object* v_p_1114_ = stack[2].m_obj;
lean_object* v_x_1115_ = stack[3].m_obj;
lean_object* v_res_1117_;
v_res_1117_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(v_phase_1112_, v_targetName_1113_, v_p_1114_, v_x_1115_);
stack->m_obj
 = v_res_1117_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed(lean_object* v_phase_1118_, lean_object* v_targetName_1119_, lean_object* v_p_1120_, lean_object* v_x_1121_){
_start:
{
uint8_t v_phase_boxed_1122_; lean_object* v_res_1123_; 
v_phase_boxed_1122_ = lean_unbox(v_phase_1118_);
v_res_1123_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(v_phase_boxed_1122_, v_targetName_1119_, v_p_1120_, v_x_1121_);
return v_res_1123_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(uint8_t v_phase_1124_, lean_object* v_targetName_1125_, lean_object* v_p_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___f_1128_; lean_object* v___x_1129_; 
v___x_1127_ = lean_box(v_phase_1124_);
lean_inc(v_targetName_1125_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1128_, 0, v___x_1127_);
lean_closure_set(v___f_1128_, 1, v_targetName_1125_);
lean_closure_set(v___f_1128_, 2, v_p_1126_);
v___x_1129_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1124_, v_targetName_1125_, v___f_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_1124_ = stack[0].m_num;
lean_object* v_targetName_1125_ = stack[1].m_obj;
lean_object* v_p_1126_ = stack[2].m_obj;
lean_object* v_res_1130_;
v_res_1130_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(v_phase_1124_, v_targetName_1125_, v_p_1126_);
stack->m_obj
 = v_res_1130_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___boxed(lean_object* v_phase_1131_, lean_object* v_targetName_1132_, lean_object* v_p_1133_){
_start:
{
uint8_t v_phase_boxed_1134_; lean_object* v_res_1135_; 
v_phase_boxed_1134_ = lean_unbox(v_phase_1131_);
v_res_1135_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(v_phase_boxed_1134_, v_targetName_1132_, v_p_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(lean_object* v_targetName_1136_, lean_object* v_occurrence_1137_, lean_object* v_as_1138_, lean_object* v_j_1139_){
_start:
{
uint8_t v___y_1141_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = lean_array_get_size(v_as_1138_);
v___x_1147_ = lean_nat_dec_lt(v_j_1139_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_dec(v_j_1139_);
v___x_1148_ = lean_box(0);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; lean_object* v_occurrence_1150_; lean_object* v_name_1151_; uint8_t v___x_1152_; 
v___x_1149_ = lean_array_fget_borrowed(v_as_1138_, v_j_1139_);
v_occurrence_1150_ = lean_ctor_get(v___x_1149_, 0);
v_name_1151_ = lean_ctor_get(v___x_1149_, 1);
v___x_1152_ = lean_name_eq(v_name_1151_, v_targetName_1136_);
if (v___x_1152_ == 0)
{
v___y_1141_ = v___x_1152_;
goto v___jp_1140_;
}
else
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_nat_dec_eq(v_occurrence_1150_, v_occurrence_1137_);
v___y_1141_ = v___x_1153_;
goto v___jp_1140_;
}
}
v___jp_1140_:
{
if (v___y_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = lean_nat_add(v_j_1139_, v___x_1142_);
lean_dec(v_j_1139_);
v_j_1139_ = v___x_1143_;
goto _start;
}
else
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_j_1139_);
return v___x_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0___boxed(lean_object* v_targetName_1154_, lean_object* v_occurrence_1155_, lean_object* v_as_1156_, lean_object* v_j_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_1154_, v_occurrence_1155_, v_as_1156_, v_j_1157_);
lean_dec_ref(v_as_1156_);
lean_dec(v_occurrence_1155_);
lean_dec(v_targetName_1154_);
return v_res_1158_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(lean_object* v_targetName_1160_, lean_object* v_occurrence_1161_, lean_object* v_p_1162_, lean_object* v_passes_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_1160_, v_occurrence_1161_, v_passes_1163_, v___x_1167_);
if (lean_obj_tag(v___x_1168_) == 1)
{
lean_object* v_val_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_occurrence_1161_);
lean_dec(v_targetName_1160_);
v_val_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1186_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_val_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1186_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_array_get_size(v_passes_1163_);
v___x_1174_ = lean_nat_dec_lt(v_val_1169_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1176_; 
lean_dec(v_val_1169_);
lean_dec_ref(v_p_1162_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set_tag(v___x_1171_, 0);
lean_ctor_set(v___x_1171_, 0, v_passes_1163_);
v___x_1176_ = v___x_1171_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_passes_1163_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
else
{
lean_object* v_v_1178_; lean_object* v___x_1179_; lean_object* v_xs_x27_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v_v_1178_ = lean_array_fget(v_passes_1163_, v_val_1169_);
v___x_1179_ = lean_box(0);
v_xs_x27_1180_ = lean_array_fset(v_passes_1163_, v_val_1169_, v___x_1179_);
v___x_1181_ = lean_apply_1(v_p_1162_, v_v_1178_);
v___x_1182_ = lean_array_fset(v_xs_x27_1180_, v_val_1169_, v___x_1181_);
lean_dec(v_val_1169_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set_tag(v___x_1171_, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1182_);
v___x_1184_ = v___x_1171_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec(v___x_1168_);
lean_dec_ref(v_passes_1163_);
lean_dec_ref(v_p_1162_);
v___x_1187_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0));
v___x_1188_ = 1;
v___x_1189_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_1160_, v___x_1188_);
v___x_1190_ = lean_string_append(v___x_1187_, v___x_1189_);
v___x_1191_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_1192_ = lean_string_append(v___x_1190_, v___x_1191_);
v___x_1193_ = l_Nat_reprFast(v_occurrence_1161_);
v___x_1194_ = lean_string_append(v___x_1192_, v___x_1193_);
lean_dec_ref(v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_1196_ = lean_string_append(v___x_1194_, v___x_1195_);
v___x_1197_ = lean_string_append(v___x_1196_, v___x_1189_);
lean_dec_ref(v___x_1189_);
v___x_1198_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_1199_ = lean_string_append(v___x_1197_, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
v___x_1201_ = l_Lean_MessageData_ofFormat(v___x_1200_);
v___x_1202_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1201_, v___y_1164_, v___y_1165_);
return v___x_1202_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_targetName_1160_ = stack[0].m_obj;
lean_object* v_occurrence_1161_ = stack[1].m_obj;
lean_object* v_p_1162_ = stack[2].m_obj;
lean_object* v_passes_1163_ = stack[3].m_obj;
lean_object* v___y_1164_ = stack[4].m_obj;
lean_object* v___y_1165_ = stack[5].m_obj;
lean_object* v_res_1203_;
v_res_1203_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(v_targetName_1160_, v_occurrence_1161_, v_p_1162_, v_passes_1163_, v___y_1164_, v___y_1165_);
stack->m_obj
 = v_res_1203_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed(lean_object* v_targetName_1204_, lean_object* v_occurrence_1205_, lean_object* v_p_1206_, lean_object* v_passes_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(v_targetName_1204_, v_occurrence_1205_, v_p_1206_, v_passes_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
return v_res_1211_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass(uint8_t v_phase_1212_, lean_object* v_targetName_1213_, lean_object* v_p_1214_, lean_object* v_occurrence_1215_){
_start:
{
lean_object* v___f_1216_; lean_object* v___x_1217_; 
v___f_1216_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1216_, 0, v_targetName_1213_);
lean_closure_set(v___f_1216_, 1, v_occurrence_1215_);
lean_closure_set(v___f_1216_, 2, v_p_1214_);
v___x_1217_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1217_, 0, v___f_1216_);
lean_ctor_set_uint8(v___x_1217_, sizeof(void*)*1, v_phase_1212_);
return v___x_1217_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_replacePass_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_1212_ = stack[0].m_num;
lean_object* v_targetName_1213_ = stack[1].m_obj;
lean_object* v_p_1214_ = stack[2].m_obj;
lean_object* v_occurrence_1215_ = stack[3].m_obj;
lean_object* v_res_1218_;
v_res_1218_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_1212_, v_targetName_1213_, v_p_1214_, v_occurrence_1215_);
stack->m_obj
 = v_res_1218_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___boxed(lean_object* v_phase_1219_, lean_object* v_targetName_1220_, lean_object* v_p_1221_, lean_object* v_occurrence_1222_){
_start:
{
uint8_t v_phase_boxed_1223_; lean_object* v_res_1224_; 
v_phase_boxed_1223_ = lean_unbox(v_phase_1219_);
v_res_1224_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_boxed_1223_, v_targetName_1220_, v_p_1221_, v_occurrence_1222_);
return v_res_1224_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(uint8_t v_phase_1225_, lean_object* v_targetName_1226_, lean_object* v_p_1227_, lean_object* v_x_1228_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_1225_, v_targetName_1226_, v_p_1227_, v_x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_1225_ = stack[0].m_num;
lean_object* v_targetName_1226_ = stack[1].m_obj;
lean_object* v_p_1227_ = stack[2].m_obj;
lean_object* v_x_1228_ = stack[3].m_obj;
lean_object* v_res_1230_;
v_res_1230_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(v_phase_1225_, v_targetName_1226_, v_p_1227_, v_x_1228_);
stack->m_obj
 = v_res_1230_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed(lean_object* v_phase_1231_, lean_object* v_targetName_1232_, lean_object* v_p_1233_, lean_object* v_x_1234_){
_start:
{
uint8_t v_phase_boxed_1235_; lean_object* v_res_1236_; 
v_phase_boxed_1235_ = lean_unbox(v_phase_1231_);
v_res_1236_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(v_phase_boxed_1235_, v_targetName_1232_, v_p_1233_, v_x_1234_);
return v_res_1236_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(uint8_t v_phase_1237_, lean_object* v_targetName_1238_, lean_object* v_p_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___f_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_box(v_phase_1237_);
lean_inc(v_targetName_1238_);
v___f_1241_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1241_, 0, v___x_1240_);
lean_closure_set(v___f_1241_, 1, v_targetName_1238_);
lean_closure_set(v___f_1241_, 2, v_p_1239_);
v___x_1242_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1237_, v_targetName_1238_, v___f_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence_0interp(lean_interpreter_value* stack)
{
uint8_t v_phase_1237_ = stack[0].m_num;
lean_object* v_targetName_1238_ = stack[1].m_obj;
lean_object* v_p_1239_ = stack[2].m_obj;
lean_object* v_res_1243_;
v_res_1243_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(v_phase_1237_, v_targetName_1238_, v_p_1239_);
stack->m_obj
 = v_res_1243_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___boxed(lean_object* v_phase_1244_, lean_object* v_targetName_1245_, lean_object* v_p_1246_){
_start:
{
uint8_t v_phase_boxed_1247_; lean_object* v_res_1248_; 
v_phase_boxed_1247_ = lean_unbox(v_phase_1244_);
v_res_1248_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(v_phase_boxed_1247_, v_targetName_1245_, v_p_1246_);
return v_res_1248_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_run(lean_object* v_manager_1249_, lean_object* v_installer_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
uint8_t v_phase_1254_; 
v_phase_1254_ = lean_ctor_get_uint8(v_installer_1250_, sizeof(void*)*1);
switch(v_phase_1254_)
{
case 0:
{
lean_object* v_install_1255_; lean_object* v_basePasses_1256_; lean_object* v_monoPasses_1257_; lean_object* v_monoPassesNoLambda_1258_; lean_object* v_impurePasses_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1283_; 
v_install_1255_ = lean_ctor_get(v_installer_1250_, 0);
lean_inc_ref(v_install_1255_);
lean_dec_ref(v_installer_1250_);
v_basePasses_1256_ = lean_ctor_get(v_manager_1249_, 0);
v_monoPasses_1257_ = lean_ctor_get(v_manager_1249_, 1);
v_monoPassesNoLambda_1258_ = lean_ctor_get(v_manager_1249_, 2);
v_impurePasses_1259_ = lean_ctor_get(v_manager_1249_, 3);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_manager_1249_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1261_ = v_manager_1249_;
v_isShared_1262_ = v_isSharedCheck_1283_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_impurePasses_1259_);
lean_inc(v_monoPassesNoLambda_1258_);
lean_inc(v_monoPasses_1257_);
lean_inc(v_basePasses_1256_);
lean_dec(v_manager_1249_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1283_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; 
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_1263_ = lean_apply_4(v_install_1255_, v_basePasses_1256_, v_a_1251_, v_a_1252_, lean_box(0));
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1274_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v_a_1264_);
v___x_1269_ = v___x_1261_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1264_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_monoPasses_1257_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_monoPassesNoLambda_1258_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_impurePasses_1259_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1269_);
v___x_1271_ = v___x_1266_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_del_object(v___x_1261_);
lean_dec_ref(v_impurePasses_1259_);
lean_dec_ref(v_monoPassesNoLambda_1258_);
lean_dec_ref(v_monoPasses_1257_);
v_a_1275_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1263_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1263_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
case 1:
{
lean_object* v_install_1284_; lean_object* v_basePasses_1285_; lean_object* v_monoPasses_1286_; lean_object* v_monoPassesNoLambda_1287_; lean_object* v_impurePasses_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1312_; 
v_install_1284_ = lean_ctor_get(v_installer_1250_, 0);
lean_inc_ref(v_install_1284_);
lean_dec_ref(v_installer_1250_);
v_basePasses_1285_ = lean_ctor_get(v_manager_1249_, 0);
v_monoPasses_1286_ = lean_ctor_get(v_manager_1249_, 1);
v_monoPassesNoLambda_1287_ = lean_ctor_get(v_manager_1249_, 2);
v_impurePasses_1288_ = lean_ctor_get(v_manager_1249_, 3);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_manager_1249_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1290_ = v_manager_1249_;
v_isShared_1291_ = v_isSharedCheck_1312_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_impurePasses_1288_);
lean_inc(v_monoPassesNoLambda_1287_);
lean_inc(v_monoPasses_1286_);
lean_inc(v_basePasses_1285_);
lean_dec(v_manager_1249_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1312_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; 
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_1292_ = lean_apply_4(v_install_1284_, v_monoPasses_1286_, v_a_1251_, v_a_1252_, lean_box(0));
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1303_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1295_ = v___x_1292_;
v_isShared_1296_ = v_isSharedCheck_1303_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1292_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1303_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v_a_1293_);
v___x_1298_ = v___x_1290_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_basePasses_1285_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_a_1293_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_monoPassesNoLambda_1287_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v_impurePasses_1288_);
v___x_1298_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1300_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 0, v___x_1298_);
v___x_1300_ = v___x_1295_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_del_object(v___x_1290_);
lean_dec_ref(v_impurePasses_1288_);
lean_dec_ref(v_monoPassesNoLambda_1287_);
lean_dec_ref(v_basePasses_1285_);
v_a_1304_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1292_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1292_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
default: 
{
lean_object* v_install_1313_; lean_object* v_basePasses_1314_; lean_object* v_monoPasses_1315_; lean_object* v_monoPassesNoLambda_1316_; lean_object* v_impurePasses_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1341_; 
v_install_1313_ = lean_ctor_get(v_installer_1250_, 0);
lean_inc_ref(v_install_1313_);
lean_dec_ref(v_installer_1250_);
v_basePasses_1314_ = lean_ctor_get(v_manager_1249_, 0);
v_monoPasses_1315_ = lean_ctor_get(v_manager_1249_, 1);
v_monoPassesNoLambda_1316_ = lean_ctor_get(v_manager_1249_, 2);
v_impurePasses_1317_ = lean_ctor_get(v_manager_1249_, 3);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_manager_1249_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1319_ = v_manager_1249_;
v_isShared_1320_ = v_isSharedCheck_1341_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_impurePasses_1317_);
lean_inc(v_monoPassesNoLambda_1316_);
lean_inc(v_monoPasses_1315_);
lean_inc(v_basePasses_1314_);
lean_dec(v_manager_1249_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1341_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; 
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_1321_ = lean_apply_4(v_install_1313_, v_impurePasses_1317_, v_a_1251_, v_a_1252_, lean_box(0));
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1332_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1332_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1332_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 3, v_a_1322_);
v___x_1327_ = v___x_1319_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_basePasses_1314_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_monoPasses_1315_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_monoPassesNoLambda_1316_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1327_);
v___x_1329_ = v___x_1324_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_del_object(v___x_1319_);
lean_dec_ref(v_monoPassesNoLambda_1316_);
lean_dec_ref(v_monoPasses_1315_);
lean_dec_ref(v_basePasses_1314_);
v_a_1333_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1321_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1321_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_manager_1249_ = stack[0].m_obj;
lean_object* v_installer_1250_ = stack[1].m_obj;
lean_object* v_a_1251_ = stack[2].m_obj;
lean_object* v_a_1252_ = stack[3].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1249_, v_installer_1250_, v_a_1251_, v_a_1252_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run___boxed(lean_object* v_manager_1343_, lean_object* v_installer_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1343_, v_installer_1344_, v_a_1345_, v_a_1346_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
return v_res_1348_;
}
}
lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(lean_object* v_x_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
if (lean_obj_tag(v_x_1349_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_a_1353_ = lean_ctor_get(v_x_1349_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v_x_1349_, 1);
v___x_1354_ = l_Lean_stringToMessageData(v_a_1353_);
v___x_1355_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1354_, v___y_1350_, v___y_1351_);
return v___x_1355_;
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_a_1356_ = lean_ctor_get(v_x_1349_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_x_1349_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v_x_1349_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v_x_1349_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set_tag(v___x_1358_, 0);
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1349_ = stack[0].m_obj;
lean_object* v___y_1350_ = stack[1].m_obj;
lean_object* v___y_1351_ = stack[2].m_obj;
lean_object* v_res_1364_;
v_res_1364_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1349_, v___y_1350_, v___y_1351_);
stack->m_obj
 = v_res_1364_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg___boxed(lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1369_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(lean_object* v_declName_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v___x_1382_; lean_object* v_env_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1382_ = lean_st_ref_get(v_a_1380_);
v_env_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc_ref(v_env_1383_);
lean_dec(v___x_1382_);
v___x_1384_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1379_);
v___x_1385_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3));
v___x_1386_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1383_, v___x_1384_, v___x_1385_, v_declName_1378_);
lean_dec_ref(v___x_1384_);
v___x_1387_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v___x_1386_, v_a_1379_, v_a_1380_);
return v___x_1387_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1378_ = stack[0].m_obj;
lean_object* v_a_1379_ = stack[1].m_obj;
lean_object* v_a_1380_ = stack[2].m_obj;
lean_object* v_res_1388_;
v_res_1388_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1378_, v_a_1379_, v_a_1380_);
stack->m_obj
 = v_res_1388_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___boxed(lean_object* v_declName_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
return v_res_1393_;
}
}
lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(lean_object* v_00_u03b1_1394_, lean_object* v_x_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1395_, v___y_1396_, v___y_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT void l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1395_ = stack[1].m_obj;
lean_object* v___y_1396_ = stack[2].m_obj;
lean_object* v___y_1397_ = stack[3].m_obj;
lean_object* v_res_1400_;
v_res_1400_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(lean_box(0), v_x_1395_, v___y_1396_, v___y_1397_);
stack->m_obj
 = v_res_1400_;
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(v_00_u03b1_1401_, v_x_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1406_;
}
}
lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object* v_manager_1407_, lean_object* v_declName_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1408_, v_a_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1407_, v_a_1413_, v_a_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1416_ = l_Lean_Compiler_LCNF_PassManager_validate(v_a_1415_, v_a_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v___x_1416_, 0);
lean_dec(v_unused_1424_);
v___x_1418_ = v___x_1416_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_dec(v___x_1416_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v_a_1415_);
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1415_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_a_1415_);
v_a_1425_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1416_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1416_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
else
{
return v___x_1414_;
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_manager_1407_);
v_a_1433_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1412_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1412_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_PassInstaller_runFromDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_manager_1407_ = stack[0].m_obj;
lean_object* v_declName_1408_ = stack[1].m_obj;
lean_object* v_a_1409_ = stack[2].m_obj;
lean_object* v_a_1410_ = stack[3].m_obj;
lean_object* v_res_1441_;
v_res_1441_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_manager_1407_, v_declName_1408_, v_a_1409_, v_a_1410_);
stack->m_obj
 = v_res_1441_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl___boxed(lean_object* v_manager_1442_, lean_object* v_declName_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_manager_1442_, v_declName_1443_, v_a_1444_, v_a_1445_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
return v_res_1447_;
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
