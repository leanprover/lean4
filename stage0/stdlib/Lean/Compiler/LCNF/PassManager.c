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
extern lean_object* l_Lean_instInhabitedMessageData_default;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___closed__0;
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
uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_30_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_pp_27_);
v___x_31_ = lean_box(v___x_30_);
v___x_32_ = lean_obj_tag_nat(v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_box(v_ip_28_);
v___x_34_ = lean_obj_tag_nat(v___x_33_);
lean_dec(v___x_33_);
v___x_35_ = lean_nat_dec_eq(v___x_32_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___y_41_; lean_object* v___y_42_; lean_object* v___x_48_; lean_object* v___y_50_; 
lean_dec(v_x_29_);
v___x_36_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0));
v___x_37_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__1));
v___x_38_ = lean_unsigned_to_nat(33u);
v___x_39_ = lean_unsigned_to_nat(4u);
v___x_48_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__3));
switch(v_pp_27_)
{
case 0:
{
lean_object* v___x_56_; 
v___x_56_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_50_ = v___x_56_;
goto v___jp_49_;
}
case 1:
{
lean_object* v___x_57_; 
v___x_57_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_50_ = v___x_57_;
goto v___jp_49_;
}
default: 
{
lean_object* v___x_58_; 
v___x_58_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_50_ = v___x_58_;
goto v___jp_49_;
}
}
v___jp_40_:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_43_ = lean_string_append(v___y_41_, v___y_42_);
v___x_44_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__2));
v___x_45_ = lean_string_append(v___x_43_, v___x_44_);
v___x_46_ = l_mkPanicMessageWithDecl(v___x_36_, v___x_37_, v___x_38_, v___x_39_, v___x_45_);
lean_dec_ref(v___x_45_);
v___x_47_ = l_panic___redArg(v_inst_26_, v___x_46_);
return v___x_47_;
}
v___jp_49_:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_string_append(v___x_48_, v___y_50_);
v___x_52_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__4));
v___x_53_ = lean_string_append(v___x_51_, v___x_52_);
if (v_ip_28_ == 0)
{
lean_object* v___x_54_; 
v___x_54_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__5));
v___y_41_ = v___x_53_;
v___y_42_ = v___x_54_;
goto v___jp_40_;
}
else
{
lean_object* v___x_55_; 
v___x_55_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_41_ = v___x_53_;
v___y_42_ = v___x_55_;
goto v___jp_40_;
}
}
}
else
{
lean_object* v___x_59_; 
v___x_59_ = lean_apply_1(v_x_29_, lean_box(0));
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___boxed(lean_object* v_inst_60_, lean_object* v_pp_61_, lean_object* v_ip_62_, lean_object* v_x_63_){
_start:
{
uint8_t v_pp_boxed_64_; uint8_t v_ip_boxed_65_; lean_object* v_res_66_; 
v_pp_boxed_64_ = lean_unbox(v_pp_61_);
v_ip_boxed_65_ = lean_unbox(v_ip_62_);
v_res_66_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v_inst_60_, v_pp_boxed_64_, v_ip_boxed_65_, v_x_63_);
lean_dec(v_inst_60_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck(lean_object* v_00_u03b1_67_, lean_object* v_inst_68_, uint8_t v_pp_69_, uint8_t v_ip_70_, lean_object* v_x_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v_inst_68_, v_pp_69_, v_ip_70_, v_x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___boxed(lean_object* v_00_u03b1_73_, lean_object* v_inst_74_, lean_object* v_pp_75_, lean_object* v_ip_76_, lean_object* v_x_77_){
_start:
{
uint8_t v_pp_boxed_78_; uint8_t v_ip_boxed_79_; lean_object* v_res_80_; 
v_pp_boxed_78_ = lean_unbox(v_pp_75_);
v_ip_boxed_79_ = lean_unbox(v_ip_76_);
v_res_80_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck(v_00_u03b1_73_, v_inst_74_, v_pp_boxed_78_, v_ip_boxed_79_, v_x_77_);
lean_dec(v_inst_74_);
return v_res_80_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instLTPhase(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(0);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instLEPhase(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(0);
return v___x_82_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableLtPhase(uint8_t v_p1_83_, uint8_t v_p2_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_85_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p1_83_);
v___x_86_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p2_84_);
v___x_87_ = lean_nat_dec_lt(v___x_85_, v___x_86_);
lean_dec(v___x_86_);
lean_dec(v___x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableLtPhase___boxed(lean_object* v_p1_88_, lean_object* v_p2_89_){
_start:
{
uint8_t v_p1_boxed_90_; uint8_t v_p2_boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_p1_boxed_90_ = lean_unbox(v_p1_88_);
v_p2_boxed_91_ = lean_unbox(v_p2_89_);
v_res_92_ = l_Lean_Compiler_LCNF_instDecidableLtPhase(v_p1_boxed_90_, v_p2_boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_instDecidableLePhase(uint8_t v_p1_94_, uint8_t v_p2_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_96_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p1_94_);
v___x_97_ = l_Lean_Compiler_LCNF_Phase_toNat(v_p2_95_);
v___x_98_ = lean_nat_dec_le(v___x_96_, v___x_97_);
lean_dec(v___x_97_);
lean_dec(v___x_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instDecidableLePhase___boxed(lean_object* v_p1_99_, lean_object* v_p2_100_){
_start:
{
uint8_t v_p1_boxed_101_; uint8_t v_p2_boxed_102_; uint8_t v_res_103_; lean_object* v_r_104_; 
v_p1_boxed_101_ = lean_unbox(v_p1_99_);
v_p2_boxed_102_ = lean_unbox(v_p2_100_);
v_res_103_ = l_Lean_Compiler_LCNF_instDecidableLePhase(v_p1_boxed_101_, v_p2_boxed_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__10));
v___x_132_ = l_Lean_mkAtom(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__12);
v___x_134_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_135_ = lean_array_push(v___x_134_, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__20));
v___x_156_ = l_Lean_mkAtom(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__21);
v___x_158_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_159_ = lean_array_push(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__26));
v___x_173_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22);
v___x_174_ = lean_array_push(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__27);
v___x_176_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19));
v___x_177_ = lean_box(2);
v___x_178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__28);
v___x_180_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_181_ = lean_array_push(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__29);
v___x_183_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17));
v___x_184_ = lean_box(2);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__30);
v___x_187_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_188_ = lean_array_push(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__35));
v___x_202_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__22);
v___x_203_ = lean_array_push(v___x_202_, v___x_201_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_204_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__36);
v___x_205_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__19));
v___x_206_ = lean_box(2);
v___x_207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_205_);
lean_ctor_set(v___x_207_, 2, v___x_204_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__37);
v___x_209_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_210_ = lean_array_push(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_211_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__38);
v___x_212_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__17));
v___x_213_ = lean_box(2);
v___x_214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
lean_ctor_set(v___x_214_, 2, v___x_211_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__39);
v___x_216_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__31);
v___x_217_ = lean_array_push(v___x_216_, v___x_215_);
return v___x_217_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_218_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__40);
v___x_219_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9));
v___x_220_ = lean_box(2);
v___x_221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_219_);
lean_ctor_set(v___x_221_, 2, v___x_218_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__41);
v___x_223_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_224_ = lean_array_push(v___x_223_, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_225_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__42);
v___x_226_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__15));
v___x_227_ = lean_box(2);
v___x_228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v___x_226_);
lean_ctor_set(v___x_228_, 2, v___x_225_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__43);
v___x_230_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__13);
v___x_231_ = lean_array_push(v___x_230_, v___x_229_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_237_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__44);
v___x_238_ = lean_array_push(v___x_237_, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_240_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__46);
v___x_241_ = lean_array_push(v___x_240_, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_243_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__47);
v___x_244_ = lean_array_push(v___x_243_, v___x_242_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__45));
v___x_246_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__48);
v___x_247_ = lean_array_push(v___x_246_, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_248_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__49);
v___x_249_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__11));
v___x_250_ = lean_box(2);
v___x_251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
lean_ctor_set(v___x_251_, 2, v___x_248_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__50);
v___x_253_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_254_ = lean_array_push(v___x_253_, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_255_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__51);
v___x_256_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__9));
v___x_257_ = lean_box(2);
v___x_258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
lean_ctor_set(v___x_258_, 2, v___x_255_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__52);
v___x_260_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_261_ = lean_array_push(v___x_260_, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_262_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__53);
v___x_263_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__7));
v___x_264_ = lean_box(2);
v___x_265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
lean_ctor_set(v___x_265_, 2, v___x_262_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__54);
v___x_267_ = ((lean_object*)(l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__5));
v___x_268_ = lean_array_push(v___x_267_, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_269_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__55);
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
v___x_273_ = lean_obj_once(&l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56, &l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56_once, _init_l_Lean_Compiler_LCNF_Pass_phaseInv___autoParam___closed__56);
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
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = l_Lean_instInhabitedMessageData_default;
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(lean_object* v_x_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___closed__0, &l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___closed__0);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0___boxed(lean_object* v_x_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Compiler_LCNF_instInhabitedPassInstaller_default___lam__0(v_x_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec_ref(v_x_305_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(lean_object* v_run_323_, size_t v_sz_324_, size_t v_i_325_, lean_object* v_bs_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
uint8_t v___x_332_; 
v___x_332_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v_run_323_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v_bs_326_);
return v___x_333_;
}
else
{
lean_object* v_v_334_; lean_object* v___x_335_; lean_object* v_bs_x27_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_v_334_ = lean_array_uget(v_bs_326_, v_i_325_);
v___x_335_ = lean_unsigned_to_nat(0u);
v_bs_x27_336_ = lean_array_uset(v_bs_326_, v_i_325_, v___x_335_);
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___closed__0));
v___x_338_ = l_Lean_Core_checkSystem(v___x_337_, v___y_329_, v___y_330_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_339_; 
lean_dec_ref_known(v___x_338_, 1);
lean_inc_ref(v_run_323_);
lean_inc(v___y_330_);
lean_inc_ref(v___y_329_);
lean_inc(v___y_328_);
lean_inc_ref(v___y_327_);
v___x_339_ = lean_apply_6(v_run_323_, v_v_334_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, lean_box(0));
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v___x_343_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_add(v_i_325_, v___x_341_);
v___x_343_ = lean_array_uset(v_bs_x27_336_, v_i_325_, v_a_340_);
v_i_325_ = v___x_342_;
v_bs_326_ = v___x_343_;
goto _start;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec_ref(v_bs_x27_336_);
lean_dec_ref(v_run_323_);
v_a_345_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_339_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_339_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref(v_bs_x27_336_);
lean_dec(v_v_334_);
lean_dec_ref(v_run_323_);
v_a_353_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_338_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_338_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0___boxed(lean_object* v_run_361_, lean_object* v_sz_362_, lean_object* v_i_363_, lean_object* v_bs_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
size_t v_sz_boxed_370_; size_t v_i_boxed_371_; lean_object* v_res_372_; 
v_sz_boxed_370_ = lean_unbox_usize(v_sz_362_);
lean_dec(v_sz_362_);
v_i_boxed_371_ = lean_unbox_usize(v_i_363_);
lean_dec(v_i_363_);
v_res_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_361_, v_sz_boxed_370_, v_i_boxed_371_, v_bs_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(lean_object* v_run_373_, lean_object* v_xs_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
size_t v_sz_380_; size_t v___x_381_; lean_object* v___x_382_; 
v_sz_380_ = lean_array_size(v_xs_374_);
v___x_381_ = ((size_t)0ULL);
v___x_382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_mkPerDeclaration_spec__0(v_run_373_, v_sz_380_, v___x_381_, v_xs_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed(lean_object* v_run_383_, lean_object* v_xs_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0(v_run_383_, v_xs_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object* v_name_391_, uint8_t v_phase_392_, lean_object* v_run_393_, lean_object* v_occurrence_394_){
_start:
{
lean_object* v___f_395_; uint8_t v___x_396_; lean_object* v___x_397_; 
v___f_395_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___lam__0___boxed), 7, 1);
lean_closure_set(v___f_395_, 0, v_run_393_);
v___x_396_ = 0;
v___x_397_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_397_, 0, v_occurrence_394_);
lean_ctor_set(v___x_397_, 1, v_name_391_);
lean_ctor_set(v___x_397_, 2, v___f_395_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*3, v_phase_392_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*3 + 1, v_phase_392_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*3 + 2, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration___boxed(lean_object* v_name_398_, lean_object* v_phase_399_, lean_object* v_run_400_, lean_object* v_occurrence_401_){
_start:
{
uint8_t v_phase_boxed_402_; lean_object* v_res_403_; 
v_phase_boxed_402_ = lean_unbox(v_phase_399_);
v_res_403_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(v_name_398_, v_phase_boxed_402_, v_run_400_, v_occurrence_401_);
return v_res_403_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_404_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__0);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
lean_ctor_set(v___x_409_, 2, v___x_408_);
lean_ctor_set(v___x_409_, 3, v___x_408_);
lean_ctor_set(v___x_409_, 4, v___x_407_);
lean_ctor_set(v___x_409_, 5, v___x_407_);
lean_ctor_set(v___x_409_, 6, v___x_407_);
lean_ctor_set(v___x_409_, 7, v___x_407_);
lean_ctor_set(v___x_409_, 8, v___x_407_);
lean_ctor_set(v___x_409_, 9, v___x_407_);
lean_ctor_set(v___x_409_, 10, v___x_407_);
return v___x_409_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_unsigned_to_nat(32u);
v___x_411_ = lean_mk_empty_array_with_capacity(v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_413_ = ((size_t)5ULL);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_unsigned_to_nat(32u);
v___x_416_ = lean_mk_empty_array_with_capacity(v___x_415_);
v___x_417_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__3);
v___x_418_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v___x_416_);
lean_ctor_set(v___x_418_, 2, v___x_414_);
lean_ctor_set(v___x_418_, 3, v___x_414_);
lean_ctor_set_usize(v___x_418_, 4, v___x_413_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_box(1);
v___x_420_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__4);
v___x_421_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__1);
v___x_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_419_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(lean_object* v_msgData_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; lean_object* v_toCold_428_; lean_object* v_env_429_; lean_object* v_options_430_; uint8_t v___x_431_; lean_object* v_env_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_427_ = lean_st_ref_get(v___y_425_);
v_toCold_428_ = lean_ctor_get(v___y_424_, 0);
v_env_429_ = lean_ctor_get(v___x_427_, 0);
lean_inc_ref(v_env_429_);
lean_dec(v___x_427_);
v_options_430_ = lean_ctor_get(v_toCold_428_, 2);
v___x_431_ = 0;
v_env_432_ = l_Lean_Environment_setRecordingDeps(v_env_429_, v___x_431_);
v___x_433_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__2);
v___x_434_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_430_);
v___x_435_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_435_, 0, v_env_432_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
lean_ctor_set(v___x_435_, 2, v___x_434_);
lean_ctor_set(v___x_435_, 3, v_options_430_);
v___x_436_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v_msgData_423_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0___boxed(lean_object* v_msgData_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msgData_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(lean_object* v_msg_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_ref_447_; lean_object* v___x_448_; lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v_ref_447_ = lean_ctor_get(v___y_444_, 2);
v___x_448_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0_spec__0(v_msg_443_, v___y_444_, v___y_445_);
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_457_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
lean_inc(v_ref_447_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_ref_447_);
lean_ctor_set(v___x_453_, 1, v_a_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set_tag(v___x_451_, 1);
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg___boxed(lean_object* v_msg_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(uint8_t v_phase_465_, lean_object* v_as_466_, size_t v_sz_467_, size_t v_i_468_, lean_object* v_b_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_a_474_; uint8_t v___x_478_; 
v___x_478_ = lean_usize_dec_lt(v_i_468_, v_sz_467_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_b_469_);
return v___x_479_;
}
else
{
lean_object* v_a_480_; uint8_t v_phase_481_; lean_object* v_name_482_; lean_object* v___x_483_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_a_480_ = lean_array_uget_borrowed(v_as_466_, v_i_468_);
v_phase_481_ = lean_ctor_get_uint8(v_a_480_, sizeof(void*)*3);
v_name_482_ = lean_ctor_get(v_a_480_, 1);
v___x_483_ = lean_box(0);
v___x_491_ = lean_box(v_phase_481_);
v___x_492_ = lean_obj_tag_nat(v___x_491_);
lean_dec(v___x_491_);
v___x_493_ = lean_box(v_phase_465_);
v___x_494_ = lean_obj_tag_nat(v___x_493_);
lean_dec(v___x_493_);
v___x_495_ = lean_nat_dec_eq(v___x_492_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___y_500_; 
lean_inc(v_name_482_);
v___x_496_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_482_, v___x_478_);
v___x_497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__0));
v___x_498_ = lean_string_append(v___x_496_, v___x_497_);
switch(v_phase_481_)
{
case 0:
{
lean_object* v___x_507_; 
v___x_507_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_500_ = v___x_507_;
goto v___jp_499_;
}
case 1:
{
lean_object* v___x_508_; 
v___x_508_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_500_ = v___x_508_;
goto v___jp_499_;
}
default: 
{
lean_object* v___x_509_; 
v___x_509_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_500_ = v___x_509_;
goto v___jp_499_;
}
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_string_append(v___x_498_, v___y_500_);
v___x_502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___closed__1));
v___x_503_ = lean_string_append(v___x_501_, v___x_502_);
switch(v_phase_465_)
{
case 0:
{
lean_object* v___x_504_; 
v___x_504_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__0));
v___y_485_ = v___x_503_;
v___y_486_ = v___x_504_;
goto v___jp_484_;
}
case 1:
{
lean_object* v___x_505_; 
v___x_505_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__1));
v___y_485_ = v___x_503_;
v___y_486_ = v___x_505_;
goto v___jp_484_;
}
default: 
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l_Lean_Compiler_LCNF_instToStringPhase___lam__0___closed__2));
v___y_485_ = v___x_503_;
v___y_486_ = v___x_506_;
goto v___jp_484_;
}
}
}
}
else
{
v_a_474_ = v___x_483_;
goto v___jp_473_;
}
v___jp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = lean_string_append(v___y_485_, v___y_486_);
v___x_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = l_Lean_MessageData_ofFormat(v___x_488_);
v___x_490_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_489_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_dec_ref_known(v___x_490_, 1);
v_a_474_ = v___x_483_;
goto v___jp_473_;
}
else
{
return v___x_490_;
}
}
}
v___jp_473_:
{
size_t v___x_475_; size_t v___x_476_; 
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_add(v_i_468_, v___x_475_);
v_i_468_ = v___x_476_;
v_b_469_ = v_a_474_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1___boxed(lean_object* v_phase_510_, lean_object* v_as_511_, lean_object* v_sz_512_, lean_object* v_i_513_, lean_object* v_b_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v_phase_boxed_518_; size_t v_sz_boxed_519_; size_t v_i_boxed_520_; lean_object* v_res_521_; 
v_phase_boxed_518_ = lean_unbox(v_phase_510_);
v_sz_boxed_519_ = lean_unbox_usize(v_sz_512_);
lean_dec(v_sz_512_);
v_i_boxed_520_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_boxed_518_, v_as_511_, v_sz_boxed_519_, v_i_boxed_520_, v_b_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v_as_511_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(uint8_t v_phase_522_, lean_object* v_passes_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_527_; size_t v_sz_528_; size_t v___x_529_; lean_object* v___x_530_; 
v___x_527_ = lean_box(0);
v_sz_528_ = lean_array_size(v_passes_523_);
v___x_529_ = ((size_t)0ULL);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__1(v_phase_522_, v_passes_523_, v_sz_528_, v___x_529_, v___x_527_, v_a_524_, v_a_525_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v___x_530_, 0);
lean_dec(v_unused_538_);
v___x_532_ = v___x_530_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_dec(v___x_530_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_527_);
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_527_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses___boxed(lean_object* v_phase_539_, lean_object* v_passes_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
uint8_t v_phase_boxed_544_; lean_object* v_res_545_; 
v_phase_boxed_544_ = lean_unbox(v_phase_539_);
v_res_545_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v_phase_boxed_544_, v_passes_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec_ref(v_passes_540_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(lean_object* v_00_u03b1_546_, lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v_msg_547_, v___y_548_, v___y_549_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___boxed(lean_object* v_00_u03b1_552_, lean_object* v_msg_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0(v_00_u03b1_552_, v_msg_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_validate(lean_object* v_manager_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_basePasses_562_; lean_object* v_monoPasses_563_; lean_object* v_monoPassesNoLambda_564_; uint8_t v___x_565_; lean_object* v___x_566_; 
v_basePasses_562_ = lean_ctor_get(v_manager_558_, 0);
v_monoPasses_563_ = lean_ctor_get(v_manager_558_, 1);
v_monoPassesNoLambda_564_ = lean_ctor_get(v_manager_558_, 2);
v___x_565_ = 0;
v___x_566_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_565_, v_basePasses_562_, v_a_559_, v_a_560_);
if (lean_obj_tag(v___x_566_) == 0)
{
uint8_t v___x_567_; lean_object* v___x_568_; 
lean_dec_ref_known(v___x_566_, 1);
v___x_567_ = 1;
v___x_568_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_567_, v_monoPasses_563_, v_a_559_, v_a_560_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_569_; 
lean_dec_ref_known(v___x_568_, 1);
v___x_569_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses(v___x_567_, v_monoPassesNoLambda_564_, v_a_559_, v_a_560_);
return v___x_569_;
}
else
{
return v___x_568_;
}
}
else
{
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_validate___boxed(lean_object* v_manager_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_Compiler_LCNF_PassManager_validate(v_manager_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec_ref(v_manager_570_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(lean_object* v_targetName_575_, lean_object* v_as_576_, size_t v_sz_577_, size_t v_i_578_, lean_object* v_b_579_){
_start:
{
lean_object* v_a_582_; uint8_t v___x_586_; 
v___x_586_ = lean_usize_dec_lt(v_i_578_, v_sz_577_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_b_579_);
return v___x_587_;
}
else
{
lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_605_; 
v_fst_588_ = lean_ctor_get(v_b_579_, 0);
v_snd_589_ = lean_ctor_get(v_b_579_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_b_579_);
if (v_isSharedCheck_605_ == 0)
{
v___x_591_ = v_b_579_;
v_isShared_592_ = v_isSharedCheck_605_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_snd_589_);
lean_inc(v_fst_588_);
lean_dec(v_b_579_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_605_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_a_593_; lean_object* v_occurrence_594_; lean_object* v_name_595_; lean_object* v___y_597_; uint8_t v___x_602_; 
v_a_593_ = lean_array_uget_borrowed(v_as_576_, v_i_578_);
v_occurrence_594_ = lean_ctor_get(v_a_593_, 0);
v_name_595_ = lean_ctor_get(v_a_593_, 1);
v___x_602_ = lean_name_eq(v_name_595_, v_targetName_575_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
lean_del_object(v___x_591_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v_fst_588_);
lean_ctor_set(v___x_603_, 1, v_snd_589_);
v_a_582_ = v___x_603_;
goto v___jp_581_;
}
else
{
lean_dec(v_snd_589_);
if (lean_obj_tag(v_fst_588_) == 0)
{
lean_object* v___x_604_; 
lean_inc(v_occurrence_594_);
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v_occurrence_594_);
v___y_597_ = v___x_604_;
goto v___jp_596_;
}
else
{
v___y_597_ = v_fst_588_;
goto v___jp_596_;
}
}
v___jp_596_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
lean_inc(v_occurrence_594_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_occurrence_594_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_598_);
lean_ctor_set(v___x_591_, 0, v___y_597_);
v___x_600_ = v___x_591_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___y_597_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
v_a_582_ = v___x_600_;
goto v___jp_581_;
}
}
}
}
v___jp_581_:
{
size_t v___x_583_; size_t v___x_584_; 
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_578_, v___x_583_);
v_i_578_ = v___x_584_;
v_b_579_ = v_a_582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg___boxed(lean_object* v_targetName_606_, lean_object* v_as_607_, lean_object* v_sz_608_, lean_object* v_i_609_, lean_object* v_b_610_, lean_object* v___y_611_){
_start:
{
size_t v_sz_boxed_612_; size_t v_i_boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_608_);
lean_dec(v_sz_608_);
v_i_boxed_613_ = lean_unbox_usize(v_i_609_);
lean_dec(v_i_609_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_606_, v_as_607_, v_sz_boxed_612_, v_i_boxed_613_, v_b_610_);
lean_dec_ref(v_as_607_);
lean_dec(v_targetName_606_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(lean_object* v_targetName_618_, lean_object* v_passes_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___x_633_; size_t v_sz_634_; size_t v___x_635_; lean_object* v___x_636_; 
v___x_633_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__1));
v_sz_634_ = lean_array_size(v_passes_619_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_618_, v_passes_619_, v_sz_634_, v___x_635_, v___x_633_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_656_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_656_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_656_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_656_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_fst_641_; 
v_fst_641_ = lean_ctor_get(v_a_637_, 0);
lean_inc(v_fst_641_);
if (lean_obj_tag(v_fst_641_) == 1)
{
lean_object* v_snd_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_654_; 
v_snd_642_ = lean_ctor_get(v_a_637_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_637_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_a_637_, 0);
lean_dec(v_unused_655_);
v___x_644_ = v_a_637_;
v_isShared_645_ = v_isSharedCheck_654_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_snd_642_);
lean_dec(v_a_637_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_654_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
if (lean_obj_tag(v_snd_642_) == 1)
{
lean_object* v_val_646_; lean_object* v_val_647_; lean_object* v___x_649_; 
lean_dec(v_targetName_618_);
v_val_646_ = lean_ctor_get(v_fst_641_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v_fst_641_, 1);
v_val_647_ = lean_ctor_get(v_snd_642_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v_snd_642_, 1);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v_val_647_);
lean_ctor_set(v___x_644_, 0, v_val_646_);
v___x_649_ = v___x_644_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_val_646_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_val_647_);
v___x_649_ = v_reuseFailAlloc_653_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_651_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_649_);
v___x_651_ = v___x_639_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
lean_del_object(v___x_644_);
lean_dec(v_snd_642_);
lean_dec_ref_known(v_fst_641_, 1);
lean_del_object(v___x_639_);
v___y_624_ = v_a_620_;
v___y_625_ = v_a_621_;
goto v___jp_623_;
}
}
}
else
{
lean_dec(v_fst_641_);
lean_del_object(v___x_639_);
lean_dec(v_a_637_);
v___y_624_ = v_a_620_;
v___y_625_ = v_a_621_;
goto v___jp_623_;
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_targetName_618_);
v_a_657_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_636_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_636_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
v___jp_623_:
{
lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_626_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___closed__0));
v___x_627_ = 1;
v___x_628_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_618_, v___x_627_);
v___x_629_ = lean_string_append(v___x_626_, v___x_628_);
lean_dec_ref(v___x_628_);
v___x_630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
v___x_631_ = l_Lean_MessageData_ofFormat(v___x_630_);
v___x_632_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_631_, v___y_624_, v___y_625_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds___boxed(lean_object* v_targetName_665_, lean_object* v_passes_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(v_targetName_665_, v_passes_666_, v_a_667_, v_a_668_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
lean_dec_ref(v_passes_666_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(lean_object* v_targetName_671_, lean_object* v_as_672_, size_t v_sz_673_, size_t v_i_674_, lean_object* v_b_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___redArg(v_targetName_671_, v_as_672_, v_sz_673_, v_i_674_, v_b_675_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0___boxed(lean_object* v_targetName_680_, lean_object* v_as_681_, lean_object* v_sz_682_, lean_object* v_i_683_, lean_object* v_b_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
size_t v_sz_boxed_688_; size_t v_i_boxed_689_; lean_object* v_res_690_; 
v_sz_boxed_688_ = lean_unbox_usize(v_sz_682_);
lean_dec(v_sz_682_);
v_i_boxed_689_ = lean_unbox_usize(v_i_683_);
lean_dec(v_i_683_);
v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_PassManager_findOccurrenceBounds_spec__0(v_targetName_680_, v_as_681_, v_sz_boxed_688_, v_i_boxed_689_, v_b_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v_as_681_);
lean_dec(v_targetName_680_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(lean_object* v_p_691_, lean_object* v_passes_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_array_push(v_passes_692_, v_p_691_);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed(lean_object* v_p_698_, lean_object* v_passes_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0(v_p_698_, v_passes_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(uint8_t v_phase_704_, lean_object* v_p_705_){
_start:
{
lean_object* v___f_706_; lean_object* v___x_707_; 
v___f_706_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_706_, 0, v_p_705_);
v___x_707_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_707_, 0, v___f_706_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*1, v_phase_704_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAtEnd___boxed(lean_object* v_phase_708_, lean_object* v_p_709_){
_start:
{
uint8_t v_phase_boxed_710_; lean_object* v_res_711_; 
v_phase_boxed_710_ = lean_unbox(v_phase_708_);
v_res_711_ = l_Lean_Compiler_LCNF_PassInstaller_installAtEnd(v_phase_boxed_710_, v_p_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(lean_object* v_passesNew_712_, lean_object* v_passes_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = l_Array_append___redArg(v_passes_713_, v_passesNew_712_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed(lean_object* v_passesNew_719_, lean_object* v_passes_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Compiler_LCNF_PassInstaller_append___lam__0(v_passesNew_719_, v_passes_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_passesNew_719_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append(uint8_t v_phase_725_, lean_object* v_passesNew_726_){
_start:
{
lean_object* v___f_727_; lean_object* v___x_728_; 
v___f_727_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_append___lam__0___boxed), 5, 1);
lean_closure_set(v___f_727_, 0, v_passesNew_726_);
v___x_728_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_728_, 0, v___f_727_);
lean_ctor_set_uint8(v___x_728_, sizeof(void*)*1, v_phase_725_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___boxed(lean_object* v_phase_729_, lean_object* v_passesNew_730_){
_start:
{
uint8_t v_phase_boxed_731_; lean_object* v_res_732_; 
v_phase_boxed_731_ = lean_unbox(v_phase_729_);
v_res_732_ = l_Lean_Compiler_LCNF_PassInstaller_append(v_phase_boxed_731_, v_passesNew_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___f_738_; lean_object* v___x_1599__overap_739_; lean_object* v___x_740_; 
v___f_738_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___closed__0));
v___x_1599__overap_739_ = lean_panic_fn_borrowed(v___f_738_, v_msg_734_);
lean_inc(v___y_736_);
lean_inc_ref(v___y_735_);
v___x_740_ = lean_apply_3(v___x_1599__overap_739_, v___y_735_, v___y_736_, lean_box(0));
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0___boxed(lean_object* v_msg_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v_msg_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(lean_object* v_install_746_, lean_object* v_b_747_, lean_object* v_____r_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; 
lean_inc(v___y_750_);
lean_inc_ref(v___y_749_);
v___x_752_ = lean_apply_4(v_install_746_, v_b_747_, v___y_749_, v___y_750_, lean_box(0));
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_761_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_761_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_761_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v_a_753_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_a_762_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_752_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_752_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0___boxed(lean_object* v_install_770_, lean_object* v_b_771_, lean_object* v_____r_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_770_, v_b_771_, v_____r_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_776_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_779_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__1));
v___x_780_ = lean_unsigned_to_nat(8u);
v___x_781_ = lean_unsigned_to_nat(170u);
v___x_782_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__0));
v___x_783_ = ((lean_object*)(l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg___closed__0));
v___x_784_ = l_mkPanicMessageWithDecl(v___x_783_, v___x_782_, v___x_781_, v___x_780_, v___x_779_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(lean_object* v_upperBound_785_, lean_object* v_f_786_, uint8_t v_phase_787_, lean_object* v_a_788_, lean_object* v_b_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___y_794_; uint8_t v___x_816_; 
v___x_816_ = lean_nat_dec_le(v_a_788_, v_upperBound_785_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_dec(v_a_788_);
lean_dec_ref(v_f_786_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v_b_789_);
return v___x_817_;
}
else
{
lean_object* v___x_818_; uint8_t v_phase_819_; lean_object* v_install_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
lean_inc_ref(v_f_786_);
lean_inc(v_a_788_);
v___x_818_ = lean_apply_1(v_f_786_, v_a_788_);
v_phase_819_ = lean_ctor_get_uint8(v___x_818_, sizeof(void*)*1);
v_install_820_ = lean_ctor_get(v___x_818_, 0);
lean_inc_ref(v_install_820_);
lean_dec_ref(v___x_818_);
v___x_821_ = lean_box(v_phase_819_);
v___x_822_ = lean_obj_tag_nat(v___x_821_);
lean_dec(v___x_821_);
v___x_823_ = lean_box(v_phase_787_);
v___x_824_ = lean_obj_tag_nat(v___x_823_);
lean_dec(v___x_823_);
v___x_825_ = lean_nat_dec_eq(v___x_822_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___closed__2);
v___x_827_ = l_panic___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__0(v___x_826_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
v___x_829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_820_, v_b_789_, v_a_828_, v___y_790_, v___y_791_);
v___y_794_ = v___x_829_;
goto v___jp_793_;
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_install_820_);
lean_dec_ref(v_b_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_f_786_);
v_a_830_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_827_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_827_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_box(0);
v___x_839_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___lam__0(v_install_820_, v_b_789_, v___x_838_, v___y_790_, v___y_791_);
v___y_794_ = v___x_839_;
goto v___jp_793_;
}
}
v___jp_793_:
{
if (lean_obj_tag(v___y_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_807_; 
v_a_795_ = lean_ctor_get(v___y_794_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___y_794_);
if (v_isSharedCheck_807_ == 0)
{
v___x_797_ = v___y_794_;
v_isShared_798_ = v_isSharedCheck_807_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___y_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_807_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
if (lean_obj_tag(v_a_795_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_801_; 
lean_dec(v_a_788_);
lean_dec_ref(v_f_786_);
v_a_799_ = lean_ctor_get(v_a_795_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v_a_795_, 1);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v_a_799_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_del_object(v___x_797_);
v_a_803_ = lean_ctor_get(v_a_795_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v_a_795_, 1);
v___x_804_ = lean_unsigned_to_nat(1u);
v___x_805_ = lean_nat_add(v_a_788_, v___x_804_);
lean_dec(v_a_788_);
v_a_788_ = v___x_805_;
v_b_789_ = v_a_803_;
goto _start;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_a_788_);
lean_dec_ref(v_f_786_);
v_a_808_ = lean_ctor_get(v___y_794_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___y_794_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___y_794_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___y_794_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg___boxed(lean_object* v_upperBound_840_, lean_object* v_f_841_, lean_object* v_phase_842_, lean_object* v_a_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
uint8_t v_phase_boxed_848_; lean_object* v_res_849_; 
v_phase_boxed_848_ = lean_unbox(v_phase_842_);
v_res_849_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_840_, v_f_841_, v_phase_boxed_848_, v_a_843_, v_b_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v_upperBound_840_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(lean_object* v_targetName_850_, lean_object* v_f_851_, uint8_t v_phase_852_, lean_object* v_passes_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Compiler_LCNF_PassManager_findOccurrenceBounds(v_targetName_850_, v_passes_853_, v___y_854_, v___y_855_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_861_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v_fst_859_ = lean_ctor_get(v_a_858_, 0);
lean_inc(v_fst_859_);
v_snd_860_ = lean_ctor_get(v_a_858_, 1);
lean_inc(v_snd_860_);
lean_dec(v_a_858_);
v___x_861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_snd_860_, v_f_851_, v_phase_852_, v_fst_859_, v_passes_853_, v___y_854_, v___y_855_);
lean_dec(v_snd_860_);
return v___x_861_;
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec_ref(v_passes_853_);
lean_dec_ref(v_f_851_);
v_a_862_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_857_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_857_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed(lean_object* v_targetName_870_, lean_object* v_f_871_, lean_object* v_phase_872_, lean_object* v_passes_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
uint8_t v_phase_boxed_877_; lean_object* v_res_878_; 
v_phase_boxed_877_ = lean_unbox(v_phase_872_);
v_res_878_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0(v_targetName_870_, v_f_871_, v_phase_boxed_877_, v_passes_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(uint8_t v_phase_879_, lean_object* v_targetName_880_, lean_object* v_f_881_){
_start:
{
lean_object* v___x_882_; lean_object* v___f_883_; lean_object* v___x_884_; 
v___x_882_ = lean_box(v_phase_879_);
v___f_883_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___lam__0___boxed), 7, 3);
lean_closure_set(v___f_883_, 0, v_targetName_880_);
lean_closure_set(v___f_883_, 1, v_f_881_);
lean_closure_set(v___f_883_, 2, v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_884_, 0, v___f_883_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*1, v_phase_879_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence___boxed(lean_object* v_phase_885_, lean_object* v_targetName_886_, lean_object* v_f_887_){
_start:
{
uint8_t v_phase_boxed_888_; lean_object* v_res_889_; 
v_phase_boxed_888_ = lean_unbox(v_phase_885_);
v_res_889_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_boxed_888_, v_targetName_886_, v_f_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(lean_object* v_upperBound_890_, lean_object* v_f_891_, uint8_t v_phase_892_, lean_object* v_inst_893_, lean_object* v_R_894_, lean_object* v_a_895_, lean_object* v_b_896_, lean_object* v_c_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___redArg(v_upperBound_890_, v_f_891_, v_phase_892_, v_a_895_, v_b_896_, v___y_898_, v___y_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1___boxed(lean_object* v_upperBound_902_, lean_object* v_f_903_, lean_object* v_phase_904_, lean_object* v_inst_905_, lean_object* v_R_906_, lean_object* v_a_907_, lean_object* v_b_908_, lean_object* v_c_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
uint8_t v_phase_boxed_913_; lean_object* v_res_914_; 
v_phase_boxed_913_ = lean_unbox(v_phase_904_);
v_res_914_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_PassInstaller_withEachOccurrence_spec__1(v_upperBound_902_, v_f_903_, v_phase_boxed_913_, v_inst_905_, v_R_906_, v_a_907_, v_b_908_, v_c_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v_upperBound_902_);
return v_res_914_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(lean_object* v_targetName_915_, lean_object* v_occurrence_916_, lean_object* v_p_917_){
_start:
{
lean_object* v_occurrence_918_; lean_object* v_name_919_; uint8_t v___x_920_; 
v_occurrence_918_ = lean_ctor_get(v_p_917_, 0);
v_name_919_ = lean_ctor_get(v_p_917_, 1);
v___x_920_ = lean_name_eq(v_name_919_, v_targetName_915_);
if (v___x_920_ == 0)
{
return v___x_920_;
}
else
{
uint8_t v___x_921_; 
v___x_921_ = lean_nat_dec_eq(v_occurrence_918_, v_occurrence_916_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed(lean_object* v_targetName_922_, lean_object* v_occurrence_923_, lean_object* v_p_924_){
_start:
{
uint8_t v_res_925_; lean_object* v_r_926_; 
v_res_925_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0(v_targetName_922_, v_occurrence_923_, v_p_924_);
lean_dec_ref(v_p_924_);
lean_dec(v_occurrence_923_);
lean_dec(v_targetName_922_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(lean_object* v___f_931_, lean_object* v_p_932_, lean_object* v_targetName_933_, lean_object* v_occurrence_934_, lean_object* v_passes_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_931_, v_passes_935_, v___x_939_);
if (lean_obj_tag(v___x_940_) == 1)
{
lean_object* v_val_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_occurrence_934_);
lean_dec(v_targetName_933_);
v_val_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_955_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_955_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_val_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_955_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_passUnderTest_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v_j_949_; lean_object* v_as_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v_passUnderTest_945_ = lean_array_fget_borrowed(v_passes_935_, v_val_941_);
v___x_946_ = lean_unsigned_to_nat(1u);
v___x_947_ = lean_nat_add(v_val_941_, v___x_946_);
lean_dec(v_val_941_);
lean_inc(v_passUnderTest_945_);
v___x_948_ = lean_apply_1(v_p_932_, v_passUnderTest_945_);
v_j_949_ = lean_array_get_size(v_passes_935_);
v_as_950_ = lean_array_push(v_passes_935_, v___x_948_);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_947_, v_as_950_, v_j_949_);
lean_dec(v___x_947_);
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 0);
lean_ctor_set(v___x_943_, 0, v___x_951_);
v___x_953_ = v___x_943_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v___x_940_);
lean_dec_ref(v_passes_935_);
lean_dec_ref(v_p_932_);
v___x_956_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0));
v___x_957_ = 1;
v___x_958_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_933_, v___x_957_);
v___x_959_ = lean_string_append(v___x_956_, v___x_958_);
v___x_960_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_961_ = lean_string_append(v___x_959_, v___x_960_);
v___x_962_ = l_Nat_reprFast(v_occurrence_934_);
v___x_963_ = lean_string_append(v___x_961_, v___x_962_);
lean_dec_ref(v___x_962_);
v___x_964_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_965_ = lean_string_append(v___x_963_, v___x_964_);
v___x_966_ = lean_string_append(v___x_965_, v___x_958_);
lean_dec_ref(v___x_958_);
v___x_967_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_968_ = lean_string_append(v___x_966_, v___x_967_);
v___x_969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
v___x_970_ = l_Lean_MessageData_ofFormat(v___x_969_);
v___x_971_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_970_, v___y_936_, v___y_937_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed(lean_object* v___f_972_, lean_object* v_p_973_, lean_object* v_targetName_974_, lean_object* v_occurrence_975_, lean_object* v_passes_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1(v___f_972_, v_p_973_, v_targetName_974_, v_occurrence_975_, v_passes_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter(uint8_t v_phase_981_, lean_object* v_targetName_982_, lean_object* v_p_983_, lean_object* v_occurrence_984_){
_start:
{
lean_object* v___f_985_; lean_object* v___f_986_; lean_object* v___x_987_; 
lean_inc(v_occurrence_984_);
lean_inc(v_targetName_982_);
v___f_985_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed), 3, 2);
lean_closure_set(v___f_985_, 0, v_targetName_982_);
lean_closure_set(v___f_985_, 1, v_occurrence_984_);
v___f_986_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___boxed), 8, 4);
lean_closure_set(v___f_986_, 0, v___f_985_);
lean_closure_set(v___f_986_, 1, v_p_983_);
lean_closure_set(v___f_986_, 2, v_targetName_982_);
lean_closure_set(v___f_986_, 3, v_occurrence_984_);
v___x_987_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_987_, 0, v___f_986_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*1, v_phase_981_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___boxed(lean_object* v_phase_988_, lean_object* v_targetName_989_, lean_object* v_p_990_, lean_object* v_occurrence_991_){
_start:
{
uint8_t v_phase_boxed_992_; lean_object* v_res_993_; 
v_phase_boxed_992_ = lean_unbox(v_phase_988_);
v_res_993_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_boxed_992_, v_targetName_989_, v_p_990_, v_occurrence_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(uint8_t v_phase_994_, lean_object* v_targetName_995_, lean_object* v_p_996_, lean_object* v_x_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Compiler_LCNF_PassInstaller_installAfter(v_phase_994_, v_targetName_995_, v_p_996_, v_x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed(lean_object* v_phase_999_, lean_object* v_targetName_1000_, lean_object* v_p_1001_, lean_object* v_x_1002_){
_start:
{
uint8_t v_phase_boxed_1003_; lean_object* v_res_1004_; 
v_phase_boxed_1003_ = lean_unbox(v_phase_999_);
v_res_1004_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0(v_phase_boxed_1003_, v_targetName_1000_, v_p_1001_, v_x_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(uint8_t v_phase_1005_, lean_object* v_targetName_1006_, lean_object* v_p_1007_){
_start:
{
lean_object* v___x_1008_; lean_object* v___f_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(v_phase_1005_);
lean_inc(v_targetName_1006_);
v___f_1009_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1009_, 0, v___x_1008_);
lean_closure_set(v___f_1009_, 1, v_targetName_1006_);
lean_closure_set(v___f_1009_, 2, v_p_1007_);
v___x_1010_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1005_, v_targetName_1006_, v___f_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfterEach___boxed(lean_object* v_phase_1011_, lean_object* v_targetName_1012_, lean_object* v_p_1013_){
_start:
{
uint8_t v_phase_boxed_1014_; lean_object* v_res_1015_; 
v_phase_boxed_1014_ = lean_unbox(v_phase_1011_);
v_res_1015_ = l_Lean_Compiler_LCNF_PassInstaller_installAfterEach(v_phase_boxed_1014_, v_targetName_1012_, v_p_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(lean_object* v___f_1016_, lean_object* v_p_1017_, lean_object* v_targetName_1018_, lean_object* v_occurrence_1019_, lean_object* v_passes_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1016_, v_passes_1020_, v___x_1024_);
if (lean_obj_tag(v___x_1025_) == 1)
{
lean_object* v_val_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v_occurrence_1019_);
lean_dec(v_targetName_1018_);
v_val_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1038_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_val_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1038_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_passUnderTest_1030_; lean_object* v___x_1031_; lean_object* v_j_1032_; lean_object* v_as_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v_passUnderTest_1030_ = lean_array_fget_borrowed(v_passes_1020_, v_val_1026_);
lean_inc(v_passUnderTest_1030_);
v___x_1031_ = lean_apply_1(v_p_1017_, v_passUnderTest_1030_);
v_j_1032_ = lean_array_get_size(v_passes_1020_);
v_as_1033_ = lean_array_push(v_passes_1020_, v___x_1031_);
v___x_1034_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_val_1026_, v_as_1033_, v_j_1032_);
lean_dec(v_val_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1034_);
v___x_1036_ = v___x_1028_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
else
{
lean_object* v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v___x_1025_);
lean_dec_ref(v_passes_1020_);
lean_dec_ref(v_p_1017_);
v___x_1039_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__0));
v___x_1040_ = 1;
v___x_1041_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_1018_, v___x_1040_);
v___x_1042_ = lean_string_append(v___x_1039_, v___x_1041_);
v___x_1043_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_1044_ = lean_string_append(v___x_1042_, v___x_1043_);
v___x_1045_ = l_Nat_reprFast(v_occurrence_1019_);
v___x_1046_ = lean_string_append(v___x_1044_, v___x_1045_);
lean_dec_ref(v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_1048_ = lean_string_append(v___x_1046_, v___x_1047_);
v___x_1049_ = lean_string_append(v___x_1048_, v___x_1041_);
lean_dec_ref(v___x_1041_);
v___x_1050_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_1051_ = lean_string_append(v___x_1049_, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
v___x_1053_ = l_Lean_MessageData_ofFormat(v___x_1052_);
v___x_1054_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1053_, v___y_1021_, v___y_1022_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed(lean_object* v___f_1055_, lean_object* v_p_1056_, lean_object* v_targetName_1057_, lean_object* v_occurrence_1058_, lean_object* v_passes_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1(v___f_1055_, v_p_1056_, v_targetName_1057_, v_occurrence_1058_, v_passes_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore(uint8_t v_phase_1064_, lean_object* v_targetName_1065_, lean_object* v_p_1066_, lean_object* v_occurrence_1067_){
_start:
{
lean_object* v___f_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; 
lean_inc(v_occurrence_1067_);
lean_inc(v_targetName_1065_);
v___f_1068_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1068_, 0, v_targetName_1065_);
lean_closure_set(v___f_1068_, 1, v_occurrence_1067_);
v___f_1069_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installBefore___lam__1___boxed), 8, 4);
lean_closure_set(v___f_1069_, 0, v___f_1068_);
lean_closure_set(v___f_1069_, 1, v_p_1066_);
lean_closure_set(v___f_1069_, 2, v_targetName_1065_);
lean_closure_set(v___f_1069_, 3, v_occurrence_1067_);
v___x_1070_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1070_, 0, v___f_1069_);
lean_ctor_set_uint8(v___x_1070_, sizeof(void*)*1, v_phase_1064_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBefore___boxed(lean_object* v_phase_1071_, lean_object* v_targetName_1072_, lean_object* v_p_1073_, lean_object* v_occurrence_1074_){
_start:
{
uint8_t v_phase_boxed_1075_; lean_object* v_res_1076_; 
v_phase_boxed_1075_ = lean_unbox(v_phase_1071_);
v_res_1076_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_boxed_1075_, v_targetName_1072_, v_p_1073_, v_occurrence_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(uint8_t v_phase_1077_, lean_object* v_targetName_1078_, lean_object* v_p_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Compiler_LCNF_PassInstaller_installBefore(v_phase_1077_, v_targetName_1078_, v_p_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed(lean_object* v_phase_1082_, lean_object* v_targetName_1083_, lean_object* v_p_1084_, lean_object* v_x_1085_){
_start:
{
uint8_t v_phase_boxed_1086_; lean_object* v_res_1087_; 
v_phase_boxed_1086_ = lean_unbox(v_phase_1082_);
v_res_1087_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0(v_phase_boxed_1086_, v_targetName_1083_, v_p_1084_, v_x_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(uint8_t v_phase_1088_, lean_object* v_targetName_1089_, lean_object* v_p_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___f_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_box(v_phase_1088_);
lean_inc(v_targetName_1089_);
v___f_1092_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1092_, 0, v___x_1091_);
lean_closure_set(v___f_1092_, 1, v_targetName_1089_);
lean_closure_set(v___f_1092_, 2, v_p_1090_);
v___x_1093_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1088_, v_targetName_1089_, v___f_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence___boxed(lean_object* v_phase_1094_, lean_object* v_targetName_1095_, lean_object* v_p_1096_){
_start:
{
uint8_t v_phase_boxed_1097_; lean_object* v_res_1098_; 
v_phase_boxed_1097_ = lean_unbox(v_phase_1094_);
v_res_1098_ = l_Lean_Compiler_LCNF_PassInstaller_installBeforeEachOccurrence(v_phase_boxed_1097_, v_targetName_1095_, v_p_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(lean_object* v_targetName_1099_, lean_object* v_occurrence_1100_, lean_object* v_as_1101_, lean_object* v_j_1102_){
_start:
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = lean_array_get_size(v_as_1101_);
v___x_1108_ = lean_nat_dec_lt(v_j_1102_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; 
lean_dec(v_j_1102_);
v___x_1109_ = lean_box(0);
return v___x_1109_;
}
else
{
lean_object* v___x_1110_; lean_object* v_occurrence_1111_; lean_object* v_name_1112_; uint8_t v___x_1113_; 
v___x_1110_ = lean_array_fget_borrowed(v_as_1101_, v_j_1102_);
v_occurrence_1111_ = lean_ctor_get(v___x_1110_, 0);
v_name_1112_ = lean_ctor_get(v___x_1110_, 1);
v___x_1113_ = lean_name_eq(v_name_1112_, v_targetName_1099_);
if (v___x_1113_ == 0)
{
goto v___jp_1103_;
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_nat_dec_eq(v_occurrence_1111_, v_occurrence_1100_);
if (v___x_1114_ == 0)
{
goto v___jp_1103_;
}
else
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1115_, 0, v_j_1102_);
return v___x_1115_;
}
}
}
v___jp_1103_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_j_1102_, v___x_1104_);
lean_dec(v_j_1102_);
v_j_1102_ = v___x_1105_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0___boxed(lean_object* v_targetName_1116_, lean_object* v_occurrence_1117_, lean_object* v_as_1118_, lean_object* v_j_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_1116_, v_occurrence_1117_, v_as_1118_, v_j_1119_);
lean_dec_ref(v_as_1118_);
lean_dec(v_occurrence_1117_);
lean_dec(v_targetName_1116_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(lean_object* v_targetName_1122_, lean_object* v_occurrence_1123_, lean_object* v_p_1124_, lean_object* v_passes_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = l_Array_findIdx_x3f_loop___at___00Lean_Compiler_LCNF_PassInstaller_replacePass_spec__0(v_targetName_1122_, v_occurrence_1123_, v_passes_1125_, v___x_1129_);
if (lean_obj_tag(v___x_1130_) == 1)
{
lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_occurrence_1123_);
lean_dec(v_targetName_1122_);
v_val_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1148_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1148_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_array_get_size(v_passes_1125_);
v___x_1136_ = lean_nat_dec_lt(v_val_1131_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1138_; 
lean_dec(v_val_1131_);
lean_dec_ref(v_p_1124_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
lean_ctor_set(v___x_1133_, 0, v_passes_1125_);
v___x_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_passes_1125_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
else
{
lean_object* v_v_1140_; lean_object* v___x_1141_; lean_object* v_xs_x27_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v_v_1140_ = lean_array_fget(v_passes_1125_, v_val_1131_);
v___x_1141_ = lean_box(0);
v_xs_x27_1142_ = lean_array_fset(v_passes_1125_, v_val_1131_, v___x_1141_);
v___x_1143_ = lean_apply_1(v_p_1124_, v_v_1140_);
v___x_1144_ = lean_array_fset(v_xs_x27_1142_, v_val_1131_, v___x_1143_);
lean_dec(v_val_1131_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1144_);
v___x_1146_ = v___x_1133_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v___x_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec(v___x_1130_);
lean_dec_ref(v_passes_1125_);
lean_dec_ref(v_p_1124_);
v___x_1149_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___closed__0));
v___x_1150_ = 1;
v___x_1151_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_targetName_1122_, v___x_1150_);
v___x_1152_ = lean_string_append(v___x_1149_, v___x_1151_);
v___x_1153_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__1));
v___x_1154_ = lean_string_append(v___x_1152_, v___x_1153_);
v___x_1155_ = l_Nat_reprFast(v_occurrence_1123_);
v___x_1156_ = lean_string_append(v___x_1154_, v___x_1155_);
lean_dec_ref(v___x_1155_);
v___x_1157_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__2));
v___x_1158_ = lean_string_append(v___x_1156_, v___x_1157_);
v___x_1159_ = lean_string_append(v___x_1158_, v___x_1151_);
lean_dec_ref(v___x_1151_);
v___x_1160_ = ((lean_object*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___lam__1___closed__3));
v___x_1161_ = lean_string_append(v___x_1159_, v___x_1160_);
v___x_1162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
v___x_1163_ = l_Lean_MessageData_ofFormat(v___x_1162_);
v___x_1164_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1163_, v___y_1126_, v___y_1127_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed(lean_object* v_targetName_1165_, lean_object* v_occurrence_1166_, lean_object* v_p_1167_, lean_object* v_passes_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0(v_targetName_1165_, v_occurrence_1166_, v_p_1167_, v_passes_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass(uint8_t v_phase_1173_, lean_object* v_targetName_1174_, lean_object* v_p_1175_, lean_object* v_occurrence_1176_){
_start:
{
lean_object* v___f_1177_; lean_object* v___x_1178_; 
v___f_1177_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_replacePass___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1177_, 0, v_targetName_1174_);
lean_closure_set(v___f_1177_, 1, v_occurrence_1176_);
lean_closure_set(v___f_1177_, 2, v_p_1175_);
v___x_1178_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1178_, 0, v___f_1177_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*1, v_phase_1173_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replacePass___boxed(lean_object* v_phase_1179_, lean_object* v_targetName_1180_, lean_object* v_p_1181_, lean_object* v_occurrence_1182_){
_start:
{
uint8_t v_phase_boxed_1183_; lean_object* v_res_1184_; 
v_phase_boxed_1183_ = lean_unbox(v_phase_1179_);
v_res_1184_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_boxed_1183_, v_targetName_1180_, v_p_1181_, v_occurrence_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(uint8_t v_phase_1185_, lean_object* v_targetName_1186_, lean_object* v_p_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Compiler_LCNF_PassInstaller_replacePass(v_phase_1185_, v_targetName_1186_, v_p_1187_, v_x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed(lean_object* v_phase_1190_, lean_object* v_targetName_1191_, lean_object* v_p_1192_, lean_object* v_x_1193_){
_start:
{
uint8_t v_phase_boxed_1194_; lean_object* v_res_1195_; 
v_phase_boxed_1194_ = lean_unbox(v_phase_1190_);
v_res_1195_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0(v_phase_boxed_1194_, v_targetName_1191_, v_p_1192_, v_x_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(uint8_t v_phase_1196_, lean_object* v_targetName_1197_, lean_object* v_p_1198_){
_start:
{
lean_object* v___x_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_box(v_phase_1196_);
lean_inc(v_targetName_1197_);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1200_, 0, v___x_1199_);
lean_closure_set(v___f_1200_, 1, v_targetName_1197_);
lean_closure_set(v___f_1200_, 2, v_p_1198_);
v___x_1201_ = l_Lean_Compiler_LCNF_PassInstaller_withEachOccurrence(v_phase_1196_, v_targetName_1197_, v___f_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence___boxed(lean_object* v_phase_1202_, lean_object* v_targetName_1203_, lean_object* v_p_1204_){
_start:
{
uint8_t v_phase_boxed_1205_; lean_object* v_res_1206_; 
v_phase_boxed_1205_ = lean_unbox(v_phase_1202_);
v_res_1206_ = l_Lean_Compiler_LCNF_PassInstaller_replaceEachOccurrence(v_phase_boxed_1205_, v_targetName_1203_, v_p_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run(lean_object* v_manager_1207_, lean_object* v_installer_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
uint8_t v_phase_1212_; 
v_phase_1212_ = lean_ctor_get_uint8(v_installer_1208_, sizeof(void*)*1);
switch(v_phase_1212_)
{
case 0:
{
lean_object* v_install_1213_; lean_object* v_basePasses_1214_; lean_object* v_monoPasses_1215_; lean_object* v_monoPassesNoLambda_1216_; lean_object* v_impurePasses_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1241_; 
v_install_1213_ = lean_ctor_get(v_installer_1208_, 0);
lean_inc_ref(v_install_1213_);
lean_dec_ref(v_installer_1208_);
v_basePasses_1214_ = lean_ctor_get(v_manager_1207_, 0);
v_monoPasses_1215_ = lean_ctor_get(v_manager_1207_, 1);
v_monoPassesNoLambda_1216_ = lean_ctor_get(v_manager_1207_, 2);
v_impurePasses_1217_ = lean_ctor_get(v_manager_1207_, 3);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_manager_1207_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1219_ = v_manager_1207_;
v_isShared_1220_ = v_isSharedCheck_1241_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_impurePasses_1217_);
lean_inc(v_monoPassesNoLambda_1216_);
lean_inc(v_monoPasses_1215_);
lean_inc(v_basePasses_1214_);
lean_dec(v_manager_1207_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1241_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; 
lean_inc(v_a_1210_);
lean_inc_ref(v_a_1209_);
v___x_1221_ = lean_apply_4(v_install_1213_, v_basePasses_1214_, v_a_1209_, v_a_1210_, lean_box(0));
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1232_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1232_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1232_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v_a_1222_);
v___x_1227_ = v___x_1219_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1222_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_monoPasses_1215_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_monoPassesNoLambda_1216_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_impurePasses_1217_);
v___x_1227_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1229_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1227_);
v___x_1229_ = v___x_1224_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_del_object(v___x_1219_);
lean_dec_ref(v_impurePasses_1217_);
lean_dec_ref(v_monoPassesNoLambda_1216_);
lean_dec_ref(v_monoPasses_1215_);
v_a_1233_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1221_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1221_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
case 1:
{
lean_object* v_install_1242_; lean_object* v_basePasses_1243_; lean_object* v_monoPasses_1244_; lean_object* v_monoPassesNoLambda_1245_; lean_object* v_impurePasses_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1270_; 
v_install_1242_ = lean_ctor_get(v_installer_1208_, 0);
lean_inc_ref(v_install_1242_);
lean_dec_ref(v_installer_1208_);
v_basePasses_1243_ = lean_ctor_get(v_manager_1207_, 0);
v_monoPasses_1244_ = lean_ctor_get(v_manager_1207_, 1);
v_monoPassesNoLambda_1245_ = lean_ctor_get(v_manager_1207_, 2);
v_impurePasses_1246_ = lean_ctor_get(v_manager_1207_, 3);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_manager_1207_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1248_ = v_manager_1207_;
v_isShared_1249_ = v_isSharedCheck_1270_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_impurePasses_1246_);
lean_inc(v_monoPassesNoLambda_1245_);
lean_inc(v_monoPasses_1244_);
lean_inc(v_basePasses_1243_);
lean_dec(v_manager_1207_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1270_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; 
lean_inc(v_a_1210_);
lean_inc_ref(v_a_1209_);
v___x_1250_ = lean_apply_4(v_install_1242_, v_monoPasses_1244_, v_a_1209_, v_a_1210_, lean_box(0));
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1261_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1261_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1261_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v_a_1251_);
v___x_1256_ = v___x_1248_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_basePasses_1243_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_a_1251_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_monoPassesNoLambda_1245_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_impurePasses_1246_);
v___x_1256_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1258_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1256_);
v___x_1258_ = v___x_1253_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_del_object(v___x_1248_);
lean_dec_ref(v_impurePasses_1246_);
lean_dec_ref(v_monoPassesNoLambda_1245_);
lean_dec_ref(v_basePasses_1243_);
v_a_1262_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1250_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1250_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
default: 
{
lean_object* v_install_1271_; lean_object* v_basePasses_1272_; lean_object* v_monoPasses_1273_; lean_object* v_monoPassesNoLambda_1274_; lean_object* v_impurePasses_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1299_; 
v_install_1271_ = lean_ctor_get(v_installer_1208_, 0);
lean_inc_ref(v_install_1271_);
lean_dec_ref(v_installer_1208_);
v_basePasses_1272_ = lean_ctor_get(v_manager_1207_, 0);
v_monoPasses_1273_ = lean_ctor_get(v_manager_1207_, 1);
v_monoPassesNoLambda_1274_ = lean_ctor_get(v_manager_1207_, 2);
v_impurePasses_1275_ = lean_ctor_get(v_manager_1207_, 3);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_manager_1207_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1277_ = v_manager_1207_;
v_isShared_1278_ = v_isSharedCheck_1299_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_impurePasses_1275_);
lean_inc(v_monoPassesNoLambda_1274_);
lean_inc(v_monoPasses_1273_);
lean_inc(v_basePasses_1272_);
lean_dec(v_manager_1207_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1299_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1279_; 
lean_inc(v_a_1210_);
lean_inc_ref(v_a_1209_);
v___x_1279_ = lean_apply_4(v_install_1271_, v_impurePasses_1275_, v_a_1209_, v_a_1210_, lean_box(0));
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1290_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1290_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1290_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 3, v_a_1280_);
v___x_1285_ = v___x_1277_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_basePasses_1272_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_monoPasses_1273_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_monoPassesNoLambda_1274_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1287_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1285_);
v___x_1287_ = v___x_1282_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_del_object(v___x_1277_);
lean_dec_ref(v_monoPassesNoLambda_1274_);
lean_dec_ref(v_monoPasses_1273_);
lean_dec_ref(v_basePasses_1272_);
v_a_1291_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1279_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1279_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_run___boxed(lean_object* v_manager_1300_, lean_object* v_installer_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1300_, v_installer_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(lean_object* v_x_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
if (lean_obj_tag(v_x_1306_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_a_1310_ = lean_ctor_get(v_x_1306_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v_x_1306_, 1);
v___x_1311_ = l_Lean_stringToMessageData(v_a_1310_);
v___x_1312_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassManager_validatePasses_spec__0___redArg(v___x_1311_, v___y_1307_, v___y_1308_);
return v___x_1312_;
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
v_a_1313_ = lean_ctor_get(v_x_1306_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_x_1306_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v_x_1306_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v_x_1306_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set_tag(v___x_1315_, 0);
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg___boxed(lean_object* v_x_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(lean_object* v_declName_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v___x_1338_; lean_object* v_env_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1338_ = lean_st_ref_get(v_a_1336_);
v_env_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc_ref(v_env_1339_);
lean_dec(v___x_1338_);
v___x_1340_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1335_);
v___x_1341_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___closed__3));
v___x_1342_ = l_Lean_Environment_evalConstCheck___redArg(v_env_1339_, v___x_1340_, v___x_1341_, v_declName_1334_);
lean_dec_ref(v___x_1340_);
v___x_1343_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v___x_1342_, v_a_1335_, v_a_1336_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe___boxed(lean_object* v_declName_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1344_, v_a_1345_, v_a_1346_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(lean_object* v_00_u03b1_1349_, lean_object* v_x_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___redArg(v_x_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_x_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe_spec__0(v_00_u03b1_1355_, v_x_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(lean_object* v_manager_1361_, lean_object* v_declName_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Lean_Compiler_LCNF_PassManager_0__Lean_Compiler_LCNF_PassInstaller_getPassInstallerUnsafe(v_declName_1362_, v_a_1363_, v_a_1364_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1368_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = l_Lean_Compiler_LCNF_PassInstaller_run(v_manager_1361_, v_a_1367_, v_a_1363_, v_a_1364_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = l_Lean_Compiler_LCNF_PassManager_validate(v_a_1369_, v_a_1363_, v_a_1364_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v___x_1370_, 0);
lean_dec(v_unused_1378_);
v___x_1372_ = v___x_1370_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v___x_1370_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v_a_1369_);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1369_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_a_1369_);
v_a_1379_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1370_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1370_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
return v___x_1368_;
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v_manager_1361_);
v_a_1387_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1366_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1366_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PassInstaller_runFromDecl___boxed(lean_object* v_manager_1395_, lean_object* v_declName_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_manager_1395_, v_declName_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
return v_res_1400_;
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
