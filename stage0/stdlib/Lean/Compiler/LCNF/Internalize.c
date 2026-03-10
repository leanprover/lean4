// Lean compiler output
// Module: Lean.Compiler.LCNF.Internalize
// Imports: public import Lean.Compiler.LCNF.Bind
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
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___boxed(lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_value;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_value;
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_value;
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3_value;
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4_value;
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5_value;
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__5_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__4_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__6_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__3_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10_value;
lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11;
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfMonadStateOf___redArg(lean_object*);
lean_object* l_modify(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___boxed(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "_private.Lean.Compiler.LCNF.Internalize.0.Lean.Compiler.LCNF.Internalize.internalizeExpr.go"};
static const lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Compiler.LCNF.Internalize"};
static const lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Compiler_LCNF_findParam_x3f___redArg(uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Lean.Compiler.LCNF.Internalize.internalizeCodeDecl"};
static const lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_cleanup___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_cleanup___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2_value;
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_st_mk_ref(x_2);
x_10 = lean_box(x_3);
lean_inc(x_9);
x_11 = lean_apply_7(x_1, x_10, x_9, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_21; 
x_12 = lean_ctor_get(x_11, 0);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
x_13 = x_11;
x_14 = x_21;
goto block_20;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_st_ref_get(x_9);
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_16);
x_17 = x_13;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec(x_9);
x_22 = lean_ctor_get(x_11, 0);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
x_23 = x_11;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_st_mk_ref(x_4);
x_12 = lean_box(x_5);
lean_inc(x_11);
x_13 = lean_apply_7(x_3, x_12, x_11, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_23; 
x_14 = lean_ctor_get(x_13, 0);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
x_15 = x_13;
x_16 = x_23;
goto block_22;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_st_ref_get(x_11);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec(x_11);
x_24 = lean_ctor_get(x_13, 0);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
x_25 = x_13;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run(x_11, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_st_mk_ref(x_2);
x_10 = lean_box(x_3);
lean_inc(x_9);
x_11 = lean_apply_7(x_1, x_10, x_9, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_st_ref_get(x_9);
lean_dec(x_9);
lean_dec(x_15);
if (x_14 == 0)
{
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_st_mk_ref(x_4);
x_12 = lean_box(x_5);
lean_inc(x_11);
x_13 = lean_apply_7(x_3, x_12, x_11, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_22; 
x_14 = lean_ctor_get(x_13, 0);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
x_15 = x_13;
x_16 = x_22;
goto block_21;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_st_ref_get(x_11);
lean_dec(x_11);
lean_dec(x_17);
if (x_16 == 0)
{
x_18 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_dec(x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Compiler_LCNF_Internalize_InternalizeM_run_x27(x_11, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_22; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_st_ref_get(x_3);
x_7 = lean_st_ref_take(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
x_10 = x_7;
x_11 = x_22;
goto block_21;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_9, x_12);
lean_dec(x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_13);
x_14 = x_10;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_13);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_st_ref_set(x_3, x_14);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l_Lean_Name_num___override(x_5, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
if (x_2 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_1);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_40; 
x_24 = lean_st_ref_get(x_3);
x_25 = lean_st_ref_take(x_3);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 1);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
x_28 = x_25;
x_29 = x_40;
goto block_39;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_27, x_30);
lean_dec(x_27);
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_31);
x_32 = x_28;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_31);
x_32 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_st_ref_set(x_3, x_32);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = l_Lean_Name_num___override(x_1, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(x_1, x_5, x_3);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(x_2, x_3, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_st_ref_get(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___lam__0(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__10));
x_2 = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0));
x_3 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11, &l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11_once, _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__11);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
lean_ctor_set(x_7, 1, x_9);
lean_ctor_set(x_7, 0, x_11);
x_12 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_10);
x_12 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_instMonadStateOfMonadStateOf___redArg(x_12);
x_14 = lean_alloc_closure((void*)(l_modify), 4, 3);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_instHashableFVarId_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_instHashableFVarId_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_35; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
x_7 = x_4;
x_8 = x_35;
goto block_34;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_32; 
x_9 = lean_st_ref_take(x_1);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 3);
x_13 = lean_ctor_get(x_9, 4);
x_14 = lean_ctor_get(x_9, 5);
x_15 = lean_ctor_get(x_9, 6);
x_16 = lean_ctor_get(x_9, 7);
x_17 = lean_ctor_get(x_9, 8);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_9, 2);
lean_dec(x_33);
x_18 = x_9;
x_19 = x_32;
goto block_31;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Name_num___override(x_5, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_6, x_21);
lean_dec(x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_22);
x_23 = x_7;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_22);
x_23 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_24; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 2, x_23);
x_24 = x_18;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_12);
lean_ctor_set(x_28, 4, x_13);
lean_ctor_set(x_28, 5, x_14);
lean_ctor_set(x_28, 6, x_15);
lean_ctor_set(x_28, 7, x_16);
lean_ctor_set(x_28, 8, x_17);
x_24 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_st_ref_set(x_1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_20);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_16; 
x_8 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(x_6);
x_9 = lean_ctor_get(x_8, 0);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
x_10 = x_8;
x_11 = x_16;
goto block_15;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_11 == 0)
{
x_12 = x_10;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_21; 
x_10 = lean_ctor_get(x_9, 0);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
x_11 = x_9;
x_12 = x_21;
goto block_20;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_st_ref_take(x_3);
lean_inc(x_10);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_10);
x_15 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(x_13, x_1, x_14);
x_16 = lean_st_ref_set(x_3, x_15);
if (x_12 == 0)
{
x_17 = x_11;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_10);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3_spec__4_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_instHashableFVarId_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_75; 
x_9 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_75 = !lean_is_exclusive(x_10);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_10, 1);
lean_dec(x_76);
x_12 = x_10;
x_13 = x_75;
goto block_74;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_72; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_72 = !lean_is_exclusive(x_11);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_11, 1);
lean_dec(x_73);
x_18 = x_11;
x_19 = x_72;
goto block_71;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_16);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_25);
lean_ctor_set(x_18, 3, x_26);
lean_ctor_set(x_18, 2, x_27);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_24);
x_28 = x_18;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_24);
lean_ctor_set(x_70, 1, x_20);
lean_ctor_set(x_70, 2, x_27);
lean_ctor_set(x_70, 3, x_26);
lean_ctor_set(x_70, 4, x_25);
x_28 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_29; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_28);
x_29 = x_12;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_28);
lean_ctor_set(x_68, 1, x_21);
x_29 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_65; 
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = lean_ctor_get(x_30, 0);
x_65 = !lean_is_exclusive(x_30);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_30, 1);
lean_dec(x_66);
x_32 = x_30;
x_33 = x_65;
goto block_64;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_62; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_31, 1);
lean_dec(x_63);
x_38 = x_31;
x_39 = x_62;
goto block_61;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_36);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_35);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_45);
lean_ctor_set(x_38, 3, x_46);
lean_ctor_set(x_38, 2, x_47);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_44);
x_48 = x_38;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_40);
lean_ctor_set(x_60, 2, x_47);
lean_ctor_set(x_60, 3, x_46);
lean_ctor_set(x_60, 4, x_45);
x_48 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_49; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_41);
lean_ctor_set(x_32, 0, x_48);
x_49 = x_32;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_41);
x_49 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = l_Lean_instInhabitedExpr;
x_52 = l_instInhabitedOfMonad___redArg(x_50, x_51);
x_53 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_panic_fn(x_53, x_1);
x_55 = lean_box(x_2);
x_56 = lean_apply_7(x_54, x_55, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_56;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(20u);
x_3 = lean_unsigned_to_nat(89u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasFVar(x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(x_13, x_12);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_61; 
lean_dec_ref(x_2);
x_16 = lean_ctor_get(x_14, 0);
x_61 = !lean_is_exclusive(x_14);
if (x_61 == 0)
{
x_17 = x_14;
x_18 = x_61;
goto block_60;
}
else
{
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = x_61;
goto block_60;
}
block_60:
{
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
x_19 = l_Lean_Compiler_LCNF_erasedExpr;
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
case 1:
{
lean_object* x_23; lean_object* x_24; 
lean_del_object(x_17);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec_ref(x_16);
x_24 = l_Lean_Compiler_LCNF_findParam_x3f___redArg(x_1, x_23, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_43; 
x_25 = lean_ctor_get(x_24, 0);
x_43 = !lean_is_exclusive(x_24);
if (x_43 == 0)
{
x_26 = x_24;
x_27 = x_43;
goto block_42;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_43;
goto block_42;
}
block_42:
{
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_23);
goto block_32;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_40; 
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_25, 0);
lean_dec(x_41);
x_33 = x_25;
x_34 = x_40;
goto block_39;
}
else
{
lean_dec(x_25);
x_33 = lean_box(0);
x_34 = x_40;
goto block_39;
}
block_39:
{
if (x_10 == 0)
{
lean_del_object(x_33);
lean_dec(x_23);
goto block_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_del_object(x_26);
x_35 = l_Lean_Expr_fvar___override(x_23);
if (x_34 == 0)
{
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_35);
x_36 = x_33;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
block_32:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Compiler_LCNF_anyExpr;
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_28);
x_29 = x_26;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_23);
x_44 = lean_ctor_get(x_24, 0);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
x_45 = x_24;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_24);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
default: 
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_del_object(x_17);
lean_dec(x_6);
x_52 = lean_ctor_get(x_16, 0);
x_59 = !lean_is_exclusive(x_16);
if (x_59 == 0)
{
x_53 = x_16;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_16);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
lean_ctor_set_tag(x_53, 0);
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
}
}
case 5:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_62);
x_64 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(x_1, x_62, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_inc_ref(x_63);
x_66 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_63, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_86; 
x_67 = lean_ctor_get(x_66, 0);
x_86 = !lean_is_exclusive(x_66);
if (x_86 == 0)
{
x_68 = x_66;
x_69 = x_86;
goto block_85;
}
else
{
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_70; uint8_t x_76; size_t x_79; size_t x_80; uint8_t x_81; 
x_79 = lean_ptr_addr(x_62);
x_80 = lean_ptr_addr(x_65);
x_81 = lean_usize_dec_eq(x_79, x_80);
if (x_81 == 0)
{
x_76 = x_81;
goto block_78;
}
else
{
size_t x_82; size_t x_83; uint8_t x_84; 
x_82 = lean_ptr_addr(x_63);
x_83 = lean_ptr_addr(x_67);
x_84 = lean_usize_dec_eq(x_82, x_83);
x_76 = x_84;
goto block_78;
}
block_75:
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lean_Expr_headBeta(x_70);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_71);
x_72 = x_68;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
block_78:
{
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec_ref(x_2);
x_77 = l_Lean_Expr_app___override(x_65, x_67);
x_70 = x_77;
goto block_75;
}
else
{
lean_dec(x_67);
lean_dec(x_65);
x_70 = x_2;
goto block_75;
}
}
}
}
else
{
lean_dec(x_65);
lean_dec_ref(x_2);
return x_66;
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_64;
}
}
case 6:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_2, 0);
x_88 = lean_ctor_get(x_2, 1);
x_89 = lean_ctor_get(x_2, 2);
x_90 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_88);
x_91 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_88, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
lean_inc_ref(x_89);
x_93 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_89, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_118; 
x_94 = lean_ctor_get(x_93, 0);
x_118 = !lean_is_exclusive(x_93);
if (x_118 == 0)
{
x_95 = x_93;
x_96 = x_118;
goto block_117;
}
else
{
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_box(0);
x_96 = x_118;
goto block_117;
}
block_117:
{
uint8_t x_97; size_t x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ptr_addr(x_88);
x_112 = lean_ptr_addr(x_92);
x_113 = lean_usize_dec_eq(x_111, x_112);
if (x_113 == 0)
{
x_97 = x_113;
goto block_110;
}
else
{
size_t x_114; size_t x_115; uint8_t x_116; 
x_114 = lean_ptr_addr(x_89);
x_115 = lean_ptr_addr(x_94);
x_116 = lean_usize_dec_eq(x_114, x_115);
x_97 = x_116;
goto block_110;
}
block_110:
{
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_inc(x_87);
lean_dec_ref(x_2);
x_98 = l_Lean_Expr_lam___override(x_87, x_92, x_94, x_90);
if (x_96 == 0)
{
lean_ctor_set(x_95, 0, x_98);
x_99 = x_95;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_98);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
else
{
uint8_t x_102; 
x_102 = l_Lean_instBEqBinderInfo_beq(x_90, x_90);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_inc(x_87);
lean_dec_ref(x_2);
x_103 = l_Lean_Expr_lam___override(x_87, x_92, x_94, x_90);
if (x_96 == 0)
{
lean_ctor_set(x_95, 0, x_103);
x_104 = x_95;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_103);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
else
{
lean_object* x_107; 
lean_dec(x_94);
lean_dec(x_92);
if (x_96 == 0)
{
lean_ctor_set(x_95, 0, x_2);
x_107 = x_95;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_2);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
}
}
}
else
{
lean_dec(x_92);
lean_dec_ref(x_2);
return x_93;
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_91;
}
}
case 7:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_2, 0);
x_120 = lean_ctor_get(x_2, 1);
x_121 = lean_ctor_get(x_2, 2);
x_122 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_120);
x_123 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_120, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
lean_inc_ref(x_121);
x_125 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_121, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_150; 
x_126 = lean_ctor_get(x_125, 0);
x_150 = !lean_is_exclusive(x_125);
if (x_150 == 0)
{
x_127 = x_125;
x_128 = x_150;
goto block_149;
}
else
{
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_box(0);
x_128 = x_150;
goto block_149;
}
block_149:
{
uint8_t x_129; size_t x_143; size_t x_144; uint8_t x_145; 
x_143 = lean_ptr_addr(x_120);
x_144 = lean_ptr_addr(x_124);
x_145 = lean_usize_dec_eq(x_143, x_144);
if (x_145 == 0)
{
x_129 = x_145;
goto block_142;
}
else
{
size_t x_146; size_t x_147; uint8_t x_148; 
x_146 = lean_ptr_addr(x_121);
x_147 = lean_ptr_addr(x_126);
x_148 = lean_usize_dec_eq(x_146, x_147);
x_129 = x_148;
goto block_142;
}
block_142:
{
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_inc(x_119);
lean_dec_ref(x_2);
x_130 = l_Lean_Expr_forallE___override(x_119, x_124, x_126, x_122);
if (x_128 == 0)
{
lean_ctor_set(x_127, 0, x_130);
x_131 = x_127;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_130);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
else
{
uint8_t x_134; 
x_134 = l_Lean_instBEqBinderInfo_beq(x_122, x_122);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_inc(x_119);
lean_dec_ref(x_2);
x_135 = l_Lean_Expr_forallE___override(x_119, x_124, x_126, x_122);
if (x_128 == 0)
{
lean_ctor_set(x_127, 0, x_135);
x_136 = x_127;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_135);
x_136 = x_138;
goto block_137;
}
block_137:
{
return x_136;
}
}
else
{
lean_object* x_139; 
lean_dec(x_126);
lean_dec(x_124);
if (x_128 == 0)
{
lean_ctor_set(x_127, 0, x_2);
x_139 = x_127;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_2);
x_139 = x_141;
goto block_140;
}
block_140:
{
return x_139;
}
}
}
}
}
}
else
{
lean_dec(x_124);
lean_dec_ref(x_2);
return x_125;
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_123;
}
}
case 8:
{
lean_object* x_151; lean_object* x_152; 
lean_dec_ref(x_2);
x_151 = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
x_152 = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(x_151, x_3, x_4, x_5, x_6, x_7, x_8);
return x_152;
}
case 10:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_2, 0);
x_154 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_154);
x_155 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_154, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_170; 
x_156 = lean_ctor_get(x_155, 0);
x_170 = !lean_is_exclusive(x_155);
if (x_170 == 0)
{
x_157 = x_155;
x_158 = x_170;
goto block_169;
}
else
{
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_box(0);
x_158 = x_170;
goto block_169;
}
block_169:
{
size_t x_159; size_t x_160; uint8_t x_161; 
x_159 = lean_ptr_addr(x_154);
x_160 = lean_ptr_addr(x_156);
x_161 = lean_usize_dec_eq(x_159, x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_inc(x_153);
lean_dec_ref(x_2);
x_162 = l_Lean_Expr_mdata___override(x_153, x_156);
if (x_158 == 0)
{
lean_ctor_set(x_157, 0, x_162);
x_163 = x_157;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_162);
x_163 = x_165;
goto block_164;
}
block_164:
{
return x_163;
}
}
else
{
lean_object* x_166; 
lean_dec(x_156);
if (x_158 == 0)
{
lean_ctor_set(x_157, 0, x_2);
x_166 = x_157;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_2);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_155;
}
}
case 11:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_2, 0);
x_172 = lean_ctor_get(x_2, 1);
x_173 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_173);
x_174 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_173, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_189; 
x_175 = lean_ctor_get(x_174, 0);
x_189 = !lean_is_exclusive(x_174);
if (x_189 == 0)
{
x_176 = x_174;
x_177 = x_189;
goto block_188;
}
else
{
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_box(0);
x_177 = x_189;
goto block_188;
}
block_188:
{
size_t x_178; size_t x_179; uint8_t x_180; 
x_178 = lean_ptr_addr(x_173);
x_179 = lean_ptr_addr(x_175);
x_180 = lean_usize_dec_eq(x_178, x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
lean_inc(x_172);
lean_inc(x_171);
lean_dec_ref(x_2);
x_181 = l_Lean_Expr_proj___override(x_171, x_172, x_175);
if (x_177 == 0)
{
lean_ctor_set(x_176, 0, x_181);
x_182 = x_176;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_181);
x_182 = x_184;
goto block_183;
}
block_183:
{
return x_182;
}
}
else
{
lean_object* x_185; 
lean_dec(x_175);
if (x_177 == 0)
{
lean_ctor_set(x_176, 0, x_2);
x_185 = x_176;
goto block_186;
}
else
{
lean_object* x_187; 
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_2);
x_185 = x_187;
goto block_186;
}
block_186:
{
return x_185;
}
}
}
}
else
{
lean_dec_ref(x_2);
return x_174;
}
}
default: 
{
lean_object* x_190; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_2);
return x_190;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_10);
x_12 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc_ref(x_11);
x_14 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_34; 
x_15 = lean_ctor_get(x_14, 0);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
x_16 = x_14;
x_17 = x_34;
goto block_33;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_34;
goto block_33;
}
block_33:
{
uint8_t x_18; size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = lean_ptr_addr(x_10);
x_28 = lean_ptr_addr(x_13);
x_29 = lean_usize_dec_eq(x_27, x_28);
if (x_29 == 0)
{
x_18 = x_29;
goto block_26;
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
x_30 = lean_ptr_addr(x_11);
x_31 = lean_ptr_addr(x_15);
x_32 = lean_usize_dec_eq(x_30, x_31);
x_18 = x_32;
goto block_26;
}
block_26:
{
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_2);
x_19 = l_Lean_Expr_app___override(x_13, x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_13);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_2);
x_23 = x_16;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_2);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_2);
return x_14;
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_12;
}
}
else
{
lean_object* x_35; 
x_35 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_61; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_61 = !lean_is_exclusive(x_2);
if (x_61 == 0)
{
x_14 = x_2;
x_15 = x_61;
goto block_60;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(x_11, x_3, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_18 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_43; 
x_21 = lean_ctor_get(x_20, 0);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
x_22 = x_20;
x_23 = x_43;
goto block_42;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_41; 
x_24 = lean_st_ref_take(x_6);
x_25 = lean_ctor_get(x_24, 0);
x_26 = lean_ctor_get(x_24, 1);
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
x_27 = x_24;
x_28 = x_41;
goto block_40;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_29; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 2, x_19);
lean_ctor_set(x_14, 1, x_17);
lean_ctor_set(x_14, 0, x_21);
x_29 = x_14;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_17);
lean_ctor_set(x_39, 2, x_19);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_13);
x_29 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_29);
x_30 = l_Lean_Compiler_LCNF_LCtx_addParam(x_1, x_25, x_29);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_26);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_st_ref_set(x_6, x_31);
lean_dec(x_6);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_29);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_29);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_19);
lean_dec(x_17);
lean_del_object(x_14);
lean_dec(x_6);
x_44 = lean_ctor_get(x_20, 0);
x_51 = !lean_is_exclusive(x_20);
if (x_51 == 0)
{
x_45 = x_20;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec(x_17);
lean_del_object(x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_52 = lean_ctor_get(x_18, 0);
x_59 = !lean_is_exclusive(x_18);
if (x_59 == 0)
{
x_53 = x_18;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_18);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(x_12, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_45; 
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_13, 0);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
x_16 = x_13;
x_17 = x_45;
goto block_44;
}
else
{
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_45;
goto block_44;
}
block_44:
{
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
case 1:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_32; 
x_22 = lean_ctor_get(x_15, 0);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
x_23 = x_15;
x_24 = x_32;
goto block_31;
}
else
{
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_box(0);
x_24 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_22);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_25);
x_26 = x_16;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
default: 
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_43; 
x_33 = lean_ctor_get(x_15, 0);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
x_34 = x_15;
x_35 = x_43;
goto block_42;
}
else
{
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_33);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_36);
x_37 = x_16;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
}
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_46);
x_47 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_46, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_56; 
x_48 = lean_ctor_get(x_47, 0);
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
x_49 = x_47;
x_50 = x_56;
goto block_55;
}
else
{
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_51; lean_object* x_52; 
x_51 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(x_1, x_2, x_48);
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_51);
x_52 = x_49;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec_ref(x_2);
x_57 = lean_ctor_get(x_47, 0);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
x_58 = x_47;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Compiler_LCNF_Internalize_internalizeArg(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget_borrowed(x_4, x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_15 = l_Lean_Compiler_LCNF_Internalize_internalizeArg(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_18, x_3, x_16);
x_3 = x_20;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
x_23 = lean_ctor_get(x_15, 0);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
x_24 = x_15;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(x_12, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(x_1, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_53 = lean_ctor_get(x_2, 2);
x_54 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_55 = 1;
lean_inc(x_53);
x_56 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_54, x_53, x_55);
lean_dec(x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_65; 
x_57 = lean_ctor_get(x_56, 0);
x_65 = !lean_is_exclusive(x_56);
if (x_65 == 0)
{
x_58 = x_56;
x_59 = x_65;
goto block_64;
}
else
{
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_60; lean_object* x_61; 
x_60 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_1, x_2, x_57);
if (x_59 == 0)
{
lean_ctor_set(x_58, 0, x_60);
x_61 = x_58;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_60);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_2);
x_66 = lean_box(1);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
case 3:
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_68);
x_69 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_68, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_78; 
x_70 = lean_ctor_get(x_69, 0);
x_78 = !lean_is_exclusive(x_69);
if (x_78 == 0)
{
x_71 = x_69;
x_72 = x_78;
goto block_77;
}
else
{
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_box(0);
x_72 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_73; lean_object* x_74; 
x_73 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_1, x_2, x_70);
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_73);
x_74 = x_71;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_73);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec_ref(x_2);
x_79 = lean_ctor_get(x_69, 0);
x_86 = !lean_is_exclusive(x_69);
if (x_86 == 0)
{
x_80 = x_69;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_69);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
case 4:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_2, 0);
x_88 = lean_ctor_get(x_2, 1);
x_89 = lean_st_ref_get(x_4);
x_90 = 1;
lean_inc(x_87);
x_91 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_89, x_87, x_90);
lean_dec(x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
lean_inc_ref(x_88);
x_93 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_88, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_102; 
x_94 = lean_ctor_get(x_93, 0);
x_102 = !lean_is_exclusive(x_93);
if (x_102 == 0)
{
x_95 = x_93;
x_96 = x_102;
goto block_101;
}
else
{
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_box(0);
x_96 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_97; lean_object* x_98; 
x_97 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(x_1, x_2, x_92, x_94);
lean_dec_ref(x_2);
if (x_96 == 0)
{
lean_ctor_set(x_95, 0, x_97);
x_98 = x_95;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_97);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec(x_92);
lean_dec_ref(x_2);
x_103 = lean_ctor_get(x_93, 0);
x_110 = !lean_is_exclusive(x_93);
if (x_110 == 0)
{
x_104 = x_93;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_93);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_103);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_2);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_111 = lean_box(1);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
case 5:
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_113);
x_114 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_113, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_123; 
x_115 = lean_ctor_get(x_114, 0);
x_123 = !lean_is_exclusive(x_114);
if (x_123 == 0)
{
x_116 = x_114;
x_117 = x_123;
goto block_122;
}
else
{
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_box(0);
x_117 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_118; lean_object* x_119; 
x_118 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_1, x_2, x_115);
if (x_117 == 0)
{
lean_ctor_set(x_116, 0, x_118);
x_119 = x_116;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_118);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_131; 
lean_dec_ref(x_2);
x_124 = lean_ctor_get(x_114, 0);
x_131 = !lean_is_exclusive(x_114);
if (x_131 == 0)
{
x_125 = x_114;
x_126 = x_131;
goto block_130;
}
else
{
lean_inc(x_124);
lean_dec(x_114);
x_125 = lean_box(0);
x_126 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_127; 
if (x_126 == 0)
{
x_127 = x_125;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_124);
x_127 = x_129;
goto block_128;
}
block_128:
{
return x_127;
}
}
}
}
case 6:
{
lean_object* x_132; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_132 = lean_ctor_get(x_2, 1);
lean_inc(x_132);
x_10 = x_132;
x_11 = x_4;
goto block_26;
}
case 7:
{
lean_object* x_133; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_133 = lean_ctor_get(x_2, 1);
lean_inc(x_133);
x_10 = x_133;
x_11 = x_4;
goto block_26;
}
case 8:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_134 = lean_ctor_get(x_2, 2);
x_135 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_136 = 1;
lean_inc(x_134);
x_137 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_135, x_134, x_136);
lean_dec(x_135);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_146; 
x_138 = lean_ctor_get(x_137, 0);
x_146 = !lean_is_exclusive(x_137);
if (x_146 == 0)
{
x_139 = x_137;
x_140 = x_146;
goto block_145;
}
else
{
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_box(0);
x_140 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_141; lean_object* x_142; 
x_141 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_1, x_2, x_138);
if (x_140 == 0)
{
lean_ctor_set(x_139, 0, x_141);
x_142 = x_139;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_141);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec_ref(x_2);
x_147 = lean_box(1);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
case 9:
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_149);
x_27 = x_149;
x_28 = x_3;
x_29 = x_4;
x_30 = x_5;
x_31 = x_6;
x_32 = x_7;
x_33 = x_8;
goto block_52;
}
case 10:
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_150);
x_27 = x_150;
x_28 = x_3;
x_29 = x_4;
x_30 = x_5;
x_31 = x_6;
x_32 = x_7;
x_33 = x_8;
goto block_52;
}
case 11:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_151 = lean_ctor_get(x_2, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_2, 1);
x_153 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_154 = 1;
lean_inc(x_152);
x_155 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_153, x_152, x_154);
lean_dec(x_153);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_164; 
x_156 = lean_ctor_get(x_155, 0);
x_164 = !lean_is_exclusive(x_155);
if (x_164 == 0)
{
x_157 = x_155;
x_158 = x_164;
goto block_163;
}
else
{
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_box(0);
x_158 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_159; lean_object* x_160; 
x_159 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(x_1, x_2, x_151, x_156);
lean_dec_ref(x_2);
if (x_158 == 0)
{
lean_ctor_set(x_157, 0, x_159);
x_160 = x_157;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_159);
x_160 = x_162;
goto block_161;
}
block_161:
{
return x_160;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_2);
lean_dec(x_151);
x_165 = lean_box(1);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
case 12:
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_2, 0);
x_168 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_168);
x_169 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_170 = lean_ctor_get(x_2, 2);
x_171 = lean_st_ref_get(x_4);
x_172 = 1;
lean_inc(x_167);
x_173 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_171, x_167, x_172);
lean_dec(x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
lean_inc_ref(x_170);
x_175 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_170, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; uint8_t x_184; 
x_176 = lean_ctor_get(x_175, 0);
x_184 = !lean_is_exclusive(x_175);
if (x_184 == 0)
{
x_177 = x_175;
x_178 = x_184;
goto block_183;
}
else
{
lean_inc(x_176);
lean_dec(x_175);
x_177 = lean_box(0);
x_178 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_179; lean_object* x_180; 
x_179 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(x_1, x_2, x_174, x_168, x_169, x_176);
if (x_178 == 0)
{
lean_ctor_set(x_177, 0, x_179);
x_180 = x_177;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_179);
x_180 = x_182;
goto block_181;
}
block_181:
{
return x_180;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_192; 
lean_dec(x_174);
lean_dec_ref(x_168);
lean_dec_ref(x_2);
x_185 = lean_ctor_get(x_175, 0);
x_192 = !lean_is_exclusive(x_175);
if (x_192 == 0)
{
x_186 = x_175;
x_187 = x_192;
goto block_191;
}
else
{
lean_inc(x_185);
lean_dec(x_175);
x_186 = lean_box(0);
x_187 = x_192;
goto block_191;
}
block_191:
{
lean_object* x_188; 
if (x_187 == 0)
{
x_188 = x_186;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_185);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec_ref(x_168);
lean_dec_ref(x_2);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_193 = lean_box(1);
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_193);
return x_194;
}
}
case 13:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_195 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_2, 1);
x_197 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_198 = 1;
lean_inc(x_196);
x_199 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_197, x_196, x_198);
lean_dec(x_197);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_208; 
x_200 = lean_ctor_get(x_199, 0);
x_208 = !lean_is_exclusive(x_199);
if (x_208 == 0)
{
x_201 = x_199;
x_202 = x_208;
goto block_207;
}
else
{
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_box(0);
x_202 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_203; lean_object* x_204; 
x_203 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(x_1, x_2, x_195, x_200);
lean_dec_ref(x_2);
if (x_202 == 0)
{
lean_ctor_set(x_201, 0, x_203);
x_204 = x_201;
goto block_205;
}
else
{
lean_object* x_206; 
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_203);
x_204 = x_206;
goto block_205;
}
block_205:
{
return x_204;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec_ref(x_2);
lean_dec_ref(x_195);
x_209 = lean_box(1);
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
case 14:
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_211 = lean_ctor_get(x_2, 0);
x_212 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_213 = 1;
lean_inc(x_211);
x_214 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_212, x_211, x_213);
lean_dec(x_212);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_223; 
x_215 = lean_ctor_get(x_214, 0);
x_223 = !lean_is_exclusive(x_214);
if (x_223 == 0)
{
x_216 = x_214;
x_217 = x_223;
goto block_222;
}
else
{
lean_inc(x_215);
lean_dec(x_214);
x_216 = lean_box(0);
x_217 = x_223;
goto block_222;
}
block_222:
{
lean_object* x_218; lean_object* x_219; 
x_218 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(x_1, x_2, x_215);
if (x_217 == 0)
{
lean_ctor_set(x_216, 0, x_218);
x_219 = x_216;
goto block_220;
}
else
{
lean_object* x_221; 
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_218);
x_219 = x_221;
goto block_220;
}
block_220:
{
return x_219;
}
}
}
else
{
lean_object* x_224; uint8_t x_225; uint8_t x_231; 
x_231 = !lean_is_exclusive(x_2);
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_2, 0);
lean_dec(x_232);
x_224 = x_2;
x_225 = x_231;
goto block_230;
}
else
{
lean_dec(x_2);
x_224 = lean_box(0);
x_225 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_box(1);
if (x_225 == 0)
{
lean_ctor_set_tag(x_224, 0);
lean_ctor_set(x_224, 0, x_226);
x_227 = x_224;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_226);
x_227 = x_229;
goto block_228;
}
block_228:
{
return x_227;
}
}
}
}
case 15:
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_233 = lean_ctor_get(x_2, 0);
x_234 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_235 = 1;
lean_inc(x_233);
x_236 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_234, x_233, x_235);
lean_dec(x_234);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_245; 
x_237 = lean_ctor_get(x_236, 0);
x_245 = !lean_is_exclusive(x_236);
if (x_245 == 0)
{
x_238 = x_236;
x_239 = x_245;
goto block_244;
}
else
{
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_box(0);
x_239 = x_245;
goto block_244;
}
block_244:
{
lean_object* x_240; lean_object* x_241; 
x_240 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(x_1, x_2, x_237);
if (x_239 == 0)
{
lean_ctor_set(x_238, 0, x_240);
x_241 = x_238;
goto block_242;
}
else
{
lean_object* x_243; 
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_240);
x_241 = x_243;
goto block_242;
}
block_242:
{
return x_241;
}
}
}
else
{
lean_object* x_246; uint8_t x_247; uint8_t x_253; 
x_253 = !lean_is_exclusive(x_2);
if (x_253 == 0)
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_2, 0);
lean_dec(x_254);
x_246 = x_2;
x_247 = x_253;
goto block_252;
}
else
{
lean_dec(x_2);
x_246 = lean_box(0);
x_247 = x_253;
goto block_252;
}
block_252:
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_box(1);
if (x_247 == 0)
{
lean_ctor_set_tag(x_246, 0);
lean_ctor_set(x_246, 0, x_248);
x_249 = x_246;
goto block_250;
}
else
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_248);
x_249 = x_251;
goto block_250;
}
block_250:
{
return x_249;
}
}
}
}
default: 
{
lean_object* x_255; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_255 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_255, 0, x_2);
return x_255;
}
}
block_26:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_st_ref_get(x_11);
lean_dec(x_11);
x_13 = 1;
x_14 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_12, x_10, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_15 = lean_ctor_get(x_14, 0);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
x_16 = x_14;
x_17 = x_23;
goto block_22;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_1, x_2, x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
block_52:
{
lean_object* x_34; 
x_34 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_43; 
x_35 = lean_ctor_get(x_34, 0);
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
x_36 = x_34;
x_37 = x_43;
goto block_42;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_1, x_2, x_35);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_38);
x_39 = x_36;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_2);
x_44 = lean_ctor_get(x_34, 0);
x_51 = !lean_is_exclusive(x_34);
if (x_51 == 0)
{
x_45 = x_34;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_71; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_71 = !lean_is_exclusive(x_2);
if (x_71 == 0)
{
x_14 = x_2;
x_15 = x_71;
goto block_70;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(x_11, x_3, x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_18 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_20 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_45; 
x_23 = lean_ctor_get(x_22, 0);
x_45 = !lean_is_exclusive(x_22);
if (x_45 == 0)
{
x_24 = x_22;
x_25 = x_45;
goto block_44;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_43; 
x_26 = lean_st_ref_take(x_6);
x_27 = lean_ctor_get(x_26, 0);
x_28 = lean_ctor_get(x_26, 1);
x_43 = !lean_is_exclusive(x_26);
if (x_43 == 0)
{
x_29 = x_26;
x_30 = x_43;
goto block_42;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_31; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 3, x_21);
lean_ctor_set(x_14, 2, x_19);
lean_ctor_set(x_14, 1, x_17);
lean_ctor_set(x_14, 0, x_23);
x_31 = x_14;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_17);
lean_ctor_set(x_41, 2, x_19);
lean_ctor_set(x_41, 3, x_21);
x_31 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_32; lean_object* x_33; 
lean_inc_ref(x_31);
x_32 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_1, x_27, x_31);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_32);
x_33 = x_29;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_28);
x_33 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_st_ref_set(x_6, x_33);
lean_dec(x_6);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_31);
x_35 = x_24;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_31);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_del_object(x_14);
lean_dec(x_6);
x_46 = lean_ctor_get(x_22, 0);
x_53 = !lean_is_exclusive(x_22);
if (x_53 == 0)
{
x_47 = x_22;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_22);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_19);
lean_dec(x_17);
lean_del_object(x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_54 = lean_ctor_get(x_20, 0);
x_61 = !lean_is_exclusive(x_20);
if (x_61 == 0)
{
x_55 = x_20;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_20);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_17);
lean_del_object(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_62 = lean_ctor_get(x_18, 0);
x_69 = !lean_is_exclusive(x_18);
if (x_69 == 0)
{
x_63 = x_18;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_18);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget_borrowed(x_4, x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_15 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_4, x_3, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_18, x_3, x_16);
x_3 = x_20;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
x_23 = lean_ctor_get(x_15, 0);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
x_24 = x_15;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_12, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_46; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 2);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
x_26 = x_14;
x_27 = x_46;
goto block_45;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = x_46;
goto block_45;
}
block_45:
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = lean_array_size(x_24);
x_29 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_30 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_1, x_28, x_29, x_24, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_32 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_25, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
if (x_27 == 0)
{
lean_ctor_set(x_26, 2, x_33);
lean_ctor_set(x_26, 1, x_31);
x_34 = x_26;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
x_17 = x_34;
goto block_22;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_31);
lean_del_object(x_26);
lean_dec(x_23);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_37 = lean_ctor_get(x_32, 0);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
x_38 = x_32;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_del_object(x_26);
lean_dec_ref(x_25);
lean_dec(x_23);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_30;
}
}
}
case 1:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_65; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
x_65 = !lean_is_exclusive(x_14);
if (x_65 == 0)
{
x_49 = x_14;
x_50 = x_65;
goto block_64;
}
else
{
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_49 = lean_box(0);
x_50 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_51; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_51 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_48, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
if (x_50 == 0)
{
lean_ctor_set(x_49, 1, x_52);
x_53 = x_49;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
x_17 = x_53;
goto block_22;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_del_object(x_49);
lean_dec_ref(x_47);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_56 = lean_ctor_get(x_51, 0);
x_63 = !lean_is_exclusive(x_51);
if (x_63 == 0)
{
x_57 = x_51;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
default: 
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_83; 
x_66 = lean_ctor_get(x_14, 0);
x_83 = !lean_is_exclusive(x_14);
if (x_83 == 0)
{
x_67 = x_14;
x_68 = x_83;
goto block_82;
}
else
{
lean_inc(x_66);
lean_dec(x_14);
x_67 = lean_box(0);
x_68 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_69; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_69 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_66, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
if (x_68 == 0)
{
lean_ctor_set(x_67, 0, x_70);
x_71 = x_67;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_70);
x_71 = x_73;
goto block_72;
}
block_72:
{
x_17 = x_71;
goto block_22;
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_del_object(x_67);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_74 = lean_ctor_get(x_69, 0);
x_81 = !lean_is_exclusive(x_69);
if (x_81 == 0)
{
x_75 = x_69;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
}
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_16, x_3, x_17);
x_3 = x_19;
x_4 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_37; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
x_12 = x_2;
x_13 = x_37;
goto block_36;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_14; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_14 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_27; 
x_17 = lean_ctor_get(x_16, 0);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
x_18 = x_16;
x_19 = x_27;
goto block_26;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_20; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_17);
lean_ctor_set(x_12, 0, x_15);
x_20 = x_12;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_17);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_20);
x_21 = x_18;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_dec(x_15);
lean_del_object(x_12);
return x_16;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_del_object(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_28 = lean_ctor_get(x_14, 0);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
x_29 = x_14;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_65; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
x_65 = !lean_is_exclusive(x_2);
if (x_65 == 0)
{
x_40 = x_2;
x_41 = x_65;
goto block_64;
}
else
{
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_2);
x_40 = lean_box(0);
x_41 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_42; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_42 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_39, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_55; 
x_45 = lean_ctor_get(x_44, 0);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
x_46 = x_44;
x_47 = x_55;
goto block_54;
}
else
{
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_48; 
if (x_41 == 0)
{
lean_ctor_set(x_40, 1, x_45);
lean_ctor_set(x_40, 0, x_43);
x_48 = x_40;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_45);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_48);
x_49 = x_46;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
else
{
lean_dec(x_43);
lean_del_object(x_40);
return x_44;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_del_object(x_40);
lean_dec_ref(x_39);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_42, 0);
x_63 = !lean_is_exclusive(x_42);
if (x_63 == 0)
{
x_57 = x_42;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_42);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
case 2:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_93; 
x_66 = lean_ctor_get(x_2, 0);
x_67 = lean_ctor_get(x_2, 1);
x_93 = !lean_is_exclusive(x_2);
if (x_93 == 0)
{
x_68 = x_2;
x_69 = x_93;
goto block_92;
}
else
{
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_2);
x_68 = lean_box(0);
x_69 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_70; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_70 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_66, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_67, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_83; 
x_73 = lean_ctor_get(x_72, 0);
x_83 = !lean_is_exclusive(x_72);
if (x_83 == 0)
{
x_74 = x_72;
x_75 = x_83;
goto block_82;
}
else
{
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_76; 
if (x_69 == 0)
{
lean_ctor_set(x_68, 1, x_73);
lean_ctor_set(x_68, 0, x_71);
x_76 = x_68;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_73);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_76);
x_77 = x_74;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_76);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
else
{
lean_dec(x_71);
lean_del_object(x_68);
return x_72;
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_del_object(x_68);
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_84 = lean_ctor_get(x_70, 0);
x_91 = !lean_is_exclusive(x_70);
if (x_91 == 0)
{
x_85 = x_70;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_70);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
}
}
}
case 3:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_124; 
x_94 = lean_ctor_get(x_2, 0);
x_95 = lean_ctor_get(x_2, 1);
x_124 = !lean_is_exclusive(x_2);
if (x_124 == 0)
{
x_96 = x_2;
x_97 = x_124;
goto block_123;
}
else
{
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_2);
x_96 = lean_box(0);
x_97 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_98 = lean_st_ref_get(x_4);
x_99 = 1;
x_100 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_98, x_94, x_99);
lean_dec(x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_95, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_113; 
x_103 = lean_ctor_get(x_102, 0);
x_113 = !lean_is_exclusive(x_102);
if (x_113 == 0)
{
x_104 = x_102;
x_105 = x_113;
goto block_112;
}
else
{
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_box(0);
x_105 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_106; 
if (x_97 == 0)
{
lean_ctor_set(x_96, 1, x_103);
lean_ctor_set(x_96, 0, x_101);
x_106 = x_96;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_111, 0, x_101);
lean_ctor_set(x_111, 1, x_103);
x_106 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_107; 
if (x_105 == 0)
{
lean_ctor_set(x_104, 0, x_106);
x_107 = x_104;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_106);
x_107 = x_109;
goto block_108;
}
block_108:
{
return x_107;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_121; 
lean_dec(x_101);
lean_del_object(x_96);
x_114 = lean_ctor_get(x_102, 0);
x_121 = !lean_is_exclusive(x_102);
if (x_121 == 0)
{
x_115 = x_102;
x_116 = x_121;
goto block_120;
}
else
{
lean_inc(x_114);
lean_dec(x_102);
x_115 = lean_box(0);
x_116 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_117; 
if (x_116 == 0)
{
x_117 = x_115;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_114);
x_117 = x_119;
goto block_118;
}
block_118:
{
return x_117;
}
}
}
}
else
{
lean_object* x_122; 
lean_del_object(x_96);
lean_dec_ref(x_95);
lean_dec(x_4);
x_122 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_122;
}
}
}
case 4:
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_177; 
x_125 = lean_ctor_get(x_2, 0);
x_177 = !lean_is_exclusive(x_2);
if (x_177 == 0)
{
x_126 = x_2;
x_127 = x_177;
goto block_176;
}
else
{
lean_inc(x_125);
lean_dec(x_2);
x_126 = lean_box(0);
x_127 = x_177;
goto block_176;
}
block_176:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_175; 
x_128 = lean_ctor_get(x_125, 0);
x_129 = lean_ctor_get(x_125, 1);
x_130 = lean_ctor_get(x_125, 2);
x_131 = lean_ctor_get(x_125, 3);
x_175 = !lean_is_exclusive(x_125);
if (x_175 == 0)
{
x_132 = x_125;
x_133 = x_175;
goto block_174;
}
else
{
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_125);
x_132 = lean_box(0);
x_133 = x_175;
goto block_174;
}
block_174:
{
lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_134 = lean_st_ref_get(x_4);
x_135 = 1;
x_136 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_134, x_130, x_135);
lean_dec(x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_138 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_129, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; size_t x_140; size_t x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
x_140 = lean_array_size(x_131);
x_141 = 0;
x_142 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(x_1, x_140, x_141, x_131, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_156; 
x_143 = lean_ctor_get(x_142, 0);
x_156 = !lean_is_exclusive(x_142);
if (x_156 == 0)
{
x_144 = x_142;
x_145 = x_156;
goto block_155;
}
else
{
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_box(0);
x_145 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_146; 
if (x_133 == 0)
{
lean_ctor_set(x_132, 3, x_143);
lean_ctor_set(x_132, 2, x_137);
lean_ctor_set(x_132, 1, x_139);
x_146 = x_132;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_154, 0, x_128);
lean_ctor_set(x_154, 1, x_139);
lean_ctor_set(x_154, 2, x_137);
lean_ctor_set(x_154, 3, x_143);
x_146 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_147; 
if (x_127 == 0)
{
lean_ctor_set(x_126, 0, x_146);
x_147 = x_126;
goto block_151;
}
else
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_152, 0, x_146);
x_147 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_148; 
if (x_145 == 0)
{
lean_ctor_set(x_144, 0, x_147);
x_148 = x_144;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_147);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_164; 
lean_dec(x_139);
lean_dec(x_137);
lean_del_object(x_132);
lean_dec(x_128);
lean_del_object(x_126);
x_157 = lean_ctor_get(x_142, 0);
x_164 = !lean_is_exclusive(x_142);
if (x_164 == 0)
{
x_158 = x_142;
x_159 = x_164;
goto block_163;
}
else
{
lean_inc(x_157);
lean_dec(x_142);
x_158 = lean_box(0);
x_159 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_160; 
if (x_159 == 0)
{
x_160 = x_158;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_157);
x_160 = x_162;
goto block_161;
}
block_161:
{
return x_160;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_172; 
lean_dec(x_137);
lean_del_object(x_132);
lean_dec_ref(x_131);
lean_dec(x_128);
lean_del_object(x_126);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_165 = lean_ctor_get(x_138, 0);
x_172 = !lean_is_exclusive(x_138);
if (x_172 == 0)
{
x_166 = x_138;
x_167 = x_172;
goto block_171;
}
else
{
lean_inc(x_165);
lean_dec(x_138);
x_166 = lean_box(0);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_167 == 0)
{
x_168 = x_166;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_165);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
else
{
lean_object* x_173; 
lean_del_object(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_del_object(x_126);
lean_dec(x_4);
x_173 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_173;
}
}
}
}
case 5:
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_197; 
x_178 = lean_ctor_get(x_2, 0);
x_197 = !lean_is_exclusive(x_2);
if (x_197 == 0)
{
x_179 = x_2;
x_180 = x_197;
goto block_196;
}
else
{
lean_inc(x_178);
lean_dec(x_2);
x_179 = lean_box(0);
x_180 = x_197;
goto block_196;
}
block_196:
{
lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_181 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_182 = 1;
x_183 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_181, x_178, x_182);
lean_dec(x_181);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; uint8_t x_194; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_184 = lean_ctor_get(x_183, 0);
x_194 = !lean_is_exclusive(x_183);
if (x_194 == 0)
{
x_185 = x_183;
x_186 = x_194;
goto block_193;
}
else
{
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_box(0);
x_186 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_187; 
if (x_180 == 0)
{
lean_ctor_set(x_179, 0, x_184);
x_187 = x_179;
goto block_191;
}
else
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_192, 0, x_184);
x_187 = x_192;
goto block_191;
}
block_191:
{
lean_object* x_188; 
if (x_186 == 0)
{
lean_ctor_set(x_185, 0, x_187);
x_188 = x_185;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_187);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
}
}
else
{
lean_object* x_195; 
lean_del_object(x_179);
x_195 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_195;
}
}
}
case 6:
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_222; 
x_198 = lean_ctor_get(x_2, 0);
x_222 = !lean_is_exclusive(x_2);
if (x_222 == 0)
{
x_199 = x_2;
x_200 = x_222;
goto block_221;
}
else
{
lean_inc(x_198);
lean_dec(x_2);
x_199 = lean_box(0);
x_200 = x_222;
goto block_221;
}
block_221:
{
lean_object* x_201; 
x_201 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_198, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; uint8_t x_212; 
x_202 = lean_ctor_get(x_201, 0);
x_212 = !lean_is_exclusive(x_201);
if (x_212 == 0)
{
x_203 = x_201;
x_204 = x_212;
goto block_211;
}
else
{
lean_inc(x_202);
lean_dec(x_201);
x_203 = lean_box(0);
x_204 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_205; 
if (x_200 == 0)
{
lean_ctor_set(x_199, 0, x_202);
x_205 = x_199;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_210, 0, x_202);
x_205 = x_210;
goto block_209;
}
block_209:
{
lean_object* x_206; 
if (x_204 == 0)
{
lean_ctor_set(x_203, 0, x_205);
x_206 = x_203;
goto block_207;
}
else
{
lean_object* x_208; 
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_205);
x_206 = x_208;
goto block_207;
}
block_207:
{
return x_206;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_220; 
lean_del_object(x_199);
x_213 = lean_ctor_get(x_201, 0);
x_220 = !lean_is_exclusive(x_201);
if (x_220 == 0)
{
x_214 = x_201;
x_215 = x_220;
goto block_219;
}
else
{
lean_inc(x_213);
lean_dec(x_201);
x_214 = lean_box(0);
x_215 = x_220;
goto block_219;
}
block_219:
{
lean_object* x_216; 
if (x_215 == 0)
{
x_216 = x_214;
goto block_217;
}
else
{
lean_object* x_218; 
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_213);
x_216 = x_218;
goto block_217;
}
block_217:
{
return x_216;
}
}
}
}
}
case 7:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_249; 
x_223 = lean_ctor_get(x_2, 0);
x_224 = lean_ctor_get(x_2, 1);
x_225 = lean_ctor_get(x_2, 2);
x_226 = lean_ctor_get(x_2, 3);
x_249 = !lean_is_exclusive(x_2);
if (x_249 == 0)
{
x_227 = x_2;
x_228 = x_249;
goto block_248;
}
else
{
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_2);
x_227 = lean_box(0);
x_228 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_229; uint8_t x_230; lean_object* x_231; 
x_229 = lean_st_ref_get(x_4);
x_230 = 1;
x_231 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_229, x_223, x_230);
lean_dec(x_229);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
x_233 = lean_st_ref_get(x_4);
x_234 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_1, x_233, x_225, x_230);
lean_dec(x_233);
x_235 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_226, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; uint8_t x_246; 
x_236 = lean_ctor_get(x_235, 0);
x_246 = !lean_is_exclusive(x_235);
if (x_246 == 0)
{
x_237 = x_235;
x_238 = x_246;
goto block_245;
}
else
{
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_box(0);
x_238 = x_246;
goto block_245;
}
block_245:
{
lean_object* x_239; 
if (x_228 == 0)
{
lean_ctor_set(x_227, 3, x_236);
lean_ctor_set(x_227, 2, x_234);
lean_ctor_set(x_227, 0, x_232);
x_239 = x_227;
goto block_243;
}
else
{
lean_object* x_244; 
x_244 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_244, 0, x_232);
lean_ctor_set(x_244, 1, x_224);
lean_ctor_set(x_244, 2, x_234);
lean_ctor_set(x_244, 3, x_236);
x_239 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_240; 
if (x_238 == 0)
{
lean_ctor_set(x_237, 0, x_239);
x_240 = x_237;
goto block_241;
}
else
{
lean_object* x_242; 
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_239);
x_240 = x_242;
goto block_241;
}
block_241:
{
return x_240;
}
}
}
}
else
{
lean_dec(x_234);
lean_dec(x_232);
lean_del_object(x_227);
lean_dec(x_224);
return x_235;
}
}
else
{
lean_object* x_247; 
lean_del_object(x_227);
lean_dec_ref(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_4);
x_247 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_247;
}
}
}
case 8:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; uint8_t x_278; 
x_250 = lean_ctor_get(x_2, 0);
x_251 = lean_ctor_get(x_2, 1);
x_252 = lean_ctor_get(x_2, 2);
x_253 = lean_ctor_get(x_2, 3);
x_278 = !lean_is_exclusive(x_2);
if (x_278 == 0)
{
x_254 = x_2;
x_255 = x_278;
goto block_277;
}
else
{
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_2);
x_254 = lean_box(0);
x_255 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_256; uint8_t x_257; lean_object* x_258; 
x_256 = lean_st_ref_get(x_4);
x_257 = 1;
x_258 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_256, x_250, x_257);
lean_dec(x_256);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
x_260 = lean_st_ref_get(x_4);
x_261 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_260, x_252, x_257);
lean_dec(x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
x_263 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_253, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_274; 
x_264 = lean_ctor_get(x_263, 0);
x_274 = !lean_is_exclusive(x_263);
if (x_274 == 0)
{
x_265 = x_263;
x_266 = x_274;
goto block_273;
}
else
{
lean_inc(x_264);
lean_dec(x_263);
x_265 = lean_box(0);
x_266 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_267; 
if (x_255 == 0)
{
lean_ctor_set(x_254, 3, x_264);
lean_ctor_set(x_254, 2, x_262);
lean_ctor_set(x_254, 0, x_259);
x_267 = x_254;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_272, 0, x_259);
lean_ctor_set(x_272, 1, x_251);
lean_ctor_set(x_272, 2, x_262);
lean_ctor_set(x_272, 3, x_264);
x_267 = x_272;
goto block_271;
}
block_271:
{
lean_object* x_268; 
if (x_266 == 0)
{
lean_ctor_set(x_265, 0, x_267);
x_268 = x_265;
goto block_269;
}
else
{
lean_object* x_270; 
x_270 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_270, 0, x_267);
x_268 = x_270;
goto block_269;
}
block_269:
{
return x_268;
}
}
}
}
else
{
lean_dec(x_262);
lean_dec(x_259);
lean_del_object(x_254);
lean_dec(x_251);
return x_263;
}
}
else
{
lean_object* x_275; 
lean_dec(x_259);
lean_del_object(x_254);
lean_dec_ref(x_253);
lean_dec(x_251);
lean_dec(x_4);
x_275 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_275;
}
}
else
{
lean_object* x_276; 
lean_del_object(x_254);
lean_dec_ref(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_4);
x_276 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_276;
}
}
}
case 9:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; uint8_t x_319; 
x_279 = lean_ctor_get(x_2, 0);
x_280 = lean_ctor_get(x_2, 1);
x_281 = lean_ctor_get(x_2, 2);
x_282 = lean_ctor_get(x_2, 3);
x_283 = lean_ctor_get(x_2, 4);
x_284 = lean_ctor_get(x_2, 5);
x_319 = !lean_is_exclusive(x_2);
if (x_319 == 0)
{
x_285 = x_2;
x_286 = x_319;
goto block_318;
}
else
{
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_2);
x_285 = lean_box(0);
x_286 = x_319;
goto block_318;
}
block_318:
{
lean_object* x_287; uint8_t x_288; lean_object* x_289; 
x_287 = lean_st_ref_get(x_4);
x_288 = 1;
x_289 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_287, x_279, x_288);
lean_dec(x_287);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
x_291 = lean_st_ref_get(x_4);
x_292 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_291, x_282, x_288);
lean_dec(x_291);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec_ref(x_292);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_294 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_283, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec_ref(x_294);
x_296 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_284, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; uint8_t x_307; 
x_297 = lean_ctor_get(x_296, 0);
x_307 = !lean_is_exclusive(x_296);
if (x_307 == 0)
{
x_298 = x_296;
x_299 = x_307;
goto block_306;
}
else
{
lean_inc(x_297);
lean_dec(x_296);
x_298 = lean_box(0);
x_299 = x_307;
goto block_306;
}
block_306:
{
lean_object* x_300; 
if (x_286 == 0)
{
lean_ctor_set(x_285, 5, x_297);
lean_ctor_set(x_285, 4, x_295);
lean_ctor_set(x_285, 3, x_293);
lean_ctor_set(x_285, 0, x_290);
x_300 = x_285;
goto block_304;
}
else
{
lean_object* x_305; 
x_305 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_305, 0, x_290);
lean_ctor_set(x_305, 1, x_280);
lean_ctor_set(x_305, 2, x_281);
lean_ctor_set(x_305, 3, x_293);
lean_ctor_set(x_305, 4, x_295);
lean_ctor_set(x_305, 5, x_297);
x_300 = x_305;
goto block_304;
}
block_304:
{
lean_object* x_301; 
if (x_299 == 0)
{
lean_ctor_set(x_298, 0, x_300);
x_301 = x_298;
goto block_302;
}
else
{
lean_object* x_303; 
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_300);
x_301 = x_303;
goto block_302;
}
block_302:
{
return x_301;
}
}
}
}
else
{
lean_dec(x_295);
lean_dec(x_293);
lean_dec(x_290);
lean_del_object(x_285);
lean_dec(x_281);
lean_dec(x_280);
return x_296;
}
}
else
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_315; 
lean_dec(x_293);
lean_dec(x_290);
lean_del_object(x_285);
lean_dec_ref(x_284);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_308 = lean_ctor_get(x_294, 0);
x_315 = !lean_is_exclusive(x_294);
if (x_315 == 0)
{
x_309 = x_294;
x_310 = x_315;
goto block_314;
}
else
{
lean_inc(x_308);
lean_dec(x_294);
x_309 = lean_box(0);
x_310 = x_315;
goto block_314;
}
block_314:
{
lean_object* x_311; 
if (x_310 == 0)
{
x_311 = x_309;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_308);
x_311 = x_313;
goto block_312;
}
block_312:
{
return x_311;
}
}
}
}
else
{
lean_object* x_316; 
lean_dec(x_290);
lean_del_object(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_4);
x_316 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_316;
}
}
else
{
lean_object* x_317; 
lean_del_object(x_285);
lean_dec_ref(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_4);
x_317 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_317;
}
}
}
case 10:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; uint8_t x_343; 
x_320 = lean_ctor_get(x_2, 0);
x_321 = lean_ctor_get(x_2, 1);
x_322 = lean_ctor_get(x_2, 2);
x_343 = !lean_is_exclusive(x_2);
if (x_343 == 0)
{
x_323 = x_2;
x_324 = x_343;
goto block_342;
}
else
{
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_2);
x_323 = lean_box(0);
x_324 = x_343;
goto block_342;
}
block_342:
{
lean_object* x_325; uint8_t x_326; lean_object* x_327; 
x_325 = lean_st_ref_get(x_4);
x_326 = 1;
x_327 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_325, x_320, x_326);
lean_dec(x_325);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
lean_dec_ref(x_327);
x_329 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_322, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; uint8_t x_332; uint8_t x_340; 
x_330 = lean_ctor_get(x_329, 0);
x_340 = !lean_is_exclusive(x_329);
if (x_340 == 0)
{
x_331 = x_329;
x_332 = x_340;
goto block_339;
}
else
{
lean_inc(x_330);
lean_dec(x_329);
x_331 = lean_box(0);
x_332 = x_340;
goto block_339;
}
block_339:
{
lean_object* x_333; 
if (x_324 == 0)
{
lean_ctor_set(x_323, 2, x_330);
lean_ctor_set(x_323, 0, x_328);
x_333 = x_323;
goto block_337;
}
else
{
lean_object* x_338; 
x_338 = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(x_338, 0, x_328);
lean_ctor_set(x_338, 1, x_321);
lean_ctor_set(x_338, 2, x_330);
x_333 = x_338;
goto block_337;
}
block_337:
{
lean_object* x_334; 
if (x_332 == 0)
{
lean_ctor_set(x_331, 0, x_333);
x_334 = x_331;
goto block_335;
}
else
{
lean_object* x_336; 
x_336 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_336, 0, x_333);
x_334 = x_336;
goto block_335;
}
block_335:
{
return x_334;
}
}
}
}
else
{
lean_dec(x_328);
lean_del_object(x_323);
lean_dec(x_321);
return x_329;
}
}
else
{
lean_object* x_341; 
lean_del_object(x_323);
lean_dec_ref(x_322);
lean_dec(x_321);
lean_dec(x_4);
x_341 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_341;
}
}
}
case 11:
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; uint8_t x_369; 
x_344 = lean_ctor_get(x_2, 0);
x_345 = lean_ctor_get(x_2, 1);
x_346 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_347 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_348 = lean_ctor_get(x_2, 2);
x_369 = !lean_is_exclusive(x_2);
if (x_369 == 0)
{
x_349 = x_2;
x_350 = x_369;
goto block_368;
}
else
{
lean_inc(x_348);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_2);
x_349 = lean_box(0);
x_350 = x_369;
goto block_368;
}
block_368:
{
lean_object* x_351; uint8_t x_352; lean_object* x_353; 
x_351 = lean_st_ref_get(x_4);
x_352 = 1;
x_353 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_351, x_344, x_352);
lean_dec(x_351);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
lean_dec_ref(x_353);
x_355 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_348, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; uint8_t x_358; uint8_t x_366; 
x_356 = lean_ctor_get(x_355, 0);
x_366 = !lean_is_exclusive(x_355);
if (x_366 == 0)
{
x_357 = x_355;
x_358 = x_366;
goto block_365;
}
else
{
lean_inc(x_356);
lean_dec(x_355);
x_357 = lean_box(0);
x_358 = x_366;
goto block_365;
}
block_365:
{
lean_object* x_359; 
if (x_350 == 0)
{
lean_ctor_set(x_349, 2, x_356);
lean_ctor_set(x_349, 0, x_354);
x_359 = x_349;
goto block_363;
}
else
{
lean_object* x_364; 
x_364 = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(x_364, 0, x_354);
lean_ctor_set(x_364, 1, x_345);
lean_ctor_set(x_364, 2, x_356);
lean_ctor_set_uint8(x_364, sizeof(void*)*3, x_346);
lean_ctor_set_uint8(x_364, sizeof(void*)*3 + 1, x_347);
x_359 = x_364;
goto block_363;
}
block_363:
{
lean_object* x_360; 
if (x_358 == 0)
{
lean_ctor_set(x_357, 0, x_359);
x_360 = x_357;
goto block_361;
}
else
{
lean_object* x_362; 
x_362 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_362, 0, x_359);
x_360 = x_362;
goto block_361;
}
block_361:
{
return x_360;
}
}
}
}
else
{
lean_dec(x_354);
lean_del_object(x_349);
lean_dec(x_345);
return x_355;
}
}
else
{
lean_object* x_367; 
lean_del_object(x_349);
lean_dec_ref(x_348);
lean_dec(x_345);
lean_dec(x_4);
x_367 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_367;
}
}
}
case 12:
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; uint8_t x_395; 
x_370 = lean_ctor_get(x_2, 0);
x_371 = lean_ctor_get(x_2, 1);
x_372 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_373 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_374 = lean_ctor_get(x_2, 2);
x_395 = !lean_is_exclusive(x_2);
if (x_395 == 0)
{
x_375 = x_2;
x_376 = x_395;
goto block_394;
}
else
{
lean_inc(x_374);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_2);
x_375 = lean_box(0);
x_376 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_377; uint8_t x_378; lean_object* x_379; 
x_377 = lean_st_ref_get(x_4);
x_378 = 1;
x_379 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_377, x_370, x_378);
lean_dec(x_377);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
lean_dec_ref(x_379);
x_381 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_374, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; uint8_t x_392; 
x_382 = lean_ctor_get(x_381, 0);
x_392 = !lean_is_exclusive(x_381);
if (x_392 == 0)
{
x_383 = x_381;
x_384 = x_392;
goto block_391;
}
else
{
lean_inc(x_382);
lean_dec(x_381);
x_383 = lean_box(0);
x_384 = x_392;
goto block_391;
}
block_391:
{
lean_object* x_385; 
if (x_376 == 0)
{
lean_ctor_set(x_375, 2, x_382);
lean_ctor_set(x_375, 0, x_380);
x_385 = x_375;
goto block_389;
}
else
{
lean_object* x_390; 
x_390 = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(x_390, 0, x_380);
lean_ctor_set(x_390, 1, x_371);
lean_ctor_set(x_390, 2, x_382);
lean_ctor_set_uint8(x_390, sizeof(void*)*3, x_372);
lean_ctor_set_uint8(x_390, sizeof(void*)*3 + 1, x_373);
x_385 = x_390;
goto block_389;
}
block_389:
{
lean_object* x_386; 
if (x_384 == 0)
{
lean_ctor_set(x_383, 0, x_385);
x_386 = x_383;
goto block_387;
}
else
{
lean_object* x_388; 
x_388 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_388, 0, x_385);
x_386 = x_388;
goto block_387;
}
block_387:
{
return x_386;
}
}
}
}
else
{
lean_dec(x_380);
lean_del_object(x_375);
lean_dec(x_371);
return x_381;
}
}
else
{
lean_object* x_393; 
lean_del_object(x_375);
lean_dec_ref(x_374);
lean_dec(x_371);
lean_dec(x_4);
x_393 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_393;
}
}
}
default: 
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; uint8_t x_418; 
x_396 = lean_ctor_get(x_2, 0);
x_397 = lean_ctor_get(x_2, 1);
x_418 = !lean_is_exclusive(x_2);
if (x_418 == 0)
{
x_398 = x_2;
x_399 = x_418;
goto block_417;
}
else
{
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_2);
x_398 = lean_box(0);
x_399 = x_418;
goto block_417;
}
block_417:
{
lean_object* x_400; uint8_t x_401; lean_object* x_402; 
x_400 = lean_st_ref_get(x_4);
x_401 = 1;
x_402 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_400, x_396, x_401);
lean_dec(x_400);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec_ref(x_402);
x_404 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_397, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; uint8_t x_407; uint8_t x_415; 
x_405 = lean_ctor_get(x_404, 0);
x_415 = !lean_is_exclusive(x_404);
if (x_415 == 0)
{
x_406 = x_404;
x_407 = x_415;
goto block_414;
}
else
{
lean_inc(x_405);
lean_dec(x_404);
x_406 = lean_box(0);
x_407 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_408; 
if (x_399 == 0)
{
lean_ctor_set(x_398, 1, x_405);
lean_ctor_set(x_398, 0, x_403);
x_408 = x_398;
goto block_412;
}
else
{
lean_object* x_413; 
x_413 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_413, 0, x_403);
lean_ctor_set(x_413, 1, x_405);
x_408 = x_413;
goto block_412;
}
block_412:
{
lean_object* x_409; 
if (x_407 == 0)
{
lean_ctor_set(x_406, 0, x_408);
x_409 = x_406;
goto block_410;
}
else
{
lean_object* x_411; 
x_411 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_411, 0, x_408);
x_409 = x_411;
goto block_410;
}
block_410:
{
return x_409;
}
}
}
}
else
{
lean_dec(x_403);
lean_del_object(x_398);
return x_404;
}
}
else
{
lean_object* x_416; 
lean_del_object(x_398);
lean_dec_ref(x_397);
lean_dec(x_4);
x_416 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_416;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_92; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = lean_ctor_get(x_2, 4);
x_92 = !lean_is_exclusive(x_2);
if (x_92 == 0)
{
x_15 = x_2;
x_16 = x_92;
goto block_91;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_17; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_17 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_refreshBinderName___redArg(x_11, x_3, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_array_size(x_12);
x_22 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_23 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_1, x_21, x_22, x_12, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_25 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_50; 
x_28 = lean_ctor_get(x_27, 0);
x_50 = !lean_is_exclusive(x_27);
if (x_50 == 0)
{
x_29 = x_27;
x_30 = x_50;
goto block_49;
}
else
{
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_48; 
x_31 = lean_st_ref_take(x_6);
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_31, 1);
x_48 = !lean_is_exclusive(x_31);
if (x_48 == 0)
{
x_34 = x_31;
x_35 = x_48;
goto block_47;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_36; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 4, x_26);
lean_ctor_set(x_15, 3, x_18);
lean_ctor_set(x_15, 2, x_24);
lean_ctor_set(x_15, 1, x_20);
lean_ctor_set(x_15, 0, x_28);
x_36 = x_15;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_28);
lean_ctor_set(x_46, 1, x_20);
lean_ctor_set(x_46, 2, x_24);
lean_ctor_set(x_46, 3, x_18);
lean_ctor_set(x_46, 4, x_26);
x_36 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_37; lean_object* x_38; 
lean_inc_ref(x_36);
x_37 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_1, x_32, x_36);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_37);
x_38 = x_34;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_33);
x_38 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_st_ref_set(x_6, x_38);
lean_dec(x_6);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_36);
x_40 = x_29;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_36);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_18);
lean_del_object(x_15);
lean_dec(x_6);
x_51 = lean_ctor_get(x_27, 0);
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
x_52 = x_27;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_27);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_18);
lean_del_object(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_59 = lean_ctor_get(x_25, 0);
x_66 = !lean_is_exclusive(x_25);
if (x_66 == 0)
{
x_60 = x_25;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_25);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec(x_20);
lean_dec(x_18);
lean_del_object(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_67 = lean_ctor_get(x_23, 0);
x_74 = !lean_is_exclusive(x_23);
if (x_74 == 0)
{
x_68 = x_23;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_23);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_dec(x_18);
lean_del_object(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_75 = lean_ctor_get(x_19, 0);
x_82 = !lean_is_exclusive(x_19);
if (x_82 == 0)
{
x_76 = x_19;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_19);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
lean_del_object(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_83 = lean_ctor_get(x_17, 0);
x_90 = !lean_is_exclusive(x_17);
if (x_90 == 0)
{
x_84 = x_17;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_17);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
return x_86;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(x_12, x_13, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_76; 
x_10 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
x_11 = l_ReaderT_instMonad___redArg(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_11, 1);
lean_dec(x_77);
x_13 = x_11;
x_14 = x_76;
goto block_75;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_73; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_12, 1);
lean_dec(x_74);
x_19 = x_12;
x_20 = x_73;
goto block_72;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
x_22 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_17);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_16);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_26);
lean_ctor_set(x_19, 3, x_27);
lean_ctor_set(x_19, 2, x_28);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_25);
x_29 = x_19;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_25);
lean_ctor_set(x_71, 1, x_21);
lean_ctor_set(x_71, 2, x_28);
lean_ctor_set(x_71, 3, x_27);
lean_ctor_set(x_71, 4, x_26);
x_29 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_30; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_29);
x_30 = x_13;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_29);
lean_ctor_set(x_69, 1, x_22);
x_30 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_66; 
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = lean_ctor_get(x_31, 0);
x_66 = !lean_is_exclusive(x_31);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_31, 1);
lean_dec(x_67);
x_33 = x_31;
x_34 = x_66;
goto block_65;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_63; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_32, 1);
lean_dec(x_64);
x_39 = x_32;
x_40 = x_63;
goto block_62;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_39 = lean_box(0);
x_40 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_42 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_37);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_36);
if (x_40 == 0)
{
lean_ctor_set(x_39, 4, x_46);
lean_ctor_set(x_39, 3, x_47);
lean_ctor_set(x_39, 2, x_48);
lean_ctor_set(x_39, 1, x_41);
lean_ctor_set(x_39, 0, x_45);
x_49 = x_39;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_45);
lean_ctor_set(x_61, 1, x_41);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_47);
lean_ctor_set(x_61, 4, x_46);
x_49 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_50; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_49);
x_50 = x_33;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_42);
x_50 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(x_1);
x_53 = l_instInhabitedOfMonad___redArg(x_51, x_52);
x_54 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = lean_panic_fn(x_54, x_2);
x_56 = lean_box(x_3);
x_57 = lean_apply_7(x_55, x_56, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_57;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(218u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_unsigned_to_nat(223u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(222u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_unsigned_to_nat(227u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(226u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(231u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(234u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(237u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(240u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_34; 
x_10 = lean_ctor_get(x_2, 0);
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
x_11 = x_2;
x_12 = x_34;
goto block_33;
}
else
{
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_24; 
x_14 = lean_ctor_get(x_13, 0);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
x_15 = x_13;
x_16 = x_24;
goto block_23;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_17; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_14);
x_17 = x_11;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_14);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_17);
x_18 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_del_object(x_11);
x_25 = lean_ctor_get(x_13, 0);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
x_26 = x_13;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
case 1:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_59; 
x_35 = lean_ctor_get(x_2, 0);
x_59 = !lean_is_exclusive(x_2);
if (x_59 == 0)
{
x_36 = x_2;
x_37 = x_59;
goto block_58;
}
else
{
lean_inc(x_35);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_38; 
x_38 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_35, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_49; 
x_39 = lean_ctor_get(x_38, 0);
x_49 = !lean_is_exclusive(x_38);
if (x_49 == 0)
{
x_40 = x_38;
x_41 = x_49;
goto block_48;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_42; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_39);
x_42 = x_36;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_39);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_42);
x_43 = x_40;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_del_object(x_36);
x_50 = lean_ctor_get(x_38, 0);
x_57 = !lean_is_exclusive(x_38);
if (x_57 == 0)
{
x_51 = x_38;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_38);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
case 2:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_84; 
x_60 = lean_ctor_get(x_2, 0);
x_84 = !lean_is_exclusive(x_2);
if (x_84 == 0)
{
x_61 = x_2;
x_62 = x_84;
goto block_83;
}
else
{
lean_inc(x_60);
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_63; 
x_63 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_60, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_74; 
x_64 = lean_ctor_get(x_63, 0);
x_74 = !lean_is_exclusive(x_63);
if (x_74 == 0)
{
x_65 = x_63;
x_66 = x_74;
goto block_73;
}
else
{
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_67; 
if (x_62 == 0)
{
lean_ctor_set(x_61, 0, x_64);
x_67 = x_61;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_64);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_67);
x_68 = x_65;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
lean_del_object(x_61);
x_75 = lean_ctor_get(x_63, 0);
x_82 = !lean_is_exclusive(x_63);
if (x_82 == 0)
{
x_76 = x_63;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_63);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
case 3:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_109; 
x_85 = lean_ctor_get(x_2, 0);
x_86 = lean_ctor_get(x_2, 1);
x_87 = lean_ctor_get(x_2, 2);
x_109 = !lean_is_exclusive(x_2);
if (x_109 == 0)
{
x_88 = x_2;
x_89 = x_109;
goto block_108;
}
else
{
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_2);
x_88 = lean_box(0);
x_89 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_90 = lean_st_ref_get(x_4);
x_91 = 1;
x_92 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_90, x_85, x_91);
lean_dec(x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_105; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_93 = lean_ctor_get(x_92, 0);
x_105 = !lean_is_exclusive(x_92);
if (x_105 == 0)
{
x_94 = x_92;
x_95 = x_105;
goto block_104;
}
else
{
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_box(0);
x_95 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_97 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_1, x_96, x_87, x_91);
lean_dec(x_96);
if (x_89 == 0)
{
lean_ctor_set(x_88, 2, x_97);
lean_ctor_set(x_88, 0, x_93);
x_98 = x_88;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_86);
lean_ctor_set(x_103, 2, x_97);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_95 == 0)
{
lean_ctor_set(x_94, 0, x_98);
x_99 = x_94;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_98);
x_99 = x_101;
goto block_100;
}
block_100:
{
return x_99;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_92);
lean_del_object(x_88);
lean_dec(x_87);
lean_dec(x_86);
x_106 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
x_107 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_106, x_3, x_4, x_5, x_6, x_7, x_8);
return x_107;
}
}
}
case 4:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_137; 
x_110 = lean_ctor_get(x_2, 0);
x_111 = lean_ctor_get(x_2, 1);
x_112 = lean_ctor_get(x_2, 2);
x_137 = !lean_is_exclusive(x_2);
if (x_137 == 0)
{
x_113 = x_2;
x_114 = x_137;
goto block_136;
}
else
{
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_2);
x_113 = lean_box(0);
x_114 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; 
x_115 = lean_st_ref_get(x_4);
x_116 = 1;
x_117 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_115, x_110, x_116);
lean_dec(x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_st_ref_get(x_4);
x_120 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_119, x_112, x_116);
lean_dec(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_131; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_121 = lean_ctor_get(x_120, 0);
x_131 = !lean_is_exclusive(x_120);
if (x_131 == 0)
{
x_122 = x_120;
x_123 = x_131;
goto block_130;
}
else
{
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_box(0);
x_123 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_124; 
if (x_114 == 0)
{
lean_ctor_set(x_113, 2, x_121);
lean_ctor_set(x_113, 0, x_118);
x_124 = x_113;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_129, 0, x_118);
lean_ctor_set(x_129, 1, x_111);
lean_ctor_set(x_129, 2, x_121);
x_124 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_125; 
if (x_123 == 0)
{
lean_ctor_set(x_122, 0, x_124);
x_125 = x_122;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_124);
x_125 = x_127;
goto block_126;
}
block_126:
{
return x_125;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_120);
lean_dec(x_118);
lean_del_object(x_113);
lean_dec(x_111);
x_132 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
x_133 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_132, x_3, x_4, x_5, x_6, x_7, x_8);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_117);
lean_del_object(x_113);
lean_dec(x_112);
lean_dec(x_111);
x_134 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
x_135 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_134, x_3, x_4, x_5, x_6, x_7, x_8);
return x_135;
}
}
}
case 5:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_169; 
x_138 = lean_ctor_get(x_2, 0);
x_139 = lean_ctor_get(x_2, 1);
x_140 = lean_ctor_get(x_2, 2);
x_141 = lean_ctor_get(x_2, 3);
x_142 = lean_ctor_get(x_2, 4);
x_169 = !lean_is_exclusive(x_2);
if (x_169 == 0)
{
x_143 = x_2;
x_144 = x_169;
goto block_168;
}
else
{
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_2);
x_143 = lean_box(0);
x_144 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_145 = lean_st_ref_get(x_4);
x_146 = 1;
x_147 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_145, x_138, x_146);
lean_dec(x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = lean_st_ref_get(x_4);
x_150 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_149, x_141, x_146);
lean_dec(x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_163; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_151 = lean_ctor_get(x_150, 0);
x_163 = !lean_is_exclusive(x_150);
if (x_163 == 0)
{
x_152 = x_150;
x_153 = x_163;
goto block_162;
}
else
{
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_box(0);
x_153 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_st_ref_get(x_4);
lean_dec(x_4);
x_155 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1, x_154, x_146, x_142);
lean_dec(x_154);
if (x_144 == 0)
{
lean_ctor_set(x_143, 4, x_155);
lean_ctor_set(x_143, 3, x_151);
lean_ctor_set(x_143, 0, x_148);
x_156 = x_143;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_161, 0, x_148);
lean_ctor_set(x_161, 1, x_139);
lean_ctor_set(x_161, 2, x_140);
lean_ctor_set(x_161, 3, x_151);
lean_ctor_set(x_161, 4, x_155);
x_156 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_157; 
if (x_153 == 0)
{
lean_ctor_set(x_152, 0, x_156);
x_157 = x_152;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_156);
x_157 = x_159;
goto block_158;
}
block_158:
{
return x_157;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_150);
lean_dec(x_148);
lean_del_object(x_143);
lean_dec_ref(x_142);
lean_dec(x_140);
lean_dec(x_139);
x_164 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
x_165 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_164, x_3, x_4, x_5, x_6, x_7, x_8);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_147);
lean_del_object(x_143);
lean_dec_ref(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
x_166 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
x_167 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_166, x_3, x_4, x_5, x_6, x_7, x_8);
return x_167;
}
}
}
case 6:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_191; 
x_170 = lean_ctor_get(x_2, 0);
x_171 = lean_ctor_get(x_2, 1);
x_191 = !lean_is_exclusive(x_2);
if (x_191 == 0)
{
x_172 = x_2;
x_173 = x_191;
goto block_190;
}
else
{
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_2);
x_172 = lean_box(0);
x_173 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_174; uint8_t x_175; lean_object* x_176; 
x_174 = lean_st_ref_get(x_4);
x_175 = 1;
x_176 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_174, x_170, x_175);
lean_dec(x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_187; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_177 = lean_ctor_get(x_176, 0);
x_187 = !lean_is_exclusive(x_176);
if (x_187 == 0)
{
x_178 = x_176;
x_179 = x_187;
goto block_186;
}
else
{
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_box(0);
x_179 = x_187;
goto block_186;
}
block_186:
{
lean_object* x_180; 
if (x_173 == 0)
{
lean_ctor_set(x_172, 0, x_177);
x_180 = x_172;
goto block_184;
}
else
{
lean_object* x_185; 
x_185 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_185, 0, x_177);
lean_ctor_set(x_185, 1, x_171);
x_180 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_181; 
if (x_179 == 0)
{
lean_ctor_set(x_178, 0, x_180);
x_181 = x_178;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_180);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_176);
lean_del_object(x_172);
lean_dec(x_171);
x_188 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
x_189 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_188, x_3, x_4, x_5, x_6, x_7, x_8);
return x_189;
}
}
}
case 7:
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_195; lean_object* x_196; uint8_t x_197; uint8_t x_215; 
x_192 = lean_ctor_get(x_2, 0);
x_193 = lean_ctor_get(x_2, 1);
x_194 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_195 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_215 = !lean_is_exclusive(x_2);
if (x_215 == 0)
{
x_196 = x_2;
x_197 = x_215;
goto block_214;
}
else
{
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_2);
x_196 = lean_box(0);
x_197 = x_215;
goto block_214;
}
block_214:
{
lean_object* x_198; uint8_t x_199; lean_object* x_200; 
x_198 = lean_st_ref_get(x_4);
x_199 = 1;
x_200 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_198, x_192, x_199);
lean_dec(x_198);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_211; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_201 = lean_ctor_get(x_200, 0);
x_211 = !lean_is_exclusive(x_200);
if (x_211 == 0)
{
x_202 = x_200;
x_203 = x_211;
goto block_210;
}
else
{
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_box(0);
x_203 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_204; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 0, x_201);
x_204 = x_196;
goto block_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(x_209, 0, x_201);
lean_ctor_set(x_209, 1, x_193);
lean_ctor_set_uint8(x_209, sizeof(void*)*2, x_194);
lean_ctor_set_uint8(x_209, sizeof(void*)*2 + 1, x_195);
x_204 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_205; 
if (x_203 == 0)
{
lean_ctor_set(x_202, 0, x_204);
x_205 = x_202;
goto block_206;
}
else
{
lean_object* x_207; 
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_204);
x_205 = x_207;
goto block_206;
}
block_206:
{
return x_205;
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_200);
lean_del_object(x_196);
lean_dec(x_193);
x_212 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
x_213 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_212, x_3, x_4, x_5, x_6, x_7, x_8);
return x_213;
}
}
}
case 8:
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; uint8_t x_219; lean_object* x_220; uint8_t x_221; uint8_t x_239; 
x_216 = lean_ctor_get(x_2, 0);
x_217 = lean_ctor_get(x_2, 1);
x_218 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_219 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_239 = !lean_is_exclusive(x_2);
if (x_239 == 0)
{
x_220 = x_2;
x_221 = x_239;
goto block_238;
}
else
{
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_2);
x_220 = lean_box(0);
x_221 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_222 = lean_st_ref_get(x_4);
x_223 = 1;
x_224 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_222, x_216, x_223);
lean_dec(x_222);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_235; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_225 = lean_ctor_get(x_224, 0);
x_235 = !lean_is_exclusive(x_224);
if (x_235 == 0)
{
x_226 = x_224;
x_227 = x_235;
goto block_234;
}
else
{
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_box(0);
x_227 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_228; 
if (x_221 == 0)
{
lean_ctor_set(x_220, 0, x_225);
x_228 = x_220;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(8, 2, 2);
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_217);
lean_ctor_set_uint8(x_233, sizeof(void*)*2, x_218);
lean_ctor_set_uint8(x_233, sizeof(void*)*2 + 1, x_219);
x_228 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_229; 
if (x_227 == 0)
{
lean_ctor_set(x_226, 0, x_228);
x_229 = x_226;
goto block_230;
}
else
{
lean_object* x_231; 
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_228);
x_229 = x_231;
goto block_230;
}
block_230:
{
return x_229;
}
}
}
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_224);
lean_del_object(x_220);
lean_dec(x_217);
x_236 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
x_237 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_236, x_3, x_4, x_5, x_6, x_7, x_8);
return x_237;
}
}
}
default: 
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_260; 
x_240 = lean_ctor_get(x_2, 0);
x_260 = !lean_is_exclusive(x_2);
if (x_260 == 0)
{
x_241 = x_2;
x_242 = x_260;
goto block_259;
}
else
{
lean_inc(x_240);
lean_dec(x_2);
x_241 = lean_box(0);
x_242 = x_260;
goto block_259;
}
block_259:
{
lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_243 = lean_st_ref_get(x_4);
x_244 = 1;
x_245 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_243, x_240, x_244);
lean_dec(x_243);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; uint8_t x_256; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_246 = lean_ctor_get(x_245, 0);
x_256 = !lean_is_exclusive(x_245);
if (x_256 == 0)
{
x_247 = x_245;
x_248 = x_256;
goto block_255;
}
else
{
lean_inc(x_246);
lean_dec(x_245);
x_247 = lean_box(0);
x_248 = x_256;
goto block_255;
}
block_255:
{
lean_object* x_249; 
if (x_242 == 0)
{
lean_ctor_set(x_241, 0, x_246);
x_249 = x_241;
goto block_253;
}
else
{
lean_object* x_254; 
x_254 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_254, 0, x_246);
x_249 = x_254;
goto block_253;
}
block_253:
{
lean_object* x_250; 
if (x_248 == 0)
{
lean_ctor_set(x_247, 0, x_249);
x_250 = x_247;
goto block_251;
}
else
{
lean_object* x_252; 
x_252 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_252, 0, x_249);
x_250 = x_252;
goto block_251;
}
block_251:
{
return x_250;
}
}
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_245);
lean_del_object(x_241);
x_257 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
x_258 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_257, x_3, x_4, x_5, x_6, x_7, x_8);
return x_258;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_st_mk_ref(x_3);
lean_inc(x_10);
x_11 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_2, x_4, x_10, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_st_ref_get(x_10);
lean_dec(x_10);
lean_dec(x_15);
if (x_14 == 0)
{
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_dec(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Compiler_LCNF_Code_internalize(x_10, x_2, x_3, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_35; 
x_10 = lean_ctor_get(x_2, 0);
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
x_11 = x_2;
x_12 = x_35;
goto block_34;
}
else
{
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(x_3);
x_14 = lean_apply_8(x_1, x_10, x_13, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_25; 
x_15 = lean_ctor_get(x_14, 0);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
x_16 = x_14;
x_17 = x_25;
goto block_24;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_18; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_15);
x_18 = x_11;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_15);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_del_object(x_11);
x_26 = lean_ctor_get(x_14, 0);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
x_27 = x_14;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_2);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_4);
x_13 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(x_11, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_73; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_13 = lean_ctor_get(x_2, 2);
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
x_14 = x_2;
x_15 = x_73;
goto block_72;
}
else
{
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; uint8_t x_71; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 2);
x_19 = lean_ctor_get(x_10, 3);
x_20 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
x_71 = !lean_is_exclusive(x_10);
if (x_71 == 0)
{
x_21 = x_10;
x_22 = x_71;
goto block_70;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_23; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_23 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_array_size(x_19);
x_26 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_27 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_1, x_25, x_26, x_19, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_box(x_1);
x_30 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 9, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(x_30, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_45; 
x_32 = lean_ctor_get(x_31, 0);
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
x_33 = x_31;
x_34 = x_45;
goto block_44;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_35; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 3, x_28);
lean_ctor_set(x_21, 2, x_24);
x_35 = x_21;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_43, 0, x_16);
lean_ctor_set(x_43, 1, x_17);
lean_ctor_set(x_43, 2, x_24);
lean_ctor_set(x_43, 3, x_28);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_20);
x_35 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_36; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_32);
lean_ctor_set(x_14, 0, x_35);
x_36 = x_14;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_13);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_12);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_36);
x_37 = x_33;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec(x_28);
lean_dec(x_24);
lean_del_object(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_del_object(x_14);
lean_dec(x_13);
x_46 = lean_ctor_get(x_31, 0);
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
x_47 = x_31;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_31);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_24);
lean_del_object(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_del_object(x_14);
lean_dec(x_13);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_54 = lean_ctor_get(x_27, 0);
x_61 = !lean_is_exclusive(x_27);
if (x_61 == 0)
{
x_55 = x_27;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_27);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_del_object(x_21);
lean_dec_ref(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_del_object(x_14);
lean_dec(x_13);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_62 = lean_ctor_get(x_23, 0);
x_69 = !lean_is_exclusive(x_23);
if (x_69 == 0)
{
x_63 = x_23;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_23);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_3);
x_12 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_st_mk_ref(x_3);
lean_inc(x_10);
x_11 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(x_1, x_2, x_4, x_10, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_st_ref_get(x_10);
lean_dec(x_10);
lean_dec(x_15);
if (x_14 == 0)
{
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_dec(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Compiler_LCNF_Decl_internalize(x_10, x_2, x_3, x_11, x_5, x_6, x_7, x_8);
return x_12;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_41; 
x_12 = lean_st_ref_take(x_6);
x_13 = lean_ctor_get(x_12, 0);
x_41 = !lean_is_exclusive(x_12);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_12, 1);
lean_dec(x_42);
x_14 = x_12;
x_15 = x_41;
goto block_40;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_16);
x_17 = x_14;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_16);
x_17 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_st_ref_set(x_6, x_17);
x_19 = lean_array_uget_borrowed(x_4, x_3);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
x_22 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_19);
x_23 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_19, x_21, x_22, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_array_uset(x_4, x_3, x_20);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_28 = lean_array_uset(x_25, x_3, x_24);
x_3 = x_27;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_30 = lean_ctor_get(x_23, 0);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
x_31 = x_23;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__0, &l_Lean_Compiler_LCNF_cleanup___closed__0_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_8 = lean_st_ref_take(x_4);
lean_dec(x_8);
x_9 = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
x_10 = lean_st_ref_set(x_4, x_9);
x_11 = lean_array_size(x_2);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0(x_1, x_11, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cleanup___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Compiler_LCNF_cleanup(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_23; 
x_5 = lean_st_ref_take(x_1);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 3);
x_9 = lean_ctor_get(x_5, 4);
x_10 = lean_ctor_get(x_5, 5);
x_11 = lean_ctor_get(x_5, 6);
x_12 = lean_ctor_get(x_5, 7);
x_13 = lean_ctor_get(x_5, 8);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_5, 2);
lean_dec(x_24);
x_14 = x_5;
x_15 = x_23;
goto block_22;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_16; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 2, x_2);
x_16 = x_14;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_7);
lean_ctor_set(x_21, 2, x_2);
lean_ctor_set(x_21, 3, x_8);
lean_ctor_set(x_21, 4, x_9);
lean_ctor_set(x_21, 5, x_10);
lean_ctor_set(x_21, 6, x_11);
lean_ctor_set(x_21, 7, x_12);
lean_ctor_set(x_21, 8, x_13);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_st_ref_set(x_1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_61; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_st_ref_take(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 3);
x_11 = lean_ctor_get(x_7, 4);
x_12 = lean_ctor_get(x_7, 5);
x_13 = lean_ctor_get(x_7, 6);
x_14 = lean_ctor_get(x_7, 7);
x_15 = lean_ctor_get(x_7, 8);
x_61 = !lean_is_exclusive(x_7);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_7, 2);
lean_dec(x_62);
x_16 = x_7;
x_17 = x_61;
goto block_60;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_18; lean_object* x_19; 
x_18 = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
if (x_17 == 0)
{
lean_ctor_set(x_16, 2, x_18);
x_19 = x_16;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_59, 0, x_8);
lean_ctor_set(x_59, 1, x_9);
lean_ctor_set(x_59, 2, x_18);
lean_ctor_set(x_59, 3, x_10);
lean_ctor_set(x_59, 4, x_11);
lean_ctor_set(x_59, 5, x_12);
lean_ctor_set(x_59, 6, x_13);
lean_ctor_set(x_59, 7, x_14);
lean_ctor_set(x_59, 8, x_15);
x_19 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_20 = lean_st_ref_set(x_4, x_19);
x_21 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_21);
lean_dec(x_6);
x_22 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
x_23 = 0;
x_24 = lean_box(x_1);
x_25 = lean_box(x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 9, 4);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_22);
lean_closure_set(x_26, 3, x_25);
x_27 = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
x_28 = 0;
lean_inc(x_4);
x_29 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_26, x_27, x_28, x_3, x_4);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_46; 
x_30 = lean_ctor_get(x_29, 0);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
x_31 = x_29;
x_32 = x_46;
goto block_45;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_33; 
lean_inc(x_30);
if (x_32 == 0)
{
lean_ctor_set_tag(x_31, 1);
x_33 = x_31;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_30);
x_33 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
x_34 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_4, x_21, x_33);
lean_dec_ref(x_33);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_34, 0);
lean_dec(x_42);
x_35 = x_34;
x_36 = x_41;
goto block_40;
}
else
{
lean_dec(x_34);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_30);
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_30);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
lean_dec_ref(x_29);
x_48 = lean_box(0);
x_49 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_4, x_21, x_48);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_49, 0);
lean_dec(x_57);
x_50 = x_49;
x_51 = x_56;
goto block_55;
}
else
{
lean_dec(x_49);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 0, x_47);
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_47);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_normalizeFVarIds(x_6, x_2, x_3, x_4);
return x_7;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_Bind(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Bind(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Internalize(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Internalize(builtin);
}
#ifdef __cplusplus
}
#endif
