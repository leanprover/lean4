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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0_value;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1_value;
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__2_value;
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__3_value;
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__4_value;
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__5_value;
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__5_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__4_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__6_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__6_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__3_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__7_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__2_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__8_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__9_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__0_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10_value;
lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_get, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___boxed(lean_object*);
lean_object* l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0;
lean_object* l_instMonadStateOfMonadStateOf___redArg(lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1;
lean_object* l_modify(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_st_ref_get(x_2);
x_6 = lean_st_ref_take(x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 1, x_10);
x_11 = lean_st_ref_set(x_2, x_6);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_Name_num___override(x_4, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_st_ref_set(x_2, x_19);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec(x_5);
x_22 = l_Lean_Name_num___override(x_4, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__11));
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
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__10));
x_2 = l_StateRefT_x27_instMonadStateOfOfMonadLiftTST___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0, &l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0_once, _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__0);
x_2 = l_instMonadStateOfMonadStateOf___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1, &l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1);
x_2 = lean_alloc_closure((void*)(l_modify), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2, &l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__2);
return x_2;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_instBEqFVarId_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_instBEqFVarId_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_instHashableFVarId_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget_borrowed(x_1, x_18);
lean_inc(x_19);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_instHashableFVarId_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget_borrowed(x_1, x_37);
lean_inc(x_38);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_instHashableFVarId_hash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget_borrowed(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
lean_inc(x_20);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_20);
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_instHashableFVarId_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget_borrowed(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__2___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
lean_inc(x_52);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__3___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_52);
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1_spec__4___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_st_ref_take(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 2);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Name_num___override(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_8, 2, x_4);
x_14 = lean_st_ref_set(x_1, x_8);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Name_num___override(x_6, x_7);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_7, x_25);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_26);
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_18);
lean_ctor_set(x_27, 4, x_19);
lean_ctor_set(x_27, 5, x_20);
lean_ctor_set(x_27, 6, x_21);
lean_ctor_set(x_27, 7, x_22);
lean_ctor_set(x_27, 8, x_23);
x_28 = lean_st_ref_set(x_1, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_24);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = lean_st_ref_take(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 3);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_32, 4);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_32, 5);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_32, 6);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_32, 7);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_32, 8);
lean_inc_ref(x_40);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 lean_ctor_release(x_32, 5);
 lean_ctor_release(x_32, 6);
 lean_ctor_release(x_32, 7);
 lean_ctor_release(x_32, 8);
 x_41 = x_32;
} else {
 lean_dec_ref(x_32);
 x_41 = lean_box(0);
}
lean_inc(x_31);
lean_inc(x_30);
x_42 = l_Lean_Name_num___override(x_30, x_31);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_31, x_43);
lean_dec(x_31);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 9, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_34);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_35);
lean_ctor_set(x_46, 4, x_36);
lean_ctor_set(x_46, 5, x_37);
lean_ctor_set(x_46, 6, x_38);
lean_ctor_set(x_46, 7, x_39);
lean_ctor_set(x_46, 8, x_40);
x_47 = lean_st_ref_set(x_1, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_42);
return x_48;
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
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_st_ref_take(x_2);
lean_inc(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(x_11, x_1, x_12);
x_14 = lean_st_ref_set(x_2, x_13);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_st_ref_take(x_2);
lean_inc(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__1___redArg(x_16, x_1, x_17);
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
return x_20;
}
}
else
{
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___redArg(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
x_9 = l_ReaderT_instMonad___redArg(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(x_14);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_15);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_25);
lean_ctor_set(x_11, 2, x_26);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_23);
lean_ctor_set(x_9, 1, x_20);
x_27 = l_ReaderT_instMonad___redArg(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_36 = lean_ctor_get(x_29, 1);
lean_dec(x_36);
x_37 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_38 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_32);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_44, 0, x_33);
lean_ctor_set(x_29, 4, x_42);
lean_ctor_set(x_29, 3, x_43);
lean_ctor_set(x_29, 2, x_44);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_27, 1, x_38);
x_45 = l_ReaderT_instMonad___redArg(x_27);
x_46 = l_Lean_instInhabitedExpr;
x_47 = l_instInhabitedOfMonad___redArg(x_45, x_46);
x_48 = lean_panic_fn(x_47, x_1);
x_49 = lean_apply_6(x_48, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 2);
x_52 = lean_ctor_get(x_29, 3);
x_53 = lean_ctor_get(x_29, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_54 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_55 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_50);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_50);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_53);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_52);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_51);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
lean_ctor_set(x_27, 1, x_55);
lean_ctor_set(x_27, 0, x_62);
x_63 = l_ReaderT_instMonad___redArg(x_27);
x_64 = l_Lean_instInhabitedExpr;
x_65 = l_instInhabitedOfMonad___redArg(x_63, x_64);
x_66 = lean_panic_fn(x_65, x_1);
x_67 = lean_apply_6(x_66, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_68 = lean_ctor_get(x_27, 0);
lean_inc(x_68);
lean_dec(x_27);
x_69 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_68, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 4);
lean_inc(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_75 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_69);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_76, 0, x_69);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_77, 0, x_69);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_80, 0, x_71);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_81, 0, x_70);
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 5, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
x_84 = l_ReaderT_instMonad___redArg(x_83);
x_85 = l_Lean_instInhabitedExpr;
x_86 = l_instInhabitedOfMonad___redArg(x_84, x_85);
x_87 = lean_panic_fn(x_86, x_1);
x_88 = lean_apply_6(x_87, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_89 = lean_ctor_get(x_11, 0);
x_90 = lean_ctor_get(x_11, 2);
x_91 = lean_ctor_get(x_11, 3);
x_92 = lean_ctor_get(x_11, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_11);
x_93 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
x_94 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(x_89);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_95, 0, x_89);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_98, 0, x_92);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_99, 0, x_91);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_100, 0, x_90);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_99);
lean_ctor_set(x_101, 4, x_98);
lean_ctor_set(x_9, 1, x_94);
lean_ctor_set(x_9, 0, x_101);
x_102 = l_ReaderT_instMonad___redArg(x_9);
x_103 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_103, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_111 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_105);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_112, 0, x_105);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_113, 0, x_105);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_115, 0, x_108);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_116, 0, x_107);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_117, 0, x_106);
if (lean_is_scalar(x_109)) {
 x_118 = lean_alloc_ctor(0, 5, 0);
} else {
 x_118 = x_109;
}
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_110);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_116);
lean_ctor_set(x_118, 4, x_115);
if (lean_is_scalar(x_104)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_104;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
x_120 = l_ReaderT_instMonad___redArg(x_119);
x_121 = l_Lean_instInhabitedExpr;
x_122 = l_instInhabitedOfMonad___redArg(x_120, x_121);
x_123 = lean_panic_fn(x_122, x_1);
x_124 = lean_apply_6(x_123, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_125 = lean_ctor_get(x_9, 0);
lean_inc(x_125);
lean_dec(x_9);
x_126 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_125, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 4);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
x_132 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(x_126);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_133, 0, x_126);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_134, 0, x_126);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_136, 0, x_129);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_137, 0, x_128);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_138, 0, x_127);
if (lean_is_scalar(x_130)) {
 x_139 = lean_alloc_ctor(0, 5, 0);
} else {
 x_139 = x_130;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_137);
lean_ctor_set(x_139, 4, x_136);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_132);
x_141 = l_ReaderT_instMonad___redArg(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_142, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 4);
lean_inc(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_150 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_144);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_151, 0, x_144);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_152, 0, x_144);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_154, 0, x_147);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_155, 0, x_146);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_156, 0, x_145);
if (lean_is_scalar(x_148)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_148;
}
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_155);
lean_ctor_set(x_157, 4, x_154);
if (lean_is_scalar(x_143)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_143;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
x_159 = l_ReaderT_instMonad___redArg(x_158);
x_160 = l_Lean_instInhabitedExpr;
x_161 = l_instInhabitedOfMonad___redArg(x_159, x_160);
x_162 = lean_panic_fn(x_161, x_1);
x_163 = lean_apply_6(x_162, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_163;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(20u);
x_3 = lean_unsigned_to_nat(70u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_hasFVar(x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_13 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(x_12, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec_ref(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_17; 
lean_dec(x_5);
x_17 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_13);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_Compiler_LCNF_findParam_x3f___redArg(x_1, x_18, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_18);
goto block_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_20, 0);
lean_dec(x_26);
if (x_9 == 0)
{
lean_free_object(x_20);
lean_dec(x_18);
goto block_24;
}
else
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = l_Lean_Expr_fvar___override(x_18);
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
}
else
{
lean_dec(x_20);
if (x_9 == 0)
{
lean_dec(x_18);
goto block_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
x_28 = l_Lean_Expr_fvar___override(x_18);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Compiler_LCNF_anyExpr;
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_30; 
lean_dec(x_18);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
default: 
{
uint8_t x_33; 
lean_free_object(x_13);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
lean_ctor_set_tag(x_16, 0);
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
switch (lean_obj_tag(x_36)) {
case 0:
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_5);
x_37 = l_Lean_Compiler_LCNF_erasedExpr;
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
case 1:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec_ref(x_36);
x_40 = l_Lean_Compiler_LCNF_findParam_x3f___redArg(x_1, x_39, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_obj_tag(x_41) == 0)
{
lean_dec(x_39);
goto block_45;
}
else
{
lean_object* x_46; 
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_46 = x_41;
} else {
 lean_dec_ref(x_41);
 x_46 = lean_box(0);
}
if (x_9 == 0)
{
lean_dec(x_46);
lean_dec(x_39);
goto block_45;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
x_47 = l_Lean_Expr_fvar___override(x_39);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_46;
 lean_ctor_set_tag(x_48, 0);
}
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
block_45:
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Compiler_LCNF_anyExpr;
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_39);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_50 = x_40;
} else {
 lean_dec_ref(x_40);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
}
default: 
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_5);
x_52 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_53 = x_36;
} else {
 lean_dec_ref(x_36);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_53;
 lean_ctor_set_tag(x_54, 0);
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
}
}
}
}
case 5:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_55);
x_57 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(x_1, x_55, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc_ref(x_56);
x_59 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_56, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_66; size_t x_69; size_t x_70; uint8_t x_71; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_69 = lean_ptr_addr(x_55);
x_70 = lean_ptr_addr(x_58);
x_71 = lean_usize_dec_eq(x_69, x_70);
if (x_71 == 0)
{
x_66 = x_71;
goto block_68;
}
else
{
size_t x_72; size_t x_73; uint8_t x_74; 
x_72 = lean_ptr_addr(x_56);
x_73 = lean_ptr_addr(x_60);
x_74 = lean_usize_dec_eq(x_72, x_73);
x_66 = x_74;
goto block_68;
}
block_65:
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_Expr_headBeta(x_62);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
block_68:
{
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec_ref(x_2);
x_67 = l_Lean_Expr_app___override(x_58, x_60);
x_62 = x_67;
goto block_65;
}
else
{
lean_dec(x_60);
lean_dec(x_58);
x_62 = x_2;
goto block_65;
}
}
}
else
{
lean_dec(x_58);
lean_dec_ref(x_2);
return x_59;
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_57;
}
}
case 6:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_2, 0);
x_76 = lean_ctor_get(x_2, 1);
x_77 = lean_ctor_get(x_2, 2);
x_78 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_76);
x_79 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_76, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
lean_inc_ref(x_77);
x_81 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_77, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; size_t x_92; size_t x_93; uint8_t x_94; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_92 = lean_ptr_addr(x_76);
x_93 = lean_ptr_addr(x_80);
x_94 = lean_usize_dec_eq(x_92, x_93);
if (x_94 == 0)
{
x_84 = x_94;
goto block_91;
}
else
{
size_t x_95; size_t x_96; uint8_t x_97; 
x_95 = lean_ptr_addr(x_77);
x_96 = lean_ptr_addr(x_82);
x_97 = lean_usize_dec_eq(x_95, x_96);
x_84 = x_97;
goto block_91;
}
block_91:
{
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_inc(x_75);
lean_dec_ref(x_2);
x_85 = l_Lean_Expr_lam___override(x_75, x_80, x_82, x_78);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
else
{
uint8_t x_87; 
x_87 = l_Lean_instBEqBinderInfo_beq(x_78, x_78);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_inc(x_75);
lean_dec_ref(x_2);
x_88 = l_Lean_Expr_lam___override(x_75, x_80, x_82, x_78);
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(0, 1, 0);
} else {
 x_89 = x_83;
}
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec(x_82);
lean_dec(x_80);
if (lean_is_scalar(x_83)) {
 x_90 = lean_alloc_ctor(0, 1, 0);
} else {
 x_90 = x_83;
}
lean_ctor_set(x_90, 0, x_2);
return x_90;
}
}
}
}
else
{
lean_dec(x_80);
lean_dec_ref(x_2);
return x_81;
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_79;
}
}
case 7:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_2, 0);
x_99 = lean_ctor_get(x_2, 1);
x_100 = lean_ctor_get(x_2, 2);
x_101 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_99);
x_102 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_99, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
lean_inc_ref(x_100);
x_104 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_100, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; size_t x_115; size_t x_116; uint8_t x_117; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_115 = lean_ptr_addr(x_99);
x_116 = lean_ptr_addr(x_103);
x_117 = lean_usize_dec_eq(x_115, x_116);
if (x_117 == 0)
{
x_107 = x_117;
goto block_114;
}
else
{
size_t x_118; size_t x_119; uint8_t x_120; 
x_118 = lean_ptr_addr(x_100);
x_119 = lean_ptr_addr(x_105);
x_120 = lean_usize_dec_eq(x_118, x_119);
x_107 = x_120;
goto block_114;
}
block_114:
{
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_inc(x_98);
lean_dec_ref(x_2);
x_108 = l_Lean_Expr_forallE___override(x_98, x_103, x_105, x_101);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 1, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
else
{
uint8_t x_110; 
x_110 = l_Lean_instBEqBinderInfo_beq(x_101, x_101);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_inc(x_98);
lean_dec_ref(x_2);
x_111 = l_Lean_Expr_forallE___override(x_98, x_103, x_105, x_101);
if (lean_is_scalar(x_106)) {
 x_112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_112 = x_106;
}
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
else
{
lean_object* x_113; 
lean_dec(x_105);
lean_dec(x_103);
if (lean_is_scalar(x_106)) {
 x_113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_113 = x_106;
}
lean_ctor_set(x_113, 0, x_2);
return x_113;
}
}
}
}
else
{
lean_dec(x_103);
lean_dec_ref(x_2);
return x_104;
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_102;
}
}
case 8:
{
lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_2);
x_121 = lean_obj_once(&l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3, &l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__3);
x_122 = l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2(x_121, x_3, x_4, x_5, x_6, x_7);
return x_122;
}
case 10:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_2, 0);
x_124 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_124);
x_125 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_124, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; size_t x_128; size_t x_129; uint8_t x_130; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ptr_addr(x_124);
x_129 = lean_ptr_addr(x_127);
x_130 = lean_usize_dec_eq(x_128, x_129);
if (x_130 == 0)
{
lean_object* x_131; 
lean_inc(x_123);
lean_dec_ref(x_2);
x_131 = l_Lean_Expr_mdata___override(x_123, x_127);
lean_ctor_set(x_125, 0, x_131);
return x_125;
}
else
{
lean_dec(x_127);
lean_ctor_set(x_125, 0, x_2);
return x_125;
}
}
else
{
lean_object* x_132; size_t x_133; size_t x_134; uint8_t x_135; 
x_132 = lean_ctor_get(x_125, 0);
lean_inc(x_132);
lean_dec(x_125);
x_133 = lean_ptr_addr(x_124);
x_134 = lean_ptr_addr(x_132);
x_135 = lean_usize_dec_eq(x_133, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_inc(x_123);
lean_dec_ref(x_2);
x_136 = l_Lean_Expr_mdata___override(x_123, x_132);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_132);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_2);
return x_138;
}
}
}
else
{
lean_dec_ref(x_2);
return x_125;
}
}
case 11:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_2, 0);
x_140 = lean_ctor_get(x_2, 1);
x_141 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_141);
x_142 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_141, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; size_t x_145; size_t x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ptr_addr(x_141);
x_146 = lean_ptr_addr(x_144);
x_147 = lean_usize_dec_eq(x_145, x_146);
if (x_147 == 0)
{
lean_object* x_148; 
lean_inc(x_140);
lean_inc(x_139);
lean_dec_ref(x_2);
x_148 = l_Lean_Expr_proj___override(x_139, x_140, x_144);
lean_ctor_set(x_142, 0, x_148);
return x_142;
}
else
{
lean_dec(x_144);
lean_ctor_set(x_142, 0, x_2);
return x_142;
}
}
else
{
lean_object* x_149; size_t x_150; size_t x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_142, 0);
lean_inc(x_149);
lean_dec(x_142);
x_150 = lean_ptr_addr(x_141);
x_151 = lean_ptr_addr(x_149);
x_152 = lean_usize_dec_eq(x_150, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_inc(x_140);
lean_inc(x_139);
lean_dec_ref(x_2);
x_153 = l_Lean_Expr_proj___override(x_139, x_140, x_149);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
else
{
lean_object* x_155; 
lean_dec(x_149);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_2);
return x_155;
}
}
}
else
{
lean_dec_ref(x_2);
return x_142;
}
}
default: 
{
lean_object* x_156; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_2);
return x_156;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_9);
x_11 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc_ref(x_10);
x_13 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; size_t x_21; size_t x_22; uint8_t x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_15 = x_13;
} else {
 lean_dec_ref(x_13);
 x_15 = lean_box(0);
}
x_21 = lean_ptr_addr(x_9);
x_22 = lean_ptr_addr(x_12);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
x_16 = x_23;
goto block_20;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = lean_ptr_addr(x_10);
x_25 = lean_ptr_addr(x_14);
x_26 = lean_usize_dec_eq(x_24, x_25);
x_16 = x_26;
goto block_20;
}
block_20:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_2);
x_17 = l_Lean_Expr_app___override(x_12, x_14);
if (lean_is_scalar(x_15)) {
 x_18 = lean_alloc_ctor(0, 1, 0);
} else {
 x_18 = x_15;
}
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_12);
if (lean_is_scalar(x_15)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_15;
}
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_2);
return x_13;
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
else
{
lean_object* x_27; 
x_27 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_goApp(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_11, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_15 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_st_ref_take(x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_2, 2, x_16);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_19);
lean_inc_ref(x_2);
x_23 = l_Lean_Compiler_LCNF_LCtx_addParam(x_1, x_22, x_2);
lean_ctor_set(x_20, 0, x_23);
x_24 = lean_st_ref_set(x_5, x_20);
lean_dec(x_5);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
lean_ctor_set(x_2, 2, x_16);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_19);
lean_inc_ref(x_2);
x_27 = l_Lean_Compiler_LCNF_LCtx_addParam(x_1, x_25, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_st_ref_set(x_5, x_28);
lean_dec(x_5);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_st_ref_take(x_5);
x_32 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
lean_ctor_set(x_2, 2, x_16);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_30);
lean_inc_ref(x_2);
x_35 = l_Lean_Compiler_LCNF_LCtx_addParam(x_1, x_32, x_2);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_st_ref_set(x_5, x_36);
lean_dec(x_5);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_2);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_16);
lean_dec(x_14);
lean_free_object(x_2);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_14);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_15, 0);
lean_inc(x_43);
lean_dec(x_15);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_2, 2);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
x_49 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_46, x_5);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_51 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_47, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_45, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_st_ref_take(x_5);
x_57 = lean_ctor_get(x_56, 0);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_50);
lean_ctor_set(x_60, 2, x_52);
lean_ctor_set_uint8(x_60, sizeof(void*)*3, x_48);
lean_inc_ref(x_60);
x_61 = l_Lean_Compiler_LCNF_LCtx_addParam(x_1, x_57, x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
x_63 = lean_st_ref_set(x_5, x_62);
lean_dec(x_5);
if (lean_is_scalar(x_55)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_55;
}
lean_ctor_set(x_64, 0, x_60);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_5);
x_65 = lean_ctor_get(x_53, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_66 = x_53;
} else {
 lean_dec_ref(x_53);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_68 = lean_ctor_get(x_51, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_69 = x_51;
} else {
 lean_dec_ref(x_51);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_12 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__1___redArg(x_11, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec_ref(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; 
x_16 = lean_box(0);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
case 1:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_ctor_set_tag(x_12, 0);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
}
default: 
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_ctor_set_tag(x_12, 0);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
}
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
switch (lean_obj_tag(x_23)) {
case 0:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
default: 
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(2, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
default: 
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_34);
x_35 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_34, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(x_1, x_2, x_37);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec(x_35);
x_40 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(x_1, x_2, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec_ref(x_2);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Internalize_internalizeArg(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget_borrowed(x_4, x_3);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_14 = l_Lean_Compiler_LCNF_Internalize_internalizeArg(x_1, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_17, x_3, x_15);
x_3 = x_19;
x_4 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_array_size(x_2);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeArgs_spec__0(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_44 = 1;
lean_inc(x_42);
x_45 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_43, x_42, x_44);
lean_dec(x_43);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_1, x_2, x_47);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_1, x_2, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_2);
x_52 = lean_box(1);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
case 3:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_54);
x_55 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_54, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_1, x_2, x_57);
lean_ctor_set(x_55, 0, x_58);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
lean_dec(x_55);
x_60 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_1, x_2, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec_ref(x_2);
x_62 = !lean_is_exclusive(x_55);
if (x_62 == 0)
{
return x_55;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
lean_dec(x_55);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
case 4:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
x_67 = lean_st_ref_get(x_3);
x_68 = 1;
lean_inc(x_65);
x_69 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_67, x_65, x_68);
lean_dec(x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
lean_inc_ref(x_66);
x_71 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_66, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(x_1, x_2, x_70, x_73);
lean_dec_ref(x_2);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
lean_dec(x_71);
x_76 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(x_1, x_2, x_70, x_75);
lean_dec_ref(x_2);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_70);
lean_dec_ref(x_2);
x_78 = !lean_is_exclusive(x_71);
if (x_78 == 0)
{
return x_71;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_71, 0);
lean_inc(x_79);
lean_dec(x_71);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_2);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_81 = lean_box(1);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
case 5:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_83);
x_84 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_83, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_1, x_2, x_86);
lean_ctor_set(x_84, 0, x_87);
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec(x_84);
x_89 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_1, x_2, x_88);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec_ref(x_2);
x_91 = !lean_is_exclusive(x_84);
if (x_91 == 0)
{
return x_84;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_84, 0);
lean_inc(x_92);
lean_dec(x_84);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
case 6:
{
lean_object* x_94; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_94 = lean_ctor_get(x_2, 1);
lean_inc(x_94);
x_9 = x_94;
x_10 = x_3;
x_11 = lean_box(0);
goto block_23;
}
case 7:
{
lean_object* x_95; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_95 = lean_ctor_get(x_2, 1);
lean_inc(x_95);
x_9 = x_95;
x_10 = x_3;
x_11 = lean_box(0);
goto block_23;
}
case 8:
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_96 = lean_ctor_get(x_2, 2);
x_97 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_98 = 1;
lean_inc(x_96);
x_99 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_97, x_96, x_98);
lean_dec(x_97);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_1, x_2, x_101);
lean_ctor_set(x_99, 0, x_102);
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
lean_dec(x_99);
x_104 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_1, x_2, x_103);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_2);
x_106 = lean_box(1);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
case 9:
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_108);
x_24 = x_108;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = lean_box(0);
goto block_41;
}
case 10:
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_109);
x_24 = x_109;
x_25 = x_3;
x_26 = x_4;
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = lean_box(0);
goto block_41;
}
case 11:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_110 = lean_ctor_get(x_2, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_2, 1);
x_112 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_113 = 1;
lean_inc(x_111);
x_114 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_112, x_111, x_113);
lean_dec(x_112);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(x_1, x_2, x_110, x_116);
lean_dec_ref(x_2);
lean_ctor_set(x_114, 0, x_117);
return x_114;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
lean_dec(x_114);
x_119 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateResetImp(x_1, x_2, x_110, x_118);
lean_dec_ref(x_2);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_2);
lean_dec(x_110);
x_121 = lean_box(1);
x_122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
case 12:
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_2, 0);
x_124 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_124);
x_125 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_126 = lean_ctor_get(x_2, 2);
x_127 = lean_st_ref_get(x_3);
x_128 = 1;
lean_inc(x_123);
x_129 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_127, x_123, x_128);
lean_dec(x_127);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
lean_inc_ref(x_126);
x_131 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_126, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(x_1, x_2, x_130, x_124, x_125, x_133);
lean_ctor_set(x_131, 0, x_134);
return x_131;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
lean_dec(x_131);
x_136 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateReuseImp(x_1, x_2, x_130, x_124, x_125, x_135);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
else
{
uint8_t x_138; 
lean_dec(x_130);
lean_dec_ref(x_124);
lean_dec_ref(x_2);
x_138 = !lean_is_exclusive(x_131);
if (x_138 == 0)
{
return x_131;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_131, 0);
lean_inc(x_139);
lean_dec(x_131);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec_ref(x_124);
lean_dec_ref(x_2);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_141 = lean_box(1);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
case 13:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_143 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_2, 1);
x_145 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_146 = 1;
lean_inc(x_144);
x_147 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_145, x_144, x_146);
lean_dec(x_145);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(x_1, x_2, x_143, x_149);
lean_dec_ref(x_2);
lean_ctor_set(x_147, 0, x_150);
return x_147;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
lean_dec(x_147);
x_152 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateBoxImp(x_1, x_2, x_143, x_151);
lean_dec_ref(x_2);
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_143);
lean_dec_ref(x_2);
x_154 = lean_box(1);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
case 14:
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_156 = lean_ctor_get(x_2, 0);
x_157 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_158 = 1;
lean_inc(x_156);
x_159 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_157, x_156, x_158);
lean_dec(x_157);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_159, 0);
x_162 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(x_1, x_2, x_161);
lean_ctor_set(x_159, 0, x_162);
return x_159;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
lean_dec(x_159);
x_164 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateUnboxImp(x_1, x_2, x_163);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
else
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_2);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_2, 0);
lean_dec(x_167);
x_168 = lean_box(1);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_168);
return x_2;
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_2);
x_169 = lean_box(1);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
}
case 15:
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_171 = lean_ctor_get(x_2, 0);
x_172 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_173 = 1;
lean_inc(x_171);
x_174 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_172, x_171, x_173);
lean_dec(x_172);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(x_1, x_2, x_176);
lean_ctor_set(x_174, 0, x_177);
return x_174;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_174, 0);
lean_inc(x_178);
lean_dec(x_174);
x_179 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateIsSharedImp(x_1, x_2, x_178);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
}
else
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_2);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_2, 0);
lean_dec(x_182);
x_183 = lean_box(1);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_183);
return x_2;
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_2);
x_184 = lean_box(1);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
}
default: 
{
lean_object* x_186; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_2);
return x_186;
}
}
block_23:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_st_ref_get(x_10);
lean_dec(x_10);
x_13 = 1;
x_14 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_12, x_9, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_1, x_2, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_1, x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
block_41:
{
lean_object* x_31; 
x_31 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_24, x_25, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_1, x_2, x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_1, x_2, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_11, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_16 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(x_1, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_st_ref_take(x_5);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_2, 3, x_19);
lean_ctor_set(x_2, 2, x_17);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_22);
lean_inc_ref(x_2);
x_26 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_1, x_25, x_2);
lean_ctor_set(x_23, 0, x_26);
x_27 = lean_st_ref_set(x_5, x_23);
lean_dec(x_5);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
lean_ctor_set(x_2, 3, x_19);
lean_ctor_set(x_2, 2, x_17);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_22);
lean_inc_ref(x_2);
x_30 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_1, x_28, x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_st_ref_set(x_5, x_31);
lean_dec(x_5);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_st_ref_take(x_5);
x_35 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
lean_ctor_set(x_2, 3, x_19);
lean_ctor_set(x_2, 2, x_17);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_33);
lean_inc_ref(x_2);
x_38 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_1, x_35, x_2);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_st_ref_set(x_5, x_39);
lean_dec(x_5);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_2);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_20, 0);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_17);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_18);
if (x_45 == 0)
{
return x_18;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_18, 0);
lean_inc(x_46);
lean_dec(x_18);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
return x_16;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
lean_dec(x_16);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 1);
x_53 = lean_ctor_get(x_2, 2);
x_54 = lean_ctor_get(x_2, 3);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_2);
x_55 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_52, x_5);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_57 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_53, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_59 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeLetValue(x_1, x_54, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_51, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_st_ref_take(x_5);
x_65 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_56);
lean_ctor_set(x_68, 2, x_58);
lean_ctor_set(x_68, 3, x_60);
lean_inc_ref(x_68);
x_69 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_1, x_65, x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
x_71 = lean_st_ref_set(x_5, x_70);
lean_dec(x_5);
if (lean_is_scalar(x_63)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_63;
}
lean_ctor_set(x_72, 0, x_68);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_5);
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_74 = x_61;
} else {
 lean_dec_ref(x_61);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_51);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_76 = lean_ctor_get(x_59, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_77 = x_59;
} else {
 lean_dec_ref(x_59);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_79 = lean_ctor_get(x_57, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_80 = x_57;
} else {
 lean_dec_ref(x_57);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget_borrowed(x_4, x_3);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_14 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_1, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_17, x_3, x_15);
x_3 = x_19;
x_4 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(uint8_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
x_26 = lean_ctor_get(x_13, 2);
x_27 = lean_array_size(x_25);
x_28 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_29 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_1, x_27, x_28, x_25, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_31 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_26, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
lean_ctor_set(x_13, 2, x_32);
lean_ctor_set(x_13, 1, x_30);
x_16 = x_13;
x_17 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_33; 
lean_dec(x_30);
lean_free_object(x_13);
lean_dec(x_24);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_free_object(x_13);
lean_dec_ref(x_26);
lean_dec(x_24);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_29;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
x_38 = lean_ctor_get(x_13, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_39 = lean_array_size(x_37);
x_40 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_41 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_1, x_39, x_40, x_37, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_43 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_38, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_44);
x_16 = x_45;
x_17 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
lean_dec(x_36);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_47 = x_43;
} else {
 lean_dec_ref(x_43);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
}
else
{
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_41;
}
}
}
case 1:
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_52 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_51, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_ctor_set(x_13, 1, x_53);
x_16 = x_13;
x_17 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_54; 
lean_free_object(x_13);
lean_dec_ref(x_50);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_59 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_58, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
x_16 = x_61;
x_17 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_57);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
}
}
default: 
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_13);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_13, 0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_67 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_66, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
lean_ctor_set(x_13, 0, x_68);
x_16 = x_13;
x_17 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_69; 
lean_free_object(x_13);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_13, 0);
lean_inc(x_72);
lean_dec(x_13);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_73 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_72, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_16 = x_75;
x_17 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
}
}
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_15, x_3, x_16);
x_3 = x_19;
x_4 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_12 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
}
else
{
lean_dec(x_13);
lean_free_object(x_2);
return x_14;
}
}
else
{
uint8_t x_19; 
lean_free_object(x_2);
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_24 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_1, x_22, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_23, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_27);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 1, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_dec(x_25);
return x_26;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_32 = x_24;
} else {
 lean_dec_ref(x_24);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_37 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_35, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_36, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_ctor_set(x_2, 1, x_41);
lean_ctor_set(x_2, 0, x_38);
lean_ctor_set(x_39, 0, x_2);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
lean_ctor_set(x_2, 1, x_42);
lean_ctor_set(x_2, 0, x_38);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_2);
return x_43;
}
}
else
{
lean_dec(x_38);
lean_free_object(x_2);
return x_39;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_2);
lean_dec_ref(x_36);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_49 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_47, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_48, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_52);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_dec(x_50);
return x_51;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_48);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_57 = x_49;
} else {
 lean_dec_ref(x_49);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
}
case 2:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_62 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_60, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_61, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_ctor_set(x_2, 1, x_66);
lean_ctor_set(x_2, 0, x_63);
lean_ctor_set(x_64, 0, x_2);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
lean_ctor_set(x_2, 1, x_67);
lean_ctor_set(x_2, 0, x_63);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_2);
return x_68;
}
}
else
{
lean_dec(x_63);
lean_free_object(x_2);
return x_64;
}
}
else
{
uint8_t x_69; 
lean_free_object(x_2);
lean_dec_ref(x_61);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_62);
if (x_69 == 0)
{
return x_62;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_2, 0);
x_73 = lean_ctor_get(x_2, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_74 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_72, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_73, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_77);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
else
{
lean_dec(x_75);
return x_76;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_73);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_82 = x_74;
} else {
 lean_dec_ref(x_74);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
}
case 3:
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_2);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_2, 0);
x_86 = lean_ctor_get(x_2, 1);
x_87 = lean_st_ref_get(x_3);
x_88 = 1;
x_89 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_87, x_85, x_88);
lean_dec(x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_86, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 0);
lean_ctor_set(x_2, 1, x_93);
lean_ctor_set(x_2, 0, x_90);
lean_ctor_set(x_91, 0, x_2);
return x_91;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_dec(x_91);
lean_ctor_set(x_2, 1, x_94);
lean_ctor_set(x_2, 0, x_90);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_2);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_90);
lean_free_object(x_2);
x_96 = !lean_is_exclusive(x_91);
if (x_96 == 0)
{
return x_91;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_91, 0);
lean_inc(x_97);
lean_dec(x_91);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; 
lean_free_object(x_2);
lean_dec_ref(x_86);
lean_dec(x_3);
x_99 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_2, 0);
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_2);
x_102 = lean_st_ref_get(x_3);
x_103 = 1;
x_104 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_102, x_100, x_103);
lean_dec(x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l_Lean_Compiler_LCNF_Internalize_internalizeArgs(x_1, x_101, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_107);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 1, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_105);
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_112 = x_106;
} else {
 lean_dec_ref(x_106);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; 
lean_dec_ref(x_101);
lean_dec(x_3);
x_114 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_114;
}
}
}
case 4:
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_2);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_2, 0);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_ctor_get(x_116, 1);
x_120 = lean_ctor_get(x_116, 2);
x_121 = lean_ctor_get(x_116, 3);
x_122 = lean_st_ref_get(x_3);
x_123 = 1;
x_124 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_122, x_120, x_123);
lean_dec(x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_126 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_119, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; size_t x_128; size_t x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_array_size(x_121);
x_129 = 0;
x_130 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(x_1, x_128, x_129, x_121, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_130, 0);
lean_ctor_set(x_116, 3, x_132);
lean_ctor_set(x_116, 2, x_125);
lean_ctor_set(x_116, 1, x_127);
lean_ctor_set(x_130, 0, x_2);
return x_130;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
lean_dec(x_130);
lean_ctor_set(x_116, 3, x_133);
lean_ctor_set(x_116, 2, x_125);
lean_ctor_set(x_116, 1, x_127);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_2);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_127);
lean_dec(x_125);
lean_free_object(x_116);
lean_dec(x_118);
lean_free_object(x_2);
x_135 = !lean_is_exclusive(x_130);
if (x_135 == 0)
{
return x_130;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_130, 0);
lean_inc(x_136);
lean_dec(x_130);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_125);
lean_free_object(x_116);
lean_dec_ref(x_121);
lean_dec(x_118);
lean_free_object(x_2);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_138 = !lean_is_exclusive(x_126);
if (x_138 == 0)
{
return x_126;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_126, 0);
lean_inc(x_139);
lean_dec(x_126);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; 
lean_free_object(x_116);
lean_dec_ref(x_121);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_free_object(x_2);
lean_dec(x_3);
x_141 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; 
x_142 = lean_ctor_get(x_116, 0);
x_143 = lean_ctor_get(x_116, 1);
x_144 = lean_ctor_get(x_116, 2);
x_145 = lean_ctor_get(x_116, 3);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_116);
x_146 = lean_st_ref_get(x_3);
x_147 = 1;
x_148 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_146, x_144, x_147);
lean_dec(x_146);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_150 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_143, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; size_t x_152; size_t x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = lean_array_size(x_145);
x_153 = 0;
x_154 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(x_1, x_152, x_153, x_145, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
x_157 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_157, 0, x_142);
lean_ctor_set(x_157, 1, x_151);
lean_ctor_set(x_157, 2, x_149);
lean_ctor_set(x_157, 3, x_155);
lean_ctor_set(x_2, 0, x_157);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 1, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_2);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_142);
lean_free_object(x_2);
x_159 = lean_ctor_get(x_154, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_160 = x_154;
} else {
 lean_dec_ref(x_154);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_149);
lean_dec_ref(x_145);
lean_dec(x_142);
lean_free_object(x_2);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_162 = lean_ctor_get(x_150, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_163 = x_150;
} else {
 lean_dec_ref(x_150);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
return x_164;
}
}
else
{
lean_object* x_165; 
lean_dec_ref(x_145);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_free_object(x_2);
lean_dec(x_3);
x_165 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; 
x_166 = lean_ctor_get(x_2, 0);
lean_inc(x_166);
lean_dec(x_2);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_166, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_166, 3);
lean_inc_ref(x_170);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 x_171 = x_166;
} else {
 lean_dec_ref(x_166);
 x_171 = lean_box(0);
}
x_172 = lean_st_ref_get(x_3);
x_173 = 1;
x_174 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_172, x_169, x_173);
lean_dec(x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec_ref(x_174);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_176 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_168, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; size_t x_178; size_t x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec_ref(x_176);
x_178 = lean_array_size(x_170);
x_179 = 0;
x_180 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(x_1, x_178, x_179, x_170, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_182 = x_180;
} else {
 lean_dec_ref(x_180);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_183 = lean_alloc_ctor(0, 4, 0);
} else {
 x_183 = x_171;
}
lean_ctor_set(x_183, 0, x_167);
lean_ctor_set(x_183, 1, x_177);
lean_ctor_set(x_183, 2, x_175);
lean_ctor_set(x_183, 3, x_181);
x_184 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_184, 0, x_183);
if (lean_is_scalar(x_182)) {
 x_185 = lean_alloc_ctor(0, 1, 0);
} else {
 x_185 = x_182;
}
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_167);
x_186 = lean_ctor_get(x_180, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_187 = x_180;
} else {
 lean_dec_ref(x_180);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec_ref(x_170);
lean_dec(x_167);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_189 = lean_ctor_get(x_176, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_190 = x_176;
} else {
 lean_dec_ref(x_176);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_189);
return x_191;
}
}
else
{
lean_object* x_192; 
lean_dec(x_171);
lean_dec_ref(x_170);
lean_dec_ref(x_168);
lean_dec(x_167);
lean_dec(x_3);
x_192 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_192;
}
}
}
case 5:
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_2);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_2, 0);
x_195 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_196 = 1;
x_197 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_195, x_194, x_196);
lean_dec(x_195);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_197, 0);
lean_ctor_set(x_2, 0, x_199);
lean_ctor_set(x_197, 0, x_2);
return x_197;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_197, 0);
lean_inc(x_200);
lean_dec(x_197);
lean_ctor_set(x_2, 0, x_200);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_2);
return x_201;
}
}
else
{
lean_object* x_202; 
lean_free_object(x_2);
x_202 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_2, 0);
lean_inc(x_203);
lean_dec(x_2);
x_204 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_205 = 1;
x_206 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_204, x_203, x_205);
lean_dec(x_204);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_209, 0, x_207);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 1, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
else
{
lean_object* x_211; 
x_211 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_211;
}
}
}
case 6:
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_2);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_2, 0);
x_214 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_213, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_214) == 0)
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_214, 0);
lean_ctor_set(x_2, 0, x_216);
lean_ctor_set(x_214, 0, x_2);
return x_214;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_214, 0);
lean_inc(x_217);
lean_dec(x_214);
lean_ctor_set(x_2, 0, x_217);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_2);
return x_218;
}
}
else
{
uint8_t x_219; 
lean_free_object(x_2);
x_219 = !lean_is_exclusive(x_214);
if (x_219 == 0)
{
return x_214;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_214, 0);
lean_inc(x_220);
lean_dec(x_214);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_2, 0);
lean_inc(x_222);
lean_dec(x_2);
x_223 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_222, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_225 = x_223;
} else {
 lean_dec_ref(x_223);
 x_225 = lean_box(0);
}
x_226 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_226, 0, x_224);
if (lean_is_scalar(x_225)) {
 x_227 = lean_alloc_ctor(0, 1, 0);
} else {
 x_227 = x_225;
}
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_223, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_229 = x_223;
} else {
 lean_dec_ref(x_223);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
return x_230;
}
}
}
case 7:
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_2);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_232 = lean_ctor_get(x_2, 0);
x_233 = lean_ctor_get(x_2, 1);
x_234 = lean_ctor_get(x_2, 2);
x_235 = lean_ctor_get(x_2, 3);
x_236 = lean_st_ref_get(x_3);
x_237 = 1;
x_238 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_236, x_232, x_237);
lean_dec(x_236);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = lean_st_ref_get(x_3);
x_241 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_1, x_240, x_234, x_237);
lean_dec(x_240);
x_242 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_235, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_242) == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_242, 0);
lean_ctor_set(x_2, 3, x_244);
lean_ctor_set(x_2, 2, x_241);
lean_ctor_set(x_2, 0, x_239);
lean_ctor_set(x_242, 0, x_2);
return x_242;
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
lean_dec(x_242);
lean_ctor_set(x_2, 3, x_245);
lean_ctor_set(x_2, 2, x_241);
lean_ctor_set(x_2, 0, x_239);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_2);
return x_246;
}
}
else
{
lean_dec(x_241);
lean_dec(x_239);
lean_free_object(x_2);
lean_dec(x_233);
return x_242;
}
}
else
{
lean_object* x_247; 
lean_free_object(x_2);
lean_dec_ref(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_3);
x_247 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; 
x_248 = lean_ctor_get(x_2, 0);
x_249 = lean_ctor_get(x_2, 1);
x_250 = lean_ctor_get(x_2, 2);
x_251 = lean_ctor_get(x_2, 3);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_2);
x_252 = lean_st_ref_get(x_3);
x_253 = 1;
x_254 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_252, x_248, x_253);
lean_dec(x_252);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = lean_st_ref_get(x_3);
x_257 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_1, x_256, x_250, x_253);
lean_dec(x_256);
x_258 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_251, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_260 = x_258;
} else {
 lean_dec_ref(x_258);
 x_260 = lean_box(0);
}
x_261 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_261, 0, x_255);
lean_ctor_set(x_261, 1, x_249);
lean_ctor_set(x_261, 2, x_257);
lean_ctor_set(x_261, 3, x_259);
if (lean_is_scalar(x_260)) {
 x_262 = lean_alloc_ctor(0, 1, 0);
} else {
 x_262 = x_260;
}
lean_ctor_set(x_262, 0, x_261);
return x_262;
}
else
{
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_249);
return x_258;
}
}
else
{
lean_object* x_263; 
lean_dec_ref(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_3);
x_263 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_263;
}
}
}
case 8:
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_2);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; 
x_265 = lean_ctor_get(x_2, 0);
x_266 = lean_ctor_get(x_2, 1);
x_267 = lean_ctor_get(x_2, 2);
x_268 = lean_ctor_get(x_2, 3);
x_269 = lean_st_ref_get(x_3);
x_270 = 1;
x_271 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_269, x_265, x_270);
lean_dec(x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec_ref(x_271);
x_273 = lean_st_ref_get(x_3);
x_274 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_273, x_267, x_270);
lean_dec(x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
lean_dec_ref(x_274);
x_276 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_268, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_276) == 0)
{
uint8_t x_277; 
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_276, 0);
lean_ctor_set(x_2, 3, x_278);
lean_ctor_set(x_2, 2, x_275);
lean_ctor_set(x_2, 0, x_272);
lean_ctor_set(x_276, 0, x_2);
return x_276;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_276, 0);
lean_inc(x_279);
lean_dec(x_276);
lean_ctor_set(x_2, 3, x_279);
lean_ctor_set(x_2, 2, x_275);
lean_ctor_set(x_2, 0, x_272);
x_280 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_280, 0, x_2);
return x_280;
}
}
else
{
lean_dec(x_275);
lean_dec(x_272);
lean_free_object(x_2);
lean_dec(x_266);
return x_276;
}
}
else
{
lean_object* x_281; 
lean_dec(x_272);
lean_free_object(x_2);
lean_dec_ref(x_268);
lean_dec(x_266);
lean_dec(x_3);
x_281 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_281;
}
}
else
{
lean_object* x_282; 
lean_free_object(x_2);
lean_dec_ref(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_3);
x_282 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; 
x_283 = lean_ctor_get(x_2, 0);
x_284 = lean_ctor_get(x_2, 1);
x_285 = lean_ctor_get(x_2, 2);
x_286 = lean_ctor_get(x_2, 3);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_2);
x_287 = lean_st_ref_get(x_3);
x_288 = 1;
x_289 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_287, x_283, x_288);
lean_dec(x_287);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
x_291 = lean_st_ref_get(x_3);
x_292 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_291, x_285, x_288);
lean_dec(x_291);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec_ref(x_292);
x_294 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_286, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_296 = x_294;
} else {
 lean_dec_ref(x_294);
 x_296 = lean_box(0);
}
x_297 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_297, 0, x_290);
lean_ctor_set(x_297, 1, x_284);
lean_ctor_set(x_297, 2, x_293);
lean_ctor_set(x_297, 3, x_295);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(0, 1, 0);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_297);
return x_298;
}
else
{
lean_dec(x_293);
lean_dec(x_290);
lean_dec(x_284);
return x_294;
}
}
else
{
lean_object* x_299; 
lean_dec(x_290);
lean_dec_ref(x_286);
lean_dec(x_284);
lean_dec(x_3);
x_299 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_299;
}
}
else
{
lean_object* x_300; 
lean_dec_ref(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_3);
x_300 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_300;
}
}
}
case 9:
{
uint8_t x_301; 
x_301 = !lean_is_exclusive(x_2);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; 
x_302 = lean_ctor_get(x_2, 0);
x_303 = lean_ctor_get(x_2, 1);
x_304 = lean_ctor_get(x_2, 2);
x_305 = lean_ctor_get(x_2, 3);
x_306 = lean_ctor_get(x_2, 4);
x_307 = lean_ctor_get(x_2, 5);
x_308 = lean_st_ref_get(x_3);
x_309 = 1;
x_310 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_308, x_302, x_309);
lean_dec(x_308);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
lean_dec_ref(x_310);
x_312 = lean_st_ref_get(x_3);
x_313 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_312, x_305, x_309);
lean_dec(x_312);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
lean_dec_ref(x_313);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_315 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_306, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_317 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_307, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_317) == 0)
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_317, 0);
lean_ctor_set(x_2, 5, x_319);
lean_ctor_set(x_2, 4, x_316);
lean_ctor_set(x_2, 3, x_314);
lean_ctor_set(x_2, 0, x_311);
lean_ctor_set(x_317, 0, x_2);
return x_317;
}
else
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_317, 0);
lean_inc(x_320);
lean_dec(x_317);
lean_ctor_set(x_2, 5, x_320);
lean_ctor_set(x_2, 4, x_316);
lean_ctor_set(x_2, 3, x_314);
lean_ctor_set(x_2, 0, x_311);
x_321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_321, 0, x_2);
return x_321;
}
}
else
{
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_311);
lean_free_object(x_2);
lean_dec(x_304);
lean_dec(x_303);
return x_317;
}
}
else
{
uint8_t x_322; 
lean_dec(x_314);
lean_dec(x_311);
lean_free_object(x_2);
lean_dec_ref(x_307);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_322 = !lean_is_exclusive(x_315);
if (x_322 == 0)
{
return x_315;
}
else
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_315, 0);
lean_inc(x_323);
lean_dec(x_315);
x_324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_324, 0, x_323);
return x_324;
}
}
}
else
{
lean_object* x_325; 
lean_dec(x_311);
lean_free_object(x_2);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_3);
x_325 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_325;
}
}
else
{
lean_object* x_326; 
lean_free_object(x_2);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_3);
x_326 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; 
x_327 = lean_ctor_get(x_2, 0);
x_328 = lean_ctor_get(x_2, 1);
x_329 = lean_ctor_get(x_2, 2);
x_330 = lean_ctor_get(x_2, 3);
x_331 = lean_ctor_get(x_2, 4);
x_332 = lean_ctor_get(x_2, 5);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_2);
x_333 = lean_st_ref_get(x_3);
x_334 = 1;
x_335 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_333, x_327, x_334);
lean_dec(x_333);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
lean_dec_ref(x_335);
x_337 = lean_st_ref_get(x_3);
x_338 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_337, x_330, x_334);
lean_dec(x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_340 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_331, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
lean_dec_ref(x_340);
x_342 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_332, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_344 = x_342;
} else {
 lean_dec_ref(x_342);
 x_344 = lean_box(0);
}
x_345 = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(x_345, 0, x_336);
lean_ctor_set(x_345, 1, x_328);
lean_ctor_set(x_345, 2, x_329);
lean_ctor_set(x_345, 3, x_339);
lean_ctor_set(x_345, 4, x_341);
lean_ctor_set(x_345, 5, x_343);
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(0, 1, 0);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_345);
return x_346;
}
else
{
lean_dec(x_341);
lean_dec(x_339);
lean_dec(x_336);
lean_dec(x_329);
lean_dec(x_328);
return x_342;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_339);
lean_dec(x_336);
lean_dec_ref(x_332);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_347 = lean_ctor_get(x_340, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 x_348 = x_340;
} else {
 lean_dec_ref(x_340);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 1, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_347);
return x_349;
}
}
else
{
lean_object* x_350; 
lean_dec(x_336);
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_3);
x_350 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_350;
}
}
else
{
lean_object* x_351; 
lean_dec_ref(x_332);
lean_dec_ref(x_331);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_3);
x_351 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_351;
}
}
}
case 10:
{
uint8_t x_352; 
x_352 = !lean_is_exclusive(x_2);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; 
x_353 = lean_ctor_get(x_2, 0);
x_354 = lean_ctor_get(x_2, 1);
x_355 = lean_ctor_get(x_2, 2);
x_356 = lean_st_ref_get(x_3);
x_357 = 1;
x_358 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_356, x_353, x_357);
lean_dec(x_356);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
lean_dec_ref(x_358);
x_360 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_355, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_360) == 0)
{
uint8_t x_361; 
x_361 = !lean_is_exclusive(x_360);
if (x_361 == 0)
{
lean_object* x_362; 
x_362 = lean_ctor_get(x_360, 0);
lean_ctor_set(x_2, 2, x_362);
lean_ctor_set(x_2, 0, x_359);
lean_ctor_set(x_360, 0, x_2);
return x_360;
}
else
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_360, 0);
lean_inc(x_363);
lean_dec(x_360);
lean_ctor_set(x_2, 2, x_363);
lean_ctor_set(x_2, 0, x_359);
x_364 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_364, 0, x_2);
return x_364;
}
}
else
{
lean_dec(x_359);
lean_free_object(x_2);
lean_dec(x_354);
return x_360;
}
}
else
{
lean_object* x_365; 
lean_free_object(x_2);
lean_dec_ref(x_355);
lean_dec(x_354);
lean_dec(x_3);
x_365 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_365;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; 
x_366 = lean_ctor_get(x_2, 0);
x_367 = lean_ctor_get(x_2, 1);
x_368 = lean_ctor_get(x_2, 2);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_2);
x_369 = lean_st_ref_get(x_3);
x_370 = 1;
x_371 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_369, x_366, x_370);
lean_dec(x_369);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
lean_dec_ref(x_371);
x_373 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_368, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 x_375 = x_373;
} else {
 lean_dec_ref(x_373);
 x_375 = lean_box(0);
}
x_376 = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(x_376, 0, x_372);
lean_ctor_set(x_376, 1, x_367);
lean_ctor_set(x_376, 2, x_374);
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(0, 1, 0);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_376);
return x_377;
}
else
{
lean_dec(x_372);
lean_dec(x_367);
return x_373;
}
}
else
{
lean_object* x_378; 
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_3);
x_378 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_378;
}
}
}
case 11:
{
uint8_t x_379; 
x_379 = !lean_is_exclusive(x_2);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; 
x_380 = lean_ctor_get(x_2, 0);
x_381 = lean_ctor_get(x_2, 1);
x_382 = lean_ctor_get(x_2, 2);
x_383 = lean_st_ref_get(x_3);
x_384 = 1;
x_385 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_383, x_380, x_384);
lean_dec(x_383);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
lean_dec_ref(x_385);
x_387 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_382, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_387) == 0)
{
uint8_t x_388; 
x_388 = !lean_is_exclusive(x_387);
if (x_388 == 0)
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_387, 0);
lean_ctor_set(x_2, 2, x_389);
lean_ctor_set(x_2, 0, x_386);
lean_ctor_set(x_387, 0, x_2);
return x_387;
}
else
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_387, 0);
lean_inc(x_390);
lean_dec(x_387);
lean_ctor_set(x_2, 2, x_390);
lean_ctor_set(x_2, 0, x_386);
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_2);
return x_391;
}
}
else
{
lean_dec(x_386);
lean_free_object(x_2);
lean_dec(x_381);
return x_387;
}
}
else
{
lean_object* x_392; 
lean_free_object(x_2);
lean_dec_ref(x_382);
lean_dec(x_381);
lean_dec(x_3);
x_392 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; uint8_t x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; 
x_393 = lean_ctor_get(x_2, 0);
x_394 = lean_ctor_get(x_2, 1);
x_395 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_396 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_397 = lean_ctor_get(x_2, 2);
lean_inc(x_397);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_2);
x_398 = lean_st_ref_get(x_3);
x_399 = 1;
x_400 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_398, x_393, x_399);
lean_dec(x_398);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
x_402 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_397, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 x_404 = x_402;
} else {
 lean_dec_ref(x_402);
 x_404 = lean_box(0);
}
x_405 = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(x_405, 0, x_401);
lean_ctor_set(x_405, 1, x_394);
lean_ctor_set(x_405, 2, x_403);
lean_ctor_set_uint8(x_405, sizeof(void*)*3, x_395);
lean_ctor_set_uint8(x_405, sizeof(void*)*3 + 1, x_396);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(0, 1, 0);
} else {
 x_406 = x_404;
}
lean_ctor_set(x_406, 0, x_405);
return x_406;
}
else
{
lean_dec(x_401);
lean_dec(x_394);
return x_402;
}
}
else
{
lean_object* x_407; 
lean_dec_ref(x_397);
lean_dec(x_394);
lean_dec(x_3);
x_407 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_407;
}
}
}
case 12:
{
uint8_t x_408; 
x_408 = !lean_is_exclusive(x_2);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_409 = lean_ctor_get(x_2, 0);
x_410 = lean_ctor_get(x_2, 1);
x_411 = lean_ctor_get(x_2, 2);
x_412 = lean_st_ref_get(x_3);
x_413 = 1;
x_414 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_412, x_409, x_413);
lean_dec(x_412);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
lean_dec_ref(x_414);
x_416 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_411, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_416) == 0)
{
uint8_t x_417; 
x_417 = !lean_is_exclusive(x_416);
if (x_417 == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_416, 0);
lean_ctor_set(x_2, 2, x_418);
lean_ctor_set(x_2, 0, x_415);
lean_ctor_set(x_416, 0, x_2);
return x_416;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_416, 0);
lean_inc(x_419);
lean_dec(x_416);
lean_ctor_set(x_2, 2, x_419);
lean_ctor_set(x_2, 0, x_415);
x_420 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_420, 0, x_2);
return x_420;
}
}
else
{
lean_dec(x_415);
lean_free_object(x_2);
lean_dec(x_410);
return x_416;
}
}
else
{
lean_object* x_421; 
lean_free_object(x_2);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec(x_3);
x_421 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_421;
}
}
else
{
lean_object* x_422; lean_object* x_423; uint8_t x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; lean_object* x_429; 
x_422 = lean_ctor_get(x_2, 0);
x_423 = lean_ctor_get(x_2, 1);
x_424 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_425 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_426 = lean_ctor_get(x_2, 2);
lean_inc(x_426);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_2);
x_427 = lean_st_ref_get(x_3);
x_428 = 1;
x_429 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_427, x_422, x_428);
lean_dec(x_427);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
lean_dec_ref(x_429);
x_431 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_426, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 x_433 = x_431;
} else {
 lean_dec_ref(x_431);
 x_433 = lean_box(0);
}
x_434 = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(x_434, 0, x_430);
lean_ctor_set(x_434, 1, x_423);
lean_ctor_set(x_434, 2, x_432);
lean_ctor_set_uint8(x_434, sizeof(void*)*3, x_424);
lean_ctor_set_uint8(x_434, sizeof(void*)*3 + 1, x_425);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(0, 1, 0);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_434);
return x_435;
}
else
{
lean_dec(x_430);
lean_dec(x_423);
return x_431;
}
}
else
{
lean_object* x_436; 
lean_dec_ref(x_426);
lean_dec(x_423);
lean_dec(x_3);
x_436 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_436;
}
}
}
default: 
{
uint8_t x_437; 
x_437 = !lean_is_exclusive(x_2);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; 
x_438 = lean_ctor_get(x_2, 0);
x_439 = lean_ctor_get(x_2, 1);
x_440 = lean_st_ref_get(x_3);
x_441 = 1;
x_442 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_440, x_438, x_441);
lean_dec(x_440);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
lean_dec_ref(x_442);
x_444 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_439, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_444) == 0)
{
uint8_t x_445; 
x_445 = !lean_is_exclusive(x_444);
if (x_445 == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_444, 0);
lean_ctor_set(x_2, 1, x_446);
lean_ctor_set(x_2, 0, x_443);
lean_ctor_set(x_444, 0, x_2);
return x_444;
}
else
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_444, 0);
lean_inc(x_447);
lean_dec(x_444);
lean_ctor_set(x_2, 1, x_447);
lean_ctor_set(x_2, 0, x_443);
x_448 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_448, 0, x_2);
return x_448;
}
}
else
{
lean_dec(x_443);
lean_free_object(x_2);
return x_444;
}
}
else
{
lean_object* x_449; 
lean_free_object(x_2);
lean_dec_ref(x_439);
lean_dec(x_3);
x_449 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_449;
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; lean_object* x_454; 
x_450 = lean_ctor_get(x_2, 0);
x_451 = lean_ctor_get(x_2, 1);
lean_inc(x_451);
lean_inc(x_450);
lean_dec(x_2);
x_452 = lean_st_ref_get(x_3);
x_453 = 1;
x_454 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_452, x_450, x_453);
lean_dec(x_452);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
lean_dec_ref(x_454);
x_456 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_451, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
x_459 = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(x_459, 0, x_455);
lean_ctor_set(x_459, 1, x_457);
if (lean_is_scalar(x_458)) {
 x_460 = lean_alloc_ctor(0, 1, 0);
} else {
 x_460 = x_458;
}
lean_ctor_set(x_460, 0, x_459);
return x_460;
}
else
{
lean_dec(x_455);
return x_456;
}
}
else
{
lean_object* x_461; 
lean_dec_ref(x_451);
lean_dec(x_3);
x_461 = l_Lean_Compiler_LCNF_mkReturnErased(x_1, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_461;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_15 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_11, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_array_size(x_12);
x_20 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_21 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_1, x_19, x_20, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_23 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_st_ref_take(x_5);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
lean_ctor_set(x_2, 4, x_24);
lean_ctor_set(x_2, 3, x_16);
lean_ctor_set(x_2, 2, x_22);
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_2, 0, x_27);
lean_inc_ref(x_2);
x_31 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_1, x_30, x_2);
lean_ctor_set(x_28, 0, x_31);
x_32 = lean_st_ref_set(x_5, x_28);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
lean_ctor_set(x_2, 4, x_24);
lean_ctor_set(x_2, 3, x_16);
lean_ctor_set(x_2, 2, x_22);
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_2, 0, x_27);
lean_inc_ref(x_2);
x_35 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_1, x_33, x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_st_ref_set(x_5, x_36);
lean_dec(x_5);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_st_ref_take(x_5);
x_40 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
lean_ctor_set(x_2, 4, x_24);
lean_ctor_set(x_2, 3, x_16);
lean_ctor_set(x_2, 2, x_22);
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_2, 0, x_38);
lean_inc_ref(x_2);
x_43 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_1, x_40, x_2);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_st_ref_set(x_5, x_44);
lean_dec(x_5);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_2);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
return x_25;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_25, 0);
lean_inc(x_48);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
return x_23;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_23, 0);
lean_inc(x_51);
lean_dec(x_23);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_18);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_21);
if (x_53 == 0)
{
return x_21;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_21, 0);
lean_inc(x_54);
lean_dec(x_21);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_16);
lean_free_object(x_2);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_17);
if (x_56 == 0)
{
return x_17;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_17, 0);
lean_inc(x_57);
lean_dec(x_17);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_free_object(x_2);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
return x_15;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_15, 0);
lean_inc(x_60);
lean_dec(x_15);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
x_64 = lean_ctor_get(x_2, 2);
x_65 = lean_ctor_get(x_2, 3);
x_66 = lean_ctor_get(x_2, 4);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_67 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_65, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___redArg(x_63, x_5);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_array_size(x_64);
x_72 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_73 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_1, x_71, x_72, x_64, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_75 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_66, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___redArg(x_62, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_st_ref_take(x_5);
x_81 = lean_ctor_get(x_80, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_70);
lean_ctor_set(x_84, 2, x_74);
lean_ctor_set(x_84, 3, x_68);
lean_ctor_set(x_84, 4, x_76);
lean_inc_ref(x_84);
x_85 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_1, x_81, x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
x_87 = lean_st_ref_set(x_5, x_86);
lean_dec(x_5);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(0, 1, 0);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_84);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_5);
x_89 = lean_ctor_get(x_77, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_90 = x_77;
} else {
 lean_dec_ref(x_77);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_74);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_62);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_92 = lean_ctor_get(x_75, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_93 = x_75;
} else {
 lean_dec_ref(x_75);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec_ref(x_66);
lean_dec(x_62);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_95 = lean_ctor_get(x_73, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_96 = x_73;
} else {
 lean_dec_ref(x_73);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_68);
lean_dec_ref(x_66);
lean_dec_ref(x_64);
lean_dec(x_62);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_98 = lean_ctor_get(x_69, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_99 = x_69;
} else {
 lean_dec_ref(x_69);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_66);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_101 = lean_ctor_get(x_67, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_102 = x_67;
} else {
 lean_dec_ref(x_67);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeCode_spec__2(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 1);
lean_dec(x_19);
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_16);
lean_ctor_set(x_12, 4, x_25);
lean_ctor_set(x_12, 3, x_26);
lean_ctor_set(x_12, 2, x_27);
lean_ctor_set(x_12, 1, x_20);
lean_ctor_set(x_12, 0, x_24);
lean_ctor_set(x_10, 1, x_21);
x_28 = l_ReaderT_instMonad___redArg(x_10);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_37 = lean_ctor_get(x_30, 1);
lean_dec(x_37);
x_38 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_39 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_34);
lean_ctor_set(x_30, 4, x_43);
lean_ctor_set(x_30, 3, x_44);
lean_ctor_set(x_30, 2, x_45);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set(x_28, 1, x_39);
x_46 = l_ReaderT_instMonad___redArg(x_28);
x_47 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(x_1);
x_48 = l_instInhabitedOfMonad___redArg(x_46, x_47);
x_49 = lean_panic_fn(x_48, x_2);
x_50 = lean_apply_6(x_49, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_51 = lean_ctor_get(x_30, 0);
x_52 = lean_ctor_get(x_30, 2);
x_53 = lean_ctor_get(x_30, 3);
x_54 = lean_ctor_get(x_30, 4);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_30);
x_55 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_56 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_51);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_57, 0, x_51);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_58, 0, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_60, 0, x_54);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_61, 0, x_53);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_62, 0, x_52);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_55);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_61);
lean_ctor_set(x_63, 4, x_60);
lean_ctor_set(x_28, 1, x_56);
lean_ctor_set(x_28, 0, x_63);
x_64 = l_ReaderT_instMonad___redArg(x_28);
x_65 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(x_1);
x_66 = l_instInhabitedOfMonad___redArg(x_64, x_65);
x_67 = lean_panic_fn(x_66, x_2);
x_68 = lean_apply_6(x_67, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_69 = lean_ctor_get(x_28, 0);
lean_inc(x_69);
lean_dec(x_28);
x_70 = lean_ctor_get(x_69, 0);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_69, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 4);
lean_inc(x_73);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 lean_ctor_release(x_69, 4);
 x_74 = x_69;
} else {
 lean_dec_ref(x_69);
 x_74 = lean_box(0);
}
x_75 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_76 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_70);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_77, 0, x_70);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_78, 0, x_70);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_80, 0, x_73);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_81, 0, x_72);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_82, 0, x_71);
if (lean_is_scalar(x_74)) {
 x_83 = lean_alloc_ctor(0, 5, 0);
} else {
 x_83 = x_74;
}
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_75);
lean_ctor_set(x_83, 2, x_82);
lean_ctor_set(x_83, 3, x_81);
lean_ctor_set(x_83, 4, x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
x_85 = l_ReaderT_instMonad___redArg(x_84);
x_86 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(x_1);
x_87 = l_instInhabitedOfMonad___redArg(x_85, x_86);
x_88 = lean_panic_fn(x_87, x_2);
x_89 = lean_apply_6(x_88, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_90 = lean_ctor_get(x_12, 0);
x_91 = lean_ctor_get(x_12, 2);
x_92 = lean_ctor_get(x_12, 3);
x_93 = lean_ctor_get(x_12, 4);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_12);
x_94 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
x_95 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(x_90);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_96, 0, x_90);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_97, 0, x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_99, 0, x_93);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_100, 0, x_92);
x_101 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_101, 0, x_91);
x_102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_94);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set(x_102, 3, x_100);
lean_ctor_set(x_102, 4, x_99);
lean_ctor_set(x_10, 1, x_95);
lean_ctor_set(x_10, 0, x_102);
x_103 = l_ReaderT_instMonad___redArg(x_10);
x_104 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_104, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_104, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 3);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 4);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 lean_ctor_release(x_104, 3);
 lean_ctor_release(x_104, 4);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
x_111 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_112 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_106);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_113, 0, x_106);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_114, 0, x_106);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_116, 0, x_109);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_117, 0, x_108);
x_118 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_118, 0, x_107);
if (lean_is_scalar(x_110)) {
 x_119 = lean_alloc_ctor(0, 5, 0);
} else {
 x_119 = x_110;
}
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_119, 3, x_117);
lean_ctor_set(x_119, 4, x_116);
if (lean_is_scalar(x_105)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_105;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_112);
x_121 = l_ReaderT_instMonad___redArg(x_120);
x_122 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(x_1);
x_123 = l_instInhabitedOfMonad___redArg(x_121, x_122);
x_124 = lean_panic_fn(x_123, x_2);
x_125 = lean_apply_6(x_124, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_126 = lean_ctor_get(x_10, 0);
lean_inc(x_126);
lean_dec(x_10);
x_127 = lean_ctor_get(x_126, 0);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_126, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 4);
lean_inc(x_130);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 lean_ctor_release(x_126, 4);
 x_131 = x_126;
} else {
 lean_dec_ref(x_126);
 x_131 = lean_box(0);
}
x_132 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__1));
x_133 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__2));
lean_inc_ref(x_127);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_134, 0, x_127);
x_135 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_135, 0, x_127);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_137, 0, x_130);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_138, 0, x_129);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_139, 0, x_128);
if (lean_is_scalar(x_131)) {
 x_140 = lean_alloc_ctor(0, 5, 0);
} else {
 x_140 = x_131;
}
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_132);
lean_ctor_set(x_140, 2, x_139);
lean_ctor_set(x_140, 3, x_138);
lean_ctor_set(x_140, 4, x_137);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_133);
x_142 = l_ReaderT_instMonad___redArg(x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_143, 0);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_143, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 4);
lean_inc(x_148);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 x_149 = x_143;
} else {
 lean_dec_ref(x_143);
 x_149 = lean_box(0);
}
x_150 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__3));
x_151 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go_spec__2___closed__4));
lean_inc_ref(x_145);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_152, 0, x_145);
x_153 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_153, 0, x_145);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_155, 0, x_148);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_156, 0, x_147);
x_157 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_157, 0, x_146);
if (lean_is_scalar(x_149)) {
 x_158 = lean_alloc_ctor(0, 5, 0);
} else {
 x_158 = x_149;
}
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_150);
lean_ctor_set(x_158, 2, x_157);
lean_ctor_set(x_158, 3, x_156);
lean_ctor_set(x_158, 4, x_155);
if (lean_is_scalar(x_144)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_144;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_151);
x_160 = l_ReaderT_instMonad___redArg(x_159);
x_161 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(x_1);
x_162 = l_instInhabitedOfMonad___redArg(x_160, x_161);
x_163 = lean_panic_fn(x_162, x_2);
x_164 = lean_apply_6(x_163, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_164;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__2));
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(199u);
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
x_3 = lean_unsigned_to_nat(204u);
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
x_3 = lean_unsigned_to_nat(203u);
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
x_3 = lean_unsigned_to_nat(208u);
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
x_3 = lean_unsigned_to_nat(207u);
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
x_3 = lean_unsigned_to_nat(212u);
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
x_3 = lean_unsigned_to_nat(215u);
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
x_3 = lean_unsigned_to_nat(218u);
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
x_3 = lean_unsigned_to_nat(221u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_1, x_19, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_21);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_26 = x_20;
} else {
 lean_dec_ref(x_20);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
case 1:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_29, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_ctor_set(x_2, 0, x_32);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_2, 0, x_33);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_2);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_2);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_dec(x_2);
x_39 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_38, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_40);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
return x_46;
}
}
}
case 2:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_48, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_ctor_set(x_2, 0, x_51);
lean_ctor_set(x_49, 0, x_2);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
lean_ctor_set(x_2, 0, x_52);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_2);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_free_object(x_2);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
lean_dec(x_2);
x_58 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_57, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_59);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_64 = x_58;
} else {
 lean_dec_ref(x_58);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
}
case 3:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_2);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get(x_2, 1);
x_69 = lean_ctor_get(x_2, 2);
x_70 = lean_st_ref_get(x_3);
x_71 = 1;
x_72 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_70, x_67, x_71);
lean_dec(x_70);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_76 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_1, x_75, x_69, x_71);
lean_dec(x_75);
lean_ctor_set(x_2, 2, x_76);
lean_ctor_set(x_2, 0, x_74);
lean_ctor_set(x_72, 0, x_2);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_79 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_1, x_78, x_69, x_71);
lean_dec(x_78);
lean_ctor_set(x_2, 2, x_79);
lean_ctor_set(x_2, 0, x_77);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_2);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_72);
lean_free_object(x_2);
lean_dec(x_69);
lean_dec(x_68);
x_81 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
x_82 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_81, x_3, x_4, x_5, x_6, x_7);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_ctor_get(x_2, 1);
x_85 = lean_ctor_get(x_2, 2);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_2);
x_86 = lean_st_ref_get(x_3);
x_87 = 1;
x_88 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_86, x_83, x_87);
lean_dec(x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_92 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_1, x_91, x_85, x_87);
lean_dec(x_91);
x_93 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_84);
lean_ctor_set(x_93, 2, x_92);
if (lean_is_scalar(x_90)) {
 x_94 = lean_alloc_ctor(0, 1, 0);
} else {
 x_94 = x_90;
}
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_84);
x_95 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__1);
x_96 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_95, x_3, x_4, x_5, x_6, x_7);
return x_96;
}
}
}
case 4:
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_2);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_2, 0);
x_99 = lean_ctor_get(x_2, 1);
x_100 = lean_ctor_get(x_2, 2);
x_101 = lean_st_ref_get(x_3);
x_102 = 1;
x_103 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_101, x_98, x_102);
lean_dec(x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_st_ref_get(x_3);
x_106 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_105, x_100, x_102);
lean_dec(x_105);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_106, 0);
lean_ctor_set(x_2, 2, x_108);
lean_ctor_set(x_2, 0, x_104);
lean_ctor_set(x_106, 0, x_2);
return x_106;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
lean_dec(x_106);
lean_ctor_set(x_2, 2, x_109);
lean_ctor_set(x_2, 0, x_104);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_2);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_106);
lean_dec(x_104);
lean_free_object(x_2);
lean_dec(x_99);
x_111 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
x_112 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_111, x_3, x_4, x_5, x_6, x_7);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_103);
lean_free_object(x_2);
lean_dec(x_100);
lean_dec(x_99);
x_113 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
x_114 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_113, x_3, x_4, x_5, x_6, x_7);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_2, 0);
x_116 = lean_ctor_get(x_2, 1);
x_117 = lean_ctor_get(x_2, 2);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_2);
x_118 = lean_st_ref_get(x_3);
x_119 = 1;
x_120 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_118, x_115, x_119);
lean_dec(x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = lean_st_ref_get(x_3);
x_123 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_122, x_117, x_119);
lean_dec(x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_126, 0, x_121);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_124);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_116);
x_128 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__2);
x_129 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_128, x_3, x_4, x_5, x_6, x_7);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_120);
lean_dec(x_117);
lean_dec(x_116);
x_130 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__3);
x_131 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_130, x_3, x_4, x_5, x_6, x_7);
return x_131;
}
}
}
case 5:
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_2);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_133 = lean_ctor_get(x_2, 0);
x_134 = lean_ctor_get(x_2, 1);
x_135 = lean_ctor_get(x_2, 2);
x_136 = lean_ctor_get(x_2, 3);
x_137 = lean_ctor_get(x_2, 4);
x_138 = lean_st_ref_get(x_3);
x_139 = 1;
x_140 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_138, x_133, x_139);
lean_dec(x_138);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_st_ref_get(x_3);
x_143 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_142, x_136, x_139);
lean_dec(x_142);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_147 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1, x_146, x_139, x_137);
lean_dec(x_146);
lean_ctor_set(x_2, 4, x_147);
lean_ctor_set(x_2, 3, x_145);
lean_ctor_set(x_2, 0, x_141);
lean_ctor_set(x_143, 0, x_2);
return x_143;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_143, 0);
lean_inc(x_148);
lean_dec(x_143);
x_149 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_150 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1, x_149, x_139, x_137);
lean_dec(x_149);
lean_ctor_set(x_2, 4, x_150);
lean_ctor_set(x_2, 3, x_148);
lean_ctor_set(x_2, 0, x_141);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_2);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_143);
lean_dec(x_141);
lean_free_object(x_2);
lean_dec_ref(x_137);
lean_dec(x_135);
lean_dec(x_134);
x_152 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
x_153 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_152, x_3, x_4, x_5, x_6, x_7);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_140);
lean_free_object(x_2);
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
x_154 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
x_155 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_154, x_3, x_4, x_5, x_6, x_7);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; 
x_156 = lean_ctor_get(x_2, 0);
x_157 = lean_ctor_get(x_2, 1);
x_158 = lean_ctor_get(x_2, 2);
x_159 = lean_ctor_get(x_2, 3);
x_160 = lean_ctor_get(x_2, 4);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_2);
x_161 = lean_st_ref_get(x_3);
x_162 = 1;
x_163 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_161, x_156, x_162);
lean_dec(x_161);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = lean_st_ref_get(x_3);
x_166 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_165, x_159, x_162);
lean_dec(x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
x_169 = lean_st_ref_get(x_3);
lean_dec(x_3);
x_170 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_1, x_169, x_162, x_160);
lean_dec(x_169);
x_171 = lean_alloc_ctor(5, 5, 0);
lean_ctor_set(x_171, 0, x_164);
lean_ctor_set(x_171, 1, x_157);
lean_ctor_set(x_171, 2, x_158);
lean_ctor_set(x_171, 3, x_167);
lean_ctor_set(x_171, 4, x_170);
if (lean_is_scalar(x_168)) {
 x_172 = lean_alloc_ctor(0, 1, 0);
} else {
 x_172 = x_168;
}
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_166);
lean_dec(x_164);
lean_dec_ref(x_160);
lean_dec(x_158);
lean_dec(x_157);
x_173 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__4);
x_174 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_173, x_3, x_4, x_5, x_6, x_7);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_163);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
x_175 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__5);
x_176 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_175, x_3, x_4, x_5, x_6, x_7);
return x_176;
}
}
}
case 6:
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_2);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; 
x_178 = lean_ctor_get(x_2, 0);
x_179 = lean_ctor_get(x_2, 1);
x_180 = lean_st_ref_get(x_3);
x_181 = 1;
x_182 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_180, x_178, x_181);
lean_dec(x_180);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_182, 0);
lean_ctor_set(x_2, 0, x_184);
lean_ctor_set(x_182, 0, x_2);
return x_182;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
lean_dec(x_182);
lean_ctor_set(x_2, 0, x_185);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_2);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_182);
lean_free_object(x_2);
lean_dec(x_179);
x_187 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
x_188 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_187, x_3, x_4, x_5, x_6, x_7);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_2, 0);
x_190 = lean_ctor_get(x_2, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_2);
x_191 = lean_st_ref_get(x_3);
x_192 = 1;
x_193 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_191, x_189, x_192);
lean_dec(x_191);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
x_196 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_190);
if (lean_is_scalar(x_195)) {
 x_197 = lean_alloc_ctor(0, 1, 0);
} else {
 x_197 = x_195;
}
lean_ctor_set(x_197, 0, x_196);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_193);
lean_dec(x_190);
x_198 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__6);
x_199 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_198, x_3, x_4, x_5, x_6, x_7);
return x_199;
}
}
}
case 7:
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_2);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_2, 0);
x_202 = lean_ctor_get(x_2, 1);
x_203 = lean_st_ref_get(x_3);
x_204 = 1;
x_205 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_203, x_201, x_204);
lean_dec(x_203);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_205, 0);
lean_ctor_set(x_2, 0, x_207);
lean_ctor_set(x_205, 0, x_2);
return x_205;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
lean_dec(x_205);
lean_ctor_set(x_2, 0, x_208);
x_209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_209, 0, x_2);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_205);
lean_free_object(x_2);
lean_dec(x_202);
x_210 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
x_211 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_210, x_3, x_4, x_5, x_6, x_7);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; 
x_212 = lean_ctor_get(x_2, 0);
x_213 = lean_ctor_get(x_2, 1);
x_214 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_215 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_2);
x_216 = lean_st_ref_get(x_3);
x_217 = 1;
x_218 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_216, x_212, x_217);
lean_dec(x_216);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_220 = x_218;
} else {
 lean_dec_ref(x_218);
 x_220 = lean_box(0);
}
x_221 = lean_alloc_ctor(7, 2, 2);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_213);
lean_ctor_set_uint8(x_221, sizeof(void*)*2, x_214);
lean_ctor_set_uint8(x_221, sizeof(void*)*2 + 1, x_215);
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(0, 1, 0);
} else {
 x_222 = x_220;
}
lean_ctor_set(x_222, 0, x_221);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_218);
lean_dec(x_213);
x_223 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__7);
x_224 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_223, x_3, x_4, x_5, x_6, x_7);
return x_224;
}
}
}
case 8:
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_2);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_2, 0);
x_227 = lean_ctor_get(x_2, 1);
x_228 = lean_st_ref_get(x_3);
x_229 = 1;
x_230 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_228, x_226, x_229);
lean_dec(x_228);
if (lean_obj_tag(x_230) == 0)
{
uint8_t x_231; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_230, 0);
lean_ctor_set(x_2, 0, x_232);
lean_ctor_set(x_230, 0, x_2);
return x_230;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
lean_dec(x_230);
lean_ctor_set(x_2, 0, x_233);
x_234 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_234, 0, x_2);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_230);
lean_free_object(x_2);
lean_dec(x_227);
x_235 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
x_236 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_235, x_3, x_4, x_5, x_6, x_7);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; 
x_237 = lean_ctor_get(x_2, 0);
x_238 = lean_ctor_get(x_2, 1);
x_239 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_240 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_2);
x_241 = lean_st_ref_get(x_3);
x_242 = 1;
x_243 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_241, x_237, x_242);
lean_dec(x_241);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
x_246 = lean_alloc_ctor(8, 2, 2);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_238);
lean_ctor_set_uint8(x_246, sizeof(void*)*2, x_239);
lean_ctor_set_uint8(x_246, sizeof(void*)*2 + 1, x_240);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 1, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_246);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_243);
lean_dec(x_238);
x_248 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__8);
x_249 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_248, x_3, x_4, x_5, x_6, x_7);
return x_249;
}
}
}
default: 
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_2);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_2, 0);
x_252 = lean_st_ref_get(x_3);
x_253 = 1;
x_254 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_252, x_251, x_253);
lean_dec(x_252);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_254, 0);
lean_ctor_set(x_2, 0, x_256);
lean_ctor_set(x_254, 0, x_2);
return x_254;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_254, 0);
lean_inc(x_257);
lean_dec(x_254);
lean_ctor_set(x_2, 0, x_257);
x_258 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_258, 0, x_2);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_254);
lean_free_object(x_2);
x_259 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
x_260 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_259, x_3, x_4, x_5, x_6, x_7);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_2, 0);
lean_inc(x_261);
lean_dec(x_2);
x_262 = lean_st_ref_get(x_3);
x_263 = 1;
x_264 = l_Lean_Compiler_LCNF_normFVarImp___redArg(x_262, x_261, x_263);
lean_dec(x_262);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_266 = x_264;
} else {
 lean_dec_ref(x_264);
 x_266 = lean_box(0);
}
x_267 = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(x_267, 0, x_265);
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(0, 1, 0);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_267);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_264);
x_269 = lean_obj_once(&l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9, &l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___closed__9);
x_270 = l_panic___at___00Lean_Compiler_LCNF_Internalize_internalizeCodeDecl_spec__0(x_1, x_269, x_3, x_4, x_5, x_6, x_7);
return x_270;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_st_mk_ref(x_3);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_st_ref_get(x_9);
lean_dec(x_9);
lean_dec(x_12);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_st_ref_get(x_9);
lean_dec(x_9);
lean_dec(x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
}
else
{
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Code_internalize(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_apply_7(x_1, x_10, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_apply_7(x_1, x_19, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_21);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_26 = x_20;
} else {
 lean_dec_ref(x_20);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_2);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 2);
x_17 = lean_ctor_get(x_10, 3);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_array_size(x_17);
x_21 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_22 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_1, x_20, x_21, x_17, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_box(x_1);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 8, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(x_25, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_10, 3, x_23);
lean_ctor_set(x_10, 2, x_19);
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_26, 0, x_2);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_10, 3, x_23);
lean_ctor_set(x_10, 2, x_19);
lean_ctor_set(x_2, 1, x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_23);
lean_dec(x_19);
lean_free_object(x_10);
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_2);
lean_dec(x_13);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_free_object(x_10);
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_2);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_10);
lean_dec_ref(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_2);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
lean_dec(x_18);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
x_44 = lean_ctor_get(x_10, 2);
x_45 = lean_ctor_get(x_10, 3);
x_46 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_47 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_44, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_array_size(x_45);
x_50 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_51 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_1, x_49, x_50, x_45, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_box(x_1);
x_54 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 8, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(x_54, x_40, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_58, 0, x_42);
lean_ctor_set(x_58, 1, x_43);
lean_ctor_set(x_58, 2, x_48);
lean_ctor_set(x_58, 3, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_46);
lean_ctor_set(x_2, 1, x_56);
lean_ctor_set(x_2, 0, x_58);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_2);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_2);
lean_dec(x_41);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_2);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_63 = lean_ctor_get(x_51, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_64 = x_51;
} else {
 lean_dec_ref(x_51);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_45);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_2);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_66 = lean_ctor_get(x_47, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_67 = x_47;
} else {
 lean_dec_ref(x_47);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_2, 0);
x_70 = lean_ctor_get(x_2, 1);
x_71 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_72 = lean_ctor_get(x_2, 2);
lean_inc(x_72);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_2);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 2);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_69, 3);
lean_inc_ref(x_76);
x_77 = lean_ctor_get_uint8(x_69, sizeof(void*)*4);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 x_78 = x_69;
} else {
 lean_dec_ref(x_69);
 x_78 = lean_box(0);
}
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_79 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_internalizeExpr_go(x_1, x_75, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_array_size(x_76);
x_82 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_83 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_1, x_81, x_82, x_76, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_box(x_1);
x_86 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed), 8, 1);
lean_closure_set(x_86, 0, x_85);
x_87 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go_spec__0___redArg(x_86, x_70, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_90 = lean_alloc_ctor(0, 4, 1);
} else {
 x_90 = x_78;
}
lean_ctor_set(x_90, 0, x_73);
lean_ctor_set(x_90, 1, x_74);
lean_ctor_set(x_90, 2, x_80);
lean_ctor_set(x_90, 3, x_84);
lean_ctor_set_uint8(x_90, sizeof(void*)*4, x_77);
x_91 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
lean_ctor_set(x_91, 2, x_72);
lean_ctor_set_uint8(x_91, sizeof(void*)*3, x_71);
if (lean_is_scalar(x_89)) {
 x_92 = lean_alloc_ctor(0, 1, 0);
} else {
 x_92 = x_89;
}
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_84);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
x_93 = lean_ctor_get(x_87, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec_ref(x_70);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_96 = lean_ctor_get(x_83, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_97 = x_83;
} else {
 lean_dec_ref(x_83);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec_ref(x_70);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_99 = lean_ctor_get(x_79, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_100 = x_79;
} else {
 lean_dec_ref(x_79);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_99);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_st_mk_ref(x_3);
lean_inc(x_9);
x_10 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Decl_internalize_go(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_st_ref_get(x_9);
lean_dec(x_9);
lean_dec(x_12);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_st_ref_get(x_9);
lean_dec(x_9);
lean_dec(x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
}
else
{
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_Decl_internalize(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
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
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 1);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_12, 1, x_15);
x_16 = lean_st_ref_set(x_6, x_12);
x_17 = lean_array_uget_borrowed(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_17);
x_20 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_17, x_19, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_array_uset(x_4, x_3, x_18);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_22, x_3, x_21);
x_3 = x_24;
x_4 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_st_ref_set(x_6, x_32);
x_34 = lean_array_uget_borrowed(x_4, x_3);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_34);
x_37 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_34, x_36, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_array_uset(x_4, x_3, x_35);
x_40 = 1;
x_41 = lean_usize_add(x_3, x_40);
x_42 = lean_array_uset(x_39, x_3, x_38);
x_3 = x_41;
x_4 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
return x_46;
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 2);
lean_dec(x_7);
lean_ctor_set(x_5, 2, x_2);
x_8 = lean_st_ref_set(x_1, x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 3);
x_14 = lean_ctor_get(x_5, 4);
x_15 = lean_ctor_get(x_5, 5);
x_16 = lean_ctor_get(x_5, 6);
x_17 = lean_ctor_get(x_5, 7);
x_18 = lean_ctor_get(x_5, 8);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_2);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_15);
lean_ctor_set(x_19, 6, x_16);
lean_ctor_set(x_19, 7, x_17);
lean_ctor_set(x_19, 8, x_18);
x_20 = lean_st_ref_set(x_1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_st_ref_take(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_7, 2);
lean_dec(x_9);
x_10 = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
lean_ctor_set(x_7, 2, x_10);
x_11 = lean_st_ref_set(x_4, x_7);
x_12 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_12);
lean_dec(x_6);
x_13 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
x_14 = lean_box(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 8, 3);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_13);
x_16 = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
x_17 = 0;
lean_inc(x_4);
x_18 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_15, x_16, x_17, x_3, x_4);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_ctor_set_tag(x_18, 1);
x_21 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_4, x_12, x_18);
lean_dec_ref(x_18);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_inc(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_4, x_12, x_26);
lean_dec_ref(x_26);
lean_dec(x_4);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_28 = x_27;
} else {
 lean_dec_ref(x_27);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec_ref(x_18);
x_31 = lean_box(0);
x_32 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_4, x_12, x_31);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; 
lean_dec(x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
x_38 = lean_ctor_get(x_7, 3);
x_39 = lean_ctor_get(x_7, 4);
x_40 = lean_ctor_get(x_7, 5);
x_41 = lean_ctor_get(x_7, 6);
x_42 = lean_ctor_get(x_7, 7);
x_43 = lean_ctor_get(x_7, 8);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_44 = ((lean_object*)(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2));
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_38);
lean_ctor_set(x_45, 4, x_39);
lean_ctor_set(x_45, 5, x_40);
lean_ctor_set(x_45, 6, x_41);
lean_ctor_set(x_45, 7, x_42);
lean_ctor_set(x_45, 8, x_43);
x_46 = lean_st_ref_set(x_4, x_45);
x_47 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_47);
lean_dec(x_6);
x_48 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_cleanup_spec__0___closed__1);
x_49 = lean_box(x_1);
x_50 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 8, 3);
lean_closure_set(x_50, 0, x_49);
lean_closure_set(x_50, 1, x_2);
lean_closure_set(x_50, 2, x_48);
x_51 = lean_obj_once(&l_Lean_Compiler_LCNF_cleanup___closed__1, &l_Lean_Compiler_LCNF_cleanup___closed__1_once, _init_l_Lean_Compiler_LCNF_cleanup___closed__1);
x_52 = 0;
lean_inc(x_4);
x_53 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_50, x_51, x_52, x_3, x_4);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
lean_inc(x_54);
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_55;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_54);
x_57 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_4, x_47, x_56);
lean_dec_ref(x_56);
lean_dec(x_4);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_58 = x_57;
} else {
 lean_dec_ref(x_57);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_54);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
lean_dec_ref(x_53);
x_61 = lean_box(0);
x_62 = l_Lean_Compiler_LCNF_normalizeFVarIds___lam__0(x_4, x_47, x_61);
lean_dec(x_4);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_63 = x_62;
} else {
 lean_dec_ref(x_62);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_63;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_60);
return x_64;
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
