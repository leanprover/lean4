// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceArity
// Imports: public import Lean.Compiler.LCNF.Internalize
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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_FindUsed_visit___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0_value;
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
static lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2;
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4_value;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5;
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toArg___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_redArg"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value),LEAN_SCALAR_PTR_LITERAL(174, 35, 1, 83, 6, 52, 87, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_value;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceArity"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value),LEAN_SCALAR_PTR_LITERAL(89, 83, 236, 44, 104, 94, 232, 236)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ", used params: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14;
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_reduceArity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_reduceArity___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_reduceArity___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value),LEAN_SCALAR_PTR_LITERAL(111, 96, 179, 183, 204, 167, 118, 86)}};
static const lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_reduceArity___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_reduceArity___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_reduceArity___closed__1_value),((lean_object*)&l_Lean_Compiler_LCNF_reduceArity___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_reduceArity___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_reduceArity = (const lean_object*)&l_Lean_Compiler_LCNF_reduceArity___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ReduceArity"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 178, 137, 206, 51, 200, 236, 181)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(129, 159, 68, 131, 252, 164, 71, 68)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 21, 243, 137, 59, 198, 123, 202)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value),LEAN_SCALAR_PTR_LITERAL(14, 5, 205, 56, 180, 134, 217, 66)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 187, 228, 121, 199, 206, 240, 67)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 80, 75, 155, 170, 54, 223, 11)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 148, 104, 136, 58, 140, 43, 122)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(138, 217, 122, 183, 228, 182, 154, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value),LEAN_SCALAR_PTR_LITERAL(88, 65, 191, 26, 52, 74, 82, 47)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 252, 105, 27, 65, 1, 14, 1)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 4, 197, 254, 1, 206, 218, 250)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
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
x_19 = lean_array_uget(x_1, x_18);
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
x_38 = lean_array_uget(x_1, x_37);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_instHashableFVarId_hash(x_2);
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
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_take(x_3);
x_10 = lean_box(0);
x_11 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(x_9, x_1, x_10);
x_12 = lean_st_ref_set(x_3, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_1, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_5, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_1, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_4);
return x_20;
}
else
{
uint8_t x_21; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_4, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = lean_array_fget(x_16, x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_17, x_26);
lean_dec(x_17);
lean_ctor_set(x_4, 1, x_27);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = lean_array_uget(x_1, x_3);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_instBEqFVarId_beq(x_28, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_28, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_dec_ref(x_32);
x_8 = x_4;
x_9 = lean_box(0);
goto block_13;
}
else
{
uint8_t x_33; 
lean_dec_ref(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_dec(x_28);
x_8 = x_4;
x_9 = lean_box(0);
goto block_13;
}
}
else
{
lean_dec(x_25);
x_8 = x_4;
x_9 = lean_box(0);
goto block_13;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
x_36 = lean_array_fget(x_16, x_17);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_17, x_37);
lean_dec(x_17);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_18);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec_ref(x_36);
x_41 = lean_array_uget(x_1, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_instBEqFVarId_beq(x_40, x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_40, x_5, x_6);
if (lean_obj_tag(x_44) == 0)
{
lean_dec_ref(x_44);
x_8 = x_39;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
}
else
{
lean_dec(x_40);
x_8 = x_39;
x_9 = lean_box(0);
goto block_13;
}
}
else
{
lean_dec(x_36);
x_8 = x_39;
x_9 = lean_box(0);
goto block_13;
}
}
}
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_1);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget_borrowed(x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_13, x_3, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_14);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_8, x_16);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_17);
x_2 = x_15;
goto _start;
}
else
{
lean_free_object(x_1);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fget_borrowed(x_19, x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_25, x_3, x_4);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_26);
x_27 = lean_box(0);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_20, x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_21);
x_1 = x_30;
x_2 = x_27;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
return x_10;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_1);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget_borrowed(x_7, x_8);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_12, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_13);
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_8, x_15);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_16);
x_2 = x_14;
goto _start;
}
else
{
lean_free_object(x_1);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_fget_borrowed(x_18, x_19);
lean_inc(x_23);
x_24 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_23, x_3, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_24);
x_25 = lean_box(0);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_19, x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_20);
x_1 = x_28;
x_2 = x_25;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_9; 
lean_dec_ref(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
case 2:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec_ref(x_1);
x_17 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_16, x_2, x_3);
lean_dec_ref(x_2);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_34; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_21);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 3);
x_34 = lean_name_eq(x_20, x_22);
lean_dec(x_20);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_21);
x_37 = lean_box(0);
x_38 = lean_nat_dec_lt(x_35, x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_21);
lean_dec_ref(x_2);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_36, x_36);
if (x_40 == 0)
{
if (x_38 == 0)
{
lean_object* x_41; 
lean_dec_ref(x_21);
lean_dec_ref(x_2);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_37);
return x_41;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; 
x_42 = 0;
x_43 = lean_usize_of_nat(x_36);
x_44 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_21, x_42, x_43, x_37, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_21);
return x_44;
}
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = 0;
x_46 = lean_usize_of_nat(x_36);
x_47 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_21, x_45, x_46, x_37, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_21);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_array_get_size(x_21);
lean_inc_ref(x_21);
x_50 = l_Array_toSubarray___redArg(x_21, x_48, x_49);
x_51 = lean_array_size(x_23);
x_52 = 0;
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(x_23, x_51, x_52, x_50, x_2, x_3);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_62; uint8_t x_63; 
lean_dec_ref(x_53);
x_62 = lean_array_get_size(x_23);
x_63 = lean_nat_dec_le(x_62, x_48);
if (x_63 == 0)
{
x_54 = x_62;
x_55 = x_49;
goto block_61;
}
else
{
x_54 = x_48;
x_55 = x_49;
goto block_61;
}
block_61:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l_Array_toSubarray___redArg(x_21, x_54, x_55);
x_57 = lean_box(0);
x_58 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(x_56, x_57, x_2, x_3);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
lean_dec_ref(x_58);
x_59 = lean_array_get_size(x_23);
x_60 = lean_nat_dec_le(x_49, x_48);
if (x_60 == 0)
{
x_24 = lean_box(0);
x_25 = x_57;
x_26 = x_49;
x_27 = x_59;
goto block_33;
}
else
{
x_24 = lean_box(0);
x_25 = x_57;
x_26 = x_48;
x_27 = x_59;
goto block_33;
}
}
else
{
lean_dec_ref(x_2);
return x_58;
}
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_21);
lean_dec_ref(x_2);
x_64 = !lean_is_exclusive(x_53);
if (x_64 == 0)
{
return x_53;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_53, 0);
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
block_33:
{
lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_23);
x_28 = l_Array_toSubarray___redArg(x_23, x_26, x_27);
x_29 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(x_28, x_25, x_2, x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_25);
return x_29;
}
else
{
lean_object* x_32; 
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_25);
return x_32;
}
}
else
{
return x_29;
}
}
}
default: 
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_1);
x_69 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_67, x_2, x_3);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_array_get_size(x_68);
x_74 = lean_box(0);
x_75 = lean_nat_dec_lt(x_72, x_73);
if (x_75 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_2);
lean_ctor_set(x_69, 0, x_74);
return x_69;
}
else
{
uint8_t x_76; 
x_76 = lean_nat_dec_le(x_73, x_73);
if (x_76 == 0)
{
if (x_75 == 0)
{
lean_dec_ref(x_68);
lean_dec_ref(x_2);
lean_ctor_set(x_69, 0, x_74);
return x_69;
}
else
{
size_t x_77; size_t x_78; lean_object* x_79; 
lean_free_object(x_69);
x_77 = 0;
x_78 = lean_usize_of_nat(x_73);
x_79 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_68, x_77, x_78, x_74, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_68);
return x_79;
}
}
else
{
size_t x_80; size_t x_81; lean_object* x_82; 
lean_free_object(x_69);
x_80 = 0;
x_81 = lean_usize_of_nat(x_73);
x_82 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_68, x_80, x_81, x_74, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_68);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_69);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_array_get_size(x_68);
x_85 = lean_box(0);
x_86 = lean_nat_dec_lt(x_83, x_84);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec_ref(x_68);
lean_dec_ref(x_2);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_85);
return x_87;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_84, x_84);
if (x_88 == 0)
{
if (x_86 == 0)
{
lean_object* x_89; 
lean_dec_ref(x_68);
lean_dec_ref(x_2);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_85);
return x_89;
}
else
{
size_t x_90; size_t x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_usize_of_nat(x_84);
x_92 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_68, x_90, x_91, x_85, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_68);
return x_92;
}
}
else
{
size_t x_93; size_t x_94; lean_object* x_95; 
x_93 = 0;
x_94 = lean_usize_of_nat(x_84);
x_95 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_68, x_93, x_94, x_85, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_68);
return x_95;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(x_3, x_4, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(x_3, x_4, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_23);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_22, 3);
lean_inc(x_24);
lean_dec_ref(x_22);
lean_inc_ref(x_2);
x_25 = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(x_24, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_dec_ref(x_25);
x_1 = x_23;
goto _start;
}
else
{
lean_dec_ref(x_23);
lean_dec_ref(x_2);
return x_25;
}
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get_size(x_27);
x_30 = lean_box(0);
x_31 = lean_nat_dec_lt(x_28, x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec_ref(x_27);
lean_dec_ref(x_2);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_29, x_29);
if (x_33 == 0)
{
if (x_31 == 0)
{
lean_object* x_34; 
lean_dec_ref(x_27);
lean_dec_ref(x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_30);
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_29);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_27, x_35, x_36, x_30, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_27);
return x_37;
}
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_29);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_27, x_38, x_39, x_30, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_27);
return x_40;
}
}
}
case 4:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_41);
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 3);
lean_inc_ref(x_43);
lean_dec_ref(x_41);
x_44 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_42, x_2, x_3);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_array_get_size(x_43);
x_49 = lean_box(0);
x_50 = lean_nat_dec_lt(x_47, x_48);
if (x_50 == 0)
{
lean_dec_ref(x_43);
lean_dec_ref(x_2);
lean_ctor_set(x_44, 0, x_49);
return x_44;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
if (x_50 == 0)
{
lean_dec_ref(x_43);
lean_dec_ref(x_2);
lean_ctor_set(x_44, 0, x_49);
return x_44;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
lean_free_object(x_44);
x_52 = 0;
x_53 = lean_usize_of_nat(x_48);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_43, x_52, x_53, x_49, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_43);
return x_54;
}
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
lean_free_object(x_44);
x_55 = 0;
x_56 = lean_usize_of_nat(x_48);
x_57 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_43, x_55, x_56, x_49, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_43);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_44);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_43);
x_60 = lean_box(0);
x_61 = lean_nat_dec_lt(x_58, x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec_ref(x_43);
lean_dec_ref(x_2);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_59, x_59);
if (x_63 == 0)
{
if (x_61 == 0)
{
lean_object* x_64; 
lean_dec_ref(x_43);
lean_dec_ref(x_2);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_60);
return x_64;
}
else
{
size_t x_65; size_t x_66; lean_object* x_67; 
x_65 = 0;
x_66 = lean_usize_of_nat(x_59);
x_67 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_43, x_65, x_66, x_60, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_43);
return x_67;
}
}
else
{
size_t x_68; size_t x_69; lean_object* x_70; 
x_68 = 0;
x_69 = lean_usize_of_nat(x_59);
x_70 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_43, x_68, x_69, x_60, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_43);
return x_70;
}
}
}
}
else
{
lean_dec_ref(x_43);
lean_dec_ref(x_2);
return x_44;
}
}
case 5:
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
lean_dec_ref(x_1);
x_72 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_71, x_2, x_3);
lean_dec_ref(x_2);
return x_72;
}
case 6:
{
uint8_t x_73; 
lean_dec_ref(x_2);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_1, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_75);
return x_1;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_1);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
default: 
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_79);
lean_dec_ref(x_1);
x_9 = x_78;
x_10 = x_79;
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = lean_box(0);
goto block_21;
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_18);
lean_dec_ref(x_9);
lean_inc_ref(x_11);
x_19 = l_Lean_Compiler_LCNF_FindUsed_visit(x_18, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_19);
x_1 = x_10;
x_2 = x_11;
x_3 = x_12;
x_4 = x_13;
x_5 = x_14;
x_6 = x_15;
x_7 = x_16;
goto _start;
}
else
{
lean_dec_ref(x_11);
lean_dec_ref(x_10);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_2, x_3);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_array_uget(x_1, x_2);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_21);
lean_dec_ref(x_20);
x_12 = x_21;
goto block_18;
}
case 1:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_20);
x_12 = x_22;
goto block_18;
}
default: 
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_23);
lean_dec_ref(x_20);
x_12 = x_23;
goto block_18;
}
}
}
else
{
lean_object* x_24; 
lean_dec_ref(x_5);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_4);
return x_24;
}
block_18:
{
lean_object* x_13; 
lean_inc_ref(x_5);
x_13 = l_Lean_Compiler_LCNF_FindUsed_visit(x_12, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_14;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_FVarIdSet_insert(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_7, 3);
x_10 = lean_box(1);
x_11 = l_Lean_instEmptyCollectionFVarIdHashSet;
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get_size(x_9);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
x_12 = x_10;
goto block_25;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
if (x_28 == 0)
{
x_12 = x_10;
goto block_25;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_27);
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(x_9, x_30, x_31, x_10);
x_12 = x_32;
goto block_25;
}
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_27);
x_35 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(x_9, x_33, x_34, x_10);
x_12 = x_35;
goto block_25;
}
}
block_25:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_st_mk_ref(x_11);
x_14 = ((lean_object*)(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0));
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_12);
lean_inc(x_13);
x_16 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(x_14, x_8, x_15, x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_st_ref_get(x_13);
lean_dec(x_13);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
x_20 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_5, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_get_size(x_3);
x_21 = lean_nat_dec_lt(x_5, x_20);
if (x_21 == 0)
{
x_14 = x_4;
goto block_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_fget_borrowed(x_3, x_5);
x_23 = lean_unbox(x_22);
x_14 = x_23;
goto block_17;
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
x_6 = x_8;
goto _start;
}
block_17:
{
if (x_14 == 0)
{
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget_borrowed(x_1, x_5);
lean_inc(x_15);
x_16 = lean_array_push(x_6, x_15);
x_8 = x_16;
x_9 = lean_box(0);
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
x_9 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(x_1, x_2, x_3, x_8, x_5, x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2));
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(603u);
x_4 = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1));
x_5 = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 3)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_73 = lean_ctor_get(x_1, 1);
x_74 = lean_ctor_get(x_71, 0);
x_75 = lean_ctor_get(x_71, 2);
x_76 = lean_ctor_get(x_71, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_2, 0);
x_78 = lean_ctor_get(x_2, 1);
x_79 = lean_ctor_get(x_2, 2);
x_80 = lean_name_eq(x_74, x_77);
lean_dec(x_74);
if (x_80 == 0)
{
lean_object* x_81; 
lean_free_object(x_71);
lean_dec_ref(x_75);
lean_inc_ref(x_73);
x_81 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_73, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; size_t x_93; size_t x_94; uint8_t x_95; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_93 = lean_ptr_addr(x_73);
x_94 = lean_ptr_addr(x_82);
x_95 = lean_usize_dec_eq(x_93, x_94);
if (x_95 == 0)
{
x_84 = x_95;
goto block_92;
}
else
{
size_t x_96; uint8_t x_97; 
x_96 = lean_ptr_addr(x_70);
x_97 = lean_usize_dec_eq(x_96, x_96);
x_84 = x_97;
goto block_92;
}
block_92:
{
if (x_84 == 0)
{
uint8_t x_85; 
lean_inc_ref(x_70);
x_85 = !lean_is_exclusive(x_1);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_1, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_1, 0);
lean_dec(x_87);
lean_ctor_set(x_1, 1, x_82);
if (lean_is_scalar(x_83)) {
 x_88 = lean_alloc_ctor(0, 1, 0);
} else {
 x_88 = x_83;
}
lean_ctor_set(x_88, 0, x_1);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_70);
lean_ctor_set(x_89, 1, x_82);
if (lean_is_scalar(x_83)) {
 x_90 = lean_alloc_ctor(0, 1, 0);
} else {
 x_90 = x_83;
}
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
else
{
lean_object* x_91; 
lean_dec(x_82);
if (lean_is_scalar(x_83)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_83;
}
lean_ctor_set(x_91, 0, x_1);
return x_91;
}
}
}
else
{
lean_dec_ref(x_1);
return x_81;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_array_get_size(x_75);
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4;
x_101 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(x_75, x_98, x_79, x_80, x_99, x_100);
lean_dec_ref(x_75);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = 0;
x_104 = lean_box(0);
lean_inc(x_78);
lean_ctor_set(x_71, 2, x_102);
lean_ctor_set(x_71, 1, x_104);
lean_ctor_set(x_71, 0, x_78);
lean_inc_ref(x_70);
x_105 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_103, x_70, x_71, x_4);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
lean_inc_ref(x_73);
x_107 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_73, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; size_t x_119; size_t x_120; uint8_t x_121; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_119 = lean_ptr_addr(x_73);
x_120 = lean_ptr_addr(x_108);
x_121 = lean_usize_dec_eq(x_119, x_120);
if (x_121 == 0)
{
x_110 = x_121;
goto block_118;
}
else
{
size_t x_122; size_t x_123; uint8_t x_124; 
x_122 = lean_ptr_addr(x_70);
x_123 = lean_ptr_addr(x_106);
x_124 = lean_usize_dec_eq(x_122, x_123);
x_110 = x_124;
goto block_118;
}
block_118:
{
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_1);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_1, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_1, 0);
lean_dec(x_113);
lean_ctor_set(x_1, 1, x_108);
lean_ctor_set(x_1, 0, x_106);
if (lean_is_scalar(x_109)) {
 x_114 = lean_alloc_ctor(0, 1, 0);
} else {
 x_114 = x_109;
}
lean_ctor_set(x_114, 0, x_1);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_1);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_106);
lean_ctor_set(x_115, 1, x_108);
if (lean_is_scalar(x_109)) {
 x_116 = lean_alloc_ctor(0, 1, 0);
} else {
 x_116 = x_109;
}
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_108);
lean_dec(x_106);
if (lean_is_scalar(x_109)) {
 x_117 = lean_alloc_ctor(0, 1, 0);
} else {
 x_117 = x_109;
}
lean_ctor_set(x_117, 0, x_1);
return x_117;
}
}
}
else
{
lean_dec(x_106);
lean_dec_ref(x_1);
return x_107;
}
}
else
{
uint8_t x_125; 
lean_dec_ref(x_1);
x_125 = !lean_is_exclusive(x_105);
if (x_125 == 0)
{
return x_105;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_105, 0);
lean_inc(x_126);
lean_dec(x_105);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_free_object(x_71);
lean_dec_ref(x_1);
x_128 = !lean_is_exclusive(x_101);
if (x_128 == 0)
{
return x_101;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_101, 0);
lean_inc(x_129);
lean_dec(x_101);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_131 = lean_ctor_get(x_1, 1);
x_132 = lean_ctor_get(x_71, 0);
x_133 = lean_ctor_get(x_71, 2);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_71);
x_134 = lean_ctor_get(x_2, 0);
x_135 = lean_ctor_get(x_2, 1);
x_136 = lean_ctor_get(x_2, 2);
x_137 = lean_name_eq(x_132, x_134);
lean_dec(x_132);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec_ref(x_133);
lean_inc_ref(x_131);
x_138 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_131, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; size_t x_147; size_t x_148; uint8_t x_149; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
x_147 = lean_ptr_addr(x_131);
x_148 = lean_ptr_addr(x_139);
x_149 = lean_usize_dec_eq(x_147, x_148);
if (x_149 == 0)
{
x_141 = x_149;
goto block_146;
}
else
{
size_t x_150; uint8_t x_151; 
x_150 = lean_ptr_addr(x_70);
x_151 = lean_usize_dec_eq(x_150, x_150);
x_141 = x_151;
goto block_146;
}
block_146:
{
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_inc_ref(x_70);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_142 = x_1;
} else {
 lean_dec_ref(x_1);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_70);
lean_ctor_set(x_143, 1, x_139);
if (lean_is_scalar(x_140)) {
 x_144 = lean_alloc_ctor(0, 1, 0);
} else {
 x_144 = x_140;
}
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
else
{
lean_object* x_145; 
lean_dec(x_139);
if (lean_is_scalar(x_140)) {
 x_145 = lean_alloc_ctor(0, 1, 0);
} else {
 x_145 = x_140;
}
lean_ctor_set(x_145, 0, x_1);
return x_145;
}
}
}
else
{
lean_dec_ref(x_1);
return x_138;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_array_get_size(x_133);
x_153 = lean_unsigned_to_nat(0u);
x_154 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4;
x_155 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(x_133, x_152, x_136, x_137, x_153, x_154);
lean_dec_ref(x_133);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = 0;
x_158 = lean_box(0);
lean_inc(x_135);
x_159 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_159, 0, x_135);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_159, 2, x_156);
lean_inc_ref(x_70);
x_160 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_157, x_70, x_159, x_4);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
lean_inc_ref(x_131);
x_162 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_131, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; size_t x_171; size_t x_172; uint8_t x_173; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_171 = lean_ptr_addr(x_131);
x_172 = lean_ptr_addr(x_163);
x_173 = lean_usize_dec_eq(x_171, x_172);
if (x_173 == 0)
{
x_165 = x_173;
goto block_170;
}
else
{
size_t x_174; size_t x_175; uint8_t x_176; 
x_174 = lean_ptr_addr(x_70);
x_175 = lean_ptr_addr(x_161);
x_176 = lean_usize_dec_eq(x_174, x_175);
x_165 = x_176;
goto block_170;
}
block_170:
{
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_166 = x_1;
} else {
 lean_dec_ref(x_1);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_163);
if (lean_is_scalar(x_164)) {
 x_168 = lean_alloc_ctor(0, 1, 0);
} else {
 x_168 = x_164;
}
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
else
{
lean_object* x_169; 
lean_dec(x_163);
lean_dec(x_161);
if (lean_is_scalar(x_164)) {
 x_169 = lean_alloc_ctor(0, 1, 0);
} else {
 x_169 = x_164;
}
lean_ctor_set(x_169, 0, x_1);
return x_169;
}
}
}
else
{
lean_dec(x_161);
lean_dec_ref(x_1);
return x_162;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec_ref(x_1);
x_177 = lean_ctor_get(x_160, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_178 = x_160;
} else {
 lean_dec_ref(x_160);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec_ref(x_1);
x_180 = lean_ctor_get(x_155, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_181 = x_155;
} else {
 lean_dec_ref(x_155);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
return x_182;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_71);
x_183 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_183);
x_184 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_183, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; size_t x_196; size_t x_197; uint8_t x_198; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_186 = x_184;
} else {
 lean_dec_ref(x_184);
 x_186 = lean_box(0);
}
x_196 = lean_ptr_addr(x_183);
x_197 = lean_ptr_addr(x_185);
x_198 = lean_usize_dec_eq(x_196, x_197);
if (x_198 == 0)
{
x_187 = x_198;
goto block_195;
}
else
{
size_t x_199; uint8_t x_200; 
x_199 = lean_ptr_addr(x_70);
x_200 = lean_usize_dec_eq(x_199, x_199);
x_187 = x_200;
goto block_195;
}
block_195:
{
if (x_187 == 0)
{
uint8_t x_188; 
lean_inc_ref(x_70);
x_188 = !lean_is_exclusive(x_1);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_1, 1);
lean_dec(x_189);
x_190 = lean_ctor_get(x_1, 0);
lean_dec(x_190);
lean_ctor_set(x_1, 1, x_185);
if (lean_is_scalar(x_186)) {
 x_191 = lean_alloc_ctor(0, 1, 0);
} else {
 x_191 = x_186;
}
lean_ctor_set(x_191, 0, x_1);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_1);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_70);
lean_ctor_set(x_192, 1, x_185);
if (lean_is_scalar(x_186)) {
 x_193 = lean_alloc_ctor(0, 1, 0);
} else {
 x_193 = x_186;
}
lean_ctor_set(x_193, 0, x_192);
return x_193;
}
}
else
{
lean_object* x_194; 
lean_dec(x_185);
if (lean_is_scalar(x_186)) {
 x_194 = lean_alloc_ctor(0, 1, 0);
} else {
 x_194 = x_186;
}
lean_ctor_set(x_194, 0, x_1);
return x_194;
}
}
}
else
{
lean_dec_ref(x_1);
return x_184;
}
}
}
case 1:
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_1, 0);
x_202 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_202);
lean_inc_ref(x_201);
x_24 = x_201;
x_25 = x_202;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = lean_box(0);
goto block_69;
}
case 2:
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_1, 0);
x_204 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_204);
lean_inc_ref(x_203);
x_24 = x_203;
x_25 = x_204;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = lean_box(0);
goto block_69;
}
case 4:
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_205);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = lean_ctor_get(x_205, 1);
x_209 = lean_ctor_get(x_205, 2);
x_210 = lean_ctor_get(x_205, 3);
x_211 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_210);
x_212 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(x_211, x_210, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_212) == 0)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; size_t x_215; size_t x_216; uint8_t x_217; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = lean_ptr_addr(x_210);
lean_dec_ref(x_210);
x_216 = lean_ptr_addr(x_214);
x_217 = lean_usize_dec_eq(x_215, x_216);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_1);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_1, 0);
lean_dec(x_219);
lean_ctor_set(x_205, 3, x_214);
lean_ctor_set(x_212, 0, x_1);
return x_212;
}
else
{
lean_object* x_220; 
lean_dec(x_1);
lean_ctor_set(x_205, 3, x_214);
x_220 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_220, 0, x_205);
lean_ctor_set(x_212, 0, x_220);
return x_212;
}
}
else
{
lean_dec(x_214);
lean_free_object(x_205);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec(x_207);
lean_ctor_set(x_212, 0, x_1);
return x_212;
}
}
else
{
lean_object* x_221; size_t x_222; size_t x_223; uint8_t x_224; 
x_221 = lean_ctor_get(x_212, 0);
lean_inc(x_221);
lean_dec(x_212);
x_222 = lean_ptr_addr(x_210);
lean_dec_ref(x_210);
x_223 = lean_ptr_addr(x_221);
x_224 = lean_usize_dec_eq(x_222, x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_225 = x_1;
} else {
 lean_dec_ref(x_1);
 x_225 = lean_box(0);
}
lean_ctor_set(x_205, 3, x_221);
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(4, 1, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_205);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
else
{
lean_object* x_228; 
lean_dec(x_221);
lean_free_object(x_205);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec(x_207);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_1);
return x_228;
}
}
}
else
{
uint8_t x_229; 
lean_free_object(x_205);
lean_dec_ref(x_210);
lean_dec(x_209);
lean_dec_ref(x_208);
lean_dec(x_207);
lean_dec_ref(x_1);
x_229 = !lean_is_exclusive(x_212);
if (x_229 == 0)
{
return x_212;
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_212, 0);
lean_inc(x_230);
lean_dec(x_212);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_230);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_232 = lean_ctor_get(x_205, 0);
x_233 = lean_ctor_get(x_205, 1);
x_234 = lean_ctor_get(x_205, 2);
x_235 = lean_ctor_get(x_205, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_205);
x_236 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_235);
x_237 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(x_236, x_235, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; size_t x_240; size_t x_241; uint8_t x_242; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
x_240 = lean_ptr_addr(x_235);
lean_dec_ref(x_235);
x_241 = lean_ptr_addr(x_238);
x_242 = lean_usize_dec_eq(x_240, x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_243 = x_1;
} else {
 lean_dec_ref(x_1);
 x_243 = lean_box(0);
}
x_244 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_244, 0, x_232);
lean_ctor_set(x_244, 1, x_233);
lean_ctor_set(x_244, 2, x_234);
lean_ctor_set(x_244, 3, x_238);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(4, 1, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
if (lean_is_scalar(x_239)) {
 x_246 = lean_alloc_ctor(0, 1, 0);
} else {
 x_246 = x_239;
}
lean_ctor_set(x_246, 0, x_245);
return x_246;
}
else
{
lean_object* x_247; 
lean_dec(x_238);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_232);
if (lean_is_scalar(x_239)) {
 x_247 = lean_alloc_ctor(0, 1, 0);
} else {
 x_247 = x_239;
}
lean_ctor_set(x_247, 0, x_1);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec_ref(x_235);
lean_dec(x_234);
lean_dec_ref(x_233);
lean_dec(x_232);
lean_dec_ref(x_1);
x_248 = lean_ctor_get(x_237, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_249 = x_237;
} else {
 lean_dec_ref(x_237);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 1, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_248);
return x_250;
}
}
}
default: 
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_1);
return x_251;
}
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_dec_ref(x_8);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_1);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_18);
lean_dec_ref(x_16);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
}
block_69:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_24, 4);
lean_inc_ref(x_34);
x_35 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_34, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = 0;
x_38 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_37, x_24, x_33, x_32, x_36, x_28);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_40) == 0)
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ptr_addr(x_43);
x_45 = lean_ptr_addr(x_41);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
x_8 = x_39;
x_9 = lean_box(0);
x_10 = x_41;
x_11 = x_46;
goto block_15;
}
else
{
size_t x_47; size_t x_48; uint8_t x_49; 
x_47 = lean_ptr_addr(x_42);
x_48 = lean_ptr_addr(x_39);
x_49 = lean_usize_dec_eq(x_47, x_48);
x_8 = x_39;
x_9 = lean_box(0);
x_10 = x_41;
x_11 = x_49;
goto block_15;
}
}
case 2:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
lean_dec_ref(x_40);
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
x_53 = lean_ptr_addr(x_52);
x_54 = lean_ptr_addr(x_50);
x_55 = lean_usize_dec_eq(x_53, x_54);
if (x_55 == 0)
{
x_16 = x_39;
x_17 = lean_box(0);
x_18 = x_50;
x_19 = x_55;
goto block_23;
}
else
{
size_t x_56; size_t x_57; uint8_t x_58; 
x_56 = lean_ptr_addr(x_51);
x_57 = lean_ptr_addr(x_39);
x_58 = lean_usize_dec_eq(x_56, x_57);
x_16 = x_39;
x_17 = lean_box(0);
x_18 = x_50;
x_19 = x_58;
goto block_23;
}
}
default: 
{
uint8_t x_59; 
lean_dec(x_39);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_40, 0);
lean_dec(x_60);
x_61 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3;
x_62 = l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(x_61);
lean_ctor_set(x_40, 0, x_62);
return x_40;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_40);
x_63 = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3;
x_64 = l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
else
{
lean_dec(x_39);
lean_dec_ref(x_1);
return x_40;
}
}
else
{
uint8_t x_66; 
lean_dec_ref(x_25);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_38);
if (x_66 == 0)
{
return x_38;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_1);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget_borrowed(x_2, x_1);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_31);
x_13 = x_31;
goto block_30;
}
case 1:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_32);
x_13 = x_32;
goto block_30;
}
default: 
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_33);
x_13 = x_33;
goto block_30;
}
}
block_30:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_12);
x_16 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_12, x_15);
x_17 = lean_ptr_addr(x_12);
x_18 = lean_ptr_addr(x_16);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = lean_array_fset(x_2, x_1, x_16);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_1, x_24);
lean_dec(x_1);
x_1 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
x_17 = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_2);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg(x_1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 5);
x_10 = lean_st_ref_get(x_6);
x_11 = lean_st_ref_get(x_4);
x_12 = l_Lean_Compiler_LCNF_getPurity___redArg(x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2;
x_20 = lean_st_ref_take(x_6);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; double x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_unbox(x_14);
lean_dec(x_14);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17, x_25);
lean_dec_ref(x_17);
lean_inc_ref(x_8);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_8);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 0, x_27);
x_28 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3;
x_29 = 0;
x_30 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4));
x_31 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_float(x_31, sizeof(void*)*2, x_28);
lean_ctor_set_float(x_31, sizeof(void*)*2 + 8, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 16, x_29);
x_32 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5;
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_11);
lean_ctor_set(x_33, 2, x_32);
lean_inc(x_9);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_9);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_PersistentArray_push___redArg(x_24, x_34);
lean_ctor_set(x_22, 0, x_35);
x_36 = lean_st_ref_set(x_6, x_20);
x_37 = lean_box(0);
lean_ctor_set(x_12, 0, x_37);
return x_12;
}
else
{
uint64_t x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; double x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_38 = lean_ctor_get_uint64(x_22, sizeof(void*)*1);
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_unbox(x_14);
lean_dec(x_14);
x_41 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17, x_40);
lean_dec_ref(x_17);
lean_inc_ref(x_8);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_15);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_8);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 0, x_42);
x_43 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3;
x_44 = 0;
x_45 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4));
x_46 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_float(x_46, sizeof(void*)*2, x_43);
lean_ctor_set_float(x_46, sizeof(void*)*2 + 8, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 16, x_44);
x_47 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5;
x_48 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_11);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_9);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_9);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_PersistentArray_push___redArg(x_39, x_49);
x_51 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_uint64(x_51, sizeof(void*)*1, x_38);
lean_ctor_set(x_20, 4, x_51);
x_52 = lean_st_ref_set(x_6, x_20);
x_53 = lean_box(0);
lean_ctor_set(x_12, 0, x_53);
return x_12;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; double x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_54 = lean_ctor_get(x_20, 4);
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
x_57 = lean_ctor_get(x_20, 2);
x_58 = lean_ctor_get(x_20, 3);
x_59 = lean_ctor_get(x_20, 5);
x_60 = lean_ctor_get(x_20, 6);
x_61 = lean_ctor_get(x_20, 7);
x_62 = lean_ctor_get(x_20, 8);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_54);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
x_63 = lean_ctor_get_uint64(x_54, sizeof(void*)*1);
x_64 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_64);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_65 = x_54;
} else {
 lean_dec_ref(x_54);
 x_65 = lean_box(0);
}
x_66 = lean_unbox(x_14);
lean_dec(x_14);
x_67 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17, x_66);
lean_dec_ref(x_17);
lean_inc_ref(x_8);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_15);
lean_ctor_set(x_68, 1, x_19);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_8);
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 0, x_68);
x_69 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3;
x_70 = 0;
x_71 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4));
x_72 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_float(x_72, sizeof(void*)*2, x_69);
lean_ctor_set_float(x_72, sizeof(void*)*2 + 8, x_69);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 16, x_70);
x_73 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5;
x_74 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_11);
lean_ctor_set(x_74, 2, x_73);
lean_inc(x_9);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_9);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_PersistentArray_push___redArg(x_64, x_75);
if (lean_is_scalar(x_65)) {
 x_77 = lean_alloc_ctor(0, 1, 8);
} else {
 x_77 = x_65;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set_uint64(x_77, sizeof(void*)*1, x_63);
x_78 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_78, 0, x_55);
lean_ctor_set(x_78, 1, x_56);
lean_ctor_set(x_78, 2, x_57);
lean_ctor_set(x_78, 3, x_58);
lean_ctor_set(x_78, 4, x_77);
lean_ctor_set(x_78, 5, x_59);
lean_ctor_set(x_78, 6, x_60);
lean_ctor_set(x_78, 7, x_61);
lean_ctor_set(x_78, 8, x_62);
x_79 = lean_st_ref_set(x_6, x_78);
x_80 = lean_box(0);
lean_ctor_set(x_12, 0, x_80);
return x_12;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint64_t x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; double x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_81 = lean_ctor_get(x_11, 0);
lean_inc(x_81);
lean_dec(x_11);
x_82 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2;
x_83 = lean_st_ref_take(x_6);
x_84 = lean_ctor_get(x_83, 4);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_83, 0);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 2);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_83, 3);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_83, 5);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_83, 6);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_83, 7);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_83, 8);
lean_inc_ref(x_92);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 lean_ctor_release(x_83, 4);
 lean_ctor_release(x_83, 5);
 lean_ctor_release(x_83, 6);
 lean_ctor_release(x_83, 7);
 lean_ctor_release(x_83, 8);
 x_93 = x_83;
} else {
 lean_dec_ref(x_83);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get_uint64(x_84, sizeof(void*)*1);
x_95 = lean_ctor_get(x_84, 0);
lean_inc_ref(x_95);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_96 = x_84;
} else {
 lean_dec_ref(x_84);
 x_96 = lean_box(0);
}
x_97 = lean_unbox(x_14);
lean_dec(x_14);
x_98 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_81, x_97);
lean_dec_ref(x_81);
lean_inc_ref(x_8);
x_99 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_99, 0, x_15);
lean_ctor_set(x_99, 1, x_82);
lean_ctor_set(x_99, 2, x_98);
lean_ctor_set(x_99, 3, x_8);
x_100 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_2);
x_101 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3;
x_102 = 0;
x_103 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4));
x_104 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set_float(x_104, sizeof(void*)*2, x_101);
lean_ctor_set_float(x_104, sizeof(void*)*2 + 8, x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*2 + 16, x_102);
x_105 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5;
x_106 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_105);
lean_inc(x_9);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_9);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_PersistentArray_push___redArg(x_95, x_107);
if (lean_is_scalar(x_96)) {
 x_109 = lean_alloc_ctor(0, 1, 8);
} else {
 x_109 = x_96;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set_uint64(x_109, sizeof(void*)*1, x_94);
if (lean_is_scalar(x_93)) {
 x_110 = lean_alloc_ctor(0, 9, 0);
} else {
 x_110 = x_93;
}
lean_ctor_set(x_110, 0, x_85);
lean_ctor_set(x_110, 1, x_86);
lean_ctor_set(x_110, 2, x_87);
lean_ctor_set(x_110, 3, x_88);
lean_ctor_set(x_110, 4, x_109);
lean_ctor_set(x_110, 5, x_89);
lean_ctor_set(x_110, 6, x_90);
lean_ctor_set(x_110, 7, x_91);
lean_ctor_set(x_110, 8, x_92);
x_111 = lean_st_ref_set(x_6, x_110);
x_112 = lean_box(0);
lean_ctor_set(x_12, 0, x_112);
return x_12;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint64_t x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; double x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_113 = lean_ctor_get(x_12, 0);
lean_inc(x_113);
lean_dec(x_12);
x_114 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_114);
lean_dec(x_10);
x_115 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_115);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_116 = x_11;
} else {
 lean_dec_ref(x_11);
 x_116 = lean_box(0);
}
x_117 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2;
x_118 = lean_st_ref_take(x_6);
x_119 = lean_ctor_get(x_118, 4);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 2);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_118, 3);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_118, 5);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_118, 6);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_118, 7);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_118, 8);
lean_inc_ref(x_127);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 lean_ctor_release(x_118, 5);
 lean_ctor_release(x_118, 6);
 lean_ctor_release(x_118, 7);
 lean_ctor_release(x_118, 8);
 x_128 = x_118;
} else {
 lean_dec_ref(x_118);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get_uint64(x_119, sizeof(void*)*1);
x_130 = lean_ctor_get(x_119, 0);
lean_inc_ref(x_130);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_131 = x_119;
} else {
 lean_dec_ref(x_119);
 x_131 = lean_box(0);
}
x_132 = lean_unbox(x_113);
lean_dec(x_113);
x_133 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_115, x_132);
lean_dec_ref(x_115);
lean_inc_ref(x_8);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_114);
lean_ctor_set(x_134, 1, x_117);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_8);
if (lean_is_scalar(x_116)) {
 x_135 = lean_alloc_ctor(3, 2, 0);
} else {
 x_135 = x_116;
 lean_ctor_set_tag(x_135, 3);
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_2);
x_136 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3;
x_137 = 0;
x_138 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4));
x_139 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_139, 0, x_1);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_float(x_139, sizeof(void*)*2, x_136);
lean_ctor_set_float(x_139, sizeof(void*)*2 + 8, x_136);
lean_ctor_set_uint8(x_139, sizeof(void*)*2 + 16, x_137);
x_140 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5;
x_141 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_135);
lean_ctor_set(x_141, 2, x_140);
lean_inc(x_9);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_9);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_PersistentArray_push___redArg(x_130, x_142);
if (lean_is_scalar(x_131)) {
 x_144 = lean_alloc_ctor(0, 1, 8);
} else {
 x_144 = x_131;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set_uint64(x_144, sizeof(void*)*1, x_129);
if (lean_is_scalar(x_128)) {
 x_145 = lean_alloc_ctor(0, 9, 0);
} else {
 x_145 = x_128;
}
lean_ctor_set(x_145, 0, x_120);
lean_ctor_set(x_145, 1, x_121);
lean_ctor_set(x_145, 2, x_122);
lean_ctor_set(x_145, 3, x_123);
lean_ctor_set(x_145, 4, x_144);
lean_ctor_set(x_145, 5, x_124);
lean_ctor_set(x_145, 6, x_125);
lean_ctor_set(x_145, 7, x_126);
lean_ctor_set(x_145, 8, x_127);
x_146 = lean_st_ref_set(x_6, x_145);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
else
{
uint8_t x_149; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_12);
if (x_149 == 0)
{
return x_12;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_12, 0);
lean_inc(x_150);
lean_dec(x_12);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
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
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_12);
x_6 = x_15;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_12);
x_6 = x_15;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(x_1, x_2, x_8, x_4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_mkFVar(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_mkFVar(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_15, 2);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
else
{
uint8_t x_22; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_array_uget(x_1, x_3);
x_27 = lean_array_fget(x_17, x_18);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_18, x_28);
lean_dec(x_18);
lean_ctor_set(x_15, 1, x_29);
x_30 = lean_unbox(x_26);
lean_dec(x_26);
if (x_30 == 0)
{
lean_dec(x_27);
x_6 = x_4;
x_7 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Compiler_LCNF_Param_toArg___redArg(x_27);
lean_dec(x_27);
x_32 = lean_array_push(x_16, x_31);
lean_ctor_set(x_4, 1, x_32);
x_6 = x_4;
x_7 = lean_box(0);
goto block_11;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_15);
x_33 = lean_array_uget(x_1, x_3);
x_34 = lean_array_fget(x_17, x_18);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_18, x_35);
lean_dec(x_18);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_17);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_unbox(x_33);
lean_dec(x_33);
if (x_38 == 0)
{
lean_dec(x_34);
lean_ctor_set(x_4, 0, x_37);
x_6 = x_4;
x_7 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Compiler_LCNF_Param_toArg___redArg(x_34);
lean_dec(x_34);
x_40 = lean_array_push(x_16, x_39);
lean_ctor_set(x_4, 1, x_40);
lean_ctor_set(x_4, 0, x_37);
x_6 = x_4;
x_7 = lean_box(0);
goto block_11;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_4);
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_41, 2);
x_46 = lean_nat_dec_lt(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_45);
lean_inc(x_44);
lean_inc_ref(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
x_50 = lean_array_uget(x_1, x_3);
x_51 = lean_array_fget(x_43, x_44);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_44, x_52);
lean_dec(x_44);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 3, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_45);
x_55 = lean_unbox(x_50);
lean_dec(x_50);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_51);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_42);
x_6 = x_56;
x_7 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = l_Lean_Compiler_LCNF_Param_toArg___redArg(x_51);
lean_dec(x_51);
x_58 = lean_array_push(x_42, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_6 = x_59;
x_7 = lean_box(0);
goto block_11;
}
}
}
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_4 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_array_uget(x_3, x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_14 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_12, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_15);
x_2 = x_19;
x_3 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofExpr(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofExpr(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(x_1, x_7);
lean_dec(x_7);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_box(x_10);
x_14 = lean_array_uset(x_9, x_3, x_13);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(x_1, x_7);
lean_dec(x_7);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_box(x_10);
x_14 = lean_array_uset(x_9, x_3, x_13);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(x_1, x_2, x_12, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_12);
x_6 = x_15;
goto block_10;
}
else
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_11);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_12 = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; size_t x_150; lean_object* x_151; lean_object* x_152; size_t x_153; lean_object* x_154; lean_object* x_155; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; uint8_t x_202; uint8_t x_221; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_14 = x_12;
} else {
 lean_dec_ref(x_12);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_20);
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_22 = x_8;
} else {
 lean_dec_ref(x_8);
 x_22 = lean_box(0);
}
x_143 = lean_array_get_size(x_20);
x_221 = lean_nat_dec_eq(x_15, x_143);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_nat_dec_eq(x_15, x_222);
x_202 = x_223;
goto block_220;
}
else
{
x_202 = x_221;
goto block_220;
}
block_142:
{
lean_object* x_39; 
lean_inc(x_33);
lean_inc_ref(x_30);
lean_inc(x_26);
lean_inc_ref(x_34);
x_39 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_36, x_7, x_28, x_34, x_26, x_30, x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
lean_inc(x_33);
lean_inc_ref(x_30);
lean_inc(x_26);
lean_inc_ref(x_34);
x_41 = l_Lean_Compiler_LCNF_Code_inferType(x_23, x_11, x_34, x_26, x_30, x_33);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
lean_inc(x_33);
lean_inc_ref(x_30);
lean_inc(x_26);
lean_inc_ref(x_34);
lean_inc_ref(x_37);
x_43 = l_Lean_Compiler_LCNF_mkForallParams(x_23, x_37, x_42, x_34, x_26, x_30, x_33);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_box(0);
lean_inc(x_25);
if (lean_is_scalar(x_22)) {
 x_46 = lean_alloc_ctor(0, 4, 1);
} else {
 x_46 = x_22;
}
lean_ctor_set(x_46, 0, x_25);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_46, 3, x_37);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_21);
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_47, 2, x_10);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_9);
lean_inc_ref(x_47);
x_48 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_47, x_33);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_48);
x_49 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0;
lean_inc(x_27);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_27);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_st_mk_ref(x_50);
lean_inc(x_33);
lean_inc_ref(x_30);
lean_inc(x_26);
lean_inc_ref(x_34);
lean_inc(x_51);
x_52 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(x_32, x_35, x_20, x_51, x_34, x_26, x_30, x_33);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_mk_empty_array_with_capacity(x_27);
x_55 = lean_array_get_size(x_53);
lean_inc(x_53);
x_56 = l_Array_toSubarray___redArg(x_53, x_27, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_58 = lean_array_size(x_31);
x_59 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(x_31, x_58, x_35, x_57);
lean_dec_ref(x_31);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_60, 1);
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_64, 0, x_25);
lean_ctor_set(x_64, 1, x_45);
lean_ctor_set(x_64, 2, x_62);
x_65 = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
lean_inc(x_33);
lean_inc(x_26);
x_66 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_23, x_64, x_65, x_34, x_26, x_30, x_33);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_60, 1, x_69);
lean_ctor_set(x_60, 0, x_67);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_60);
x_71 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_71, 0, x_17);
lean_ctor_set(x_71, 1, x_18);
lean_ctor_set(x_71, 2, x_19);
lean_ctor_set(x_71, 3, x_53);
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_21);
x_72 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
x_73 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*3, x_29);
lean_inc_ref(x_73);
x_74 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_73, x_33);
lean_dec(x_33);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_74);
x_75 = lean_st_ref_get(x_51);
lean_dec(x_51);
lean_dec(x_75);
x_76 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_23, x_38, x_26);
lean_dec(x_26);
lean_dec_ref(x_38);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
x_80 = lean_array_push(x_79, x_47);
x_81 = lean_array_push(x_80, x_73);
lean_ctor_set(x_76, 0, x_81);
return x_76;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_76);
x_82 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
x_83 = lean_array_push(x_82, x_47);
x_84 = lean_array_push(x_83, x_73);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec_ref(x_73);
lean_dec_ref(x_47);
x_86 = !lean_is_exclusive(x_76);
if (x_86 == 0)
{
return x_76;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
lean_dec(x_76);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec_ref(x_73);
lean_dec(x_51);
lean_dec_ref(x_47);
lean_dec_ref(x_38);
lean_dec(x_26);
x_89 = !lean_is_exclusive(x_74);
if (x_89 == 0)
{
return x_74;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_74, 0);
lean_inc(x_90);
lean_dec(x_74);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_free_object(x_60);
lean_dec(x_53);
lean_dec(x_51);
lean_dec_ref(x_47);
lean_dec_ref(x_38);
lean_dec(x_33);
lean_dec(x_26);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_92 = !lean_is_exclusive(x_66);
if (x_92 == 0)
{
return x_66;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_66, 0);
lean_inc(x_93);
lean_dec(x_66);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_60, 1);
lean_inc(x_95);
lean_dec(x_60);
x_96 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_96, 0, x_25);
lean_ctor_set(x_96, 1, x_45);
lean_ctor_set(x_96, 2, x_95);
x_97 = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
lean_inc(x_33);
lean_inc(x_26);
x_98 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_23, x_96, x_97, x_34, x_26, x_30, x_33);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_104, 0, x_17);
lean_ctor_set(x_104, 1, x_18);
lean_ctor_set(x_104, 2, x_19);
lean_ctor_set(x_104, 3, x_53);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_21);
x_105 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
x_106 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_103);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*3, x_29);
lean_inc_ref(x_106);
x_107 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_106, x_33);
lean_dec(x_33);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_107);
x_108 = lean_st_ref_get(x_51);
lean_dec(x_51);
lean_dec(x_108);
x_109 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_23, x_38, x_26);
lean_dec(x_26);
lean_dec_ref(x_38);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_110 = x_109;
} else {
 lean_dec_ref(x_109);
 x_110 = lean_box(0);
}
x_111 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
x_112 = lean_array_push(x_111, x_47);
x_113 = lean_array_push(x_112, x_106);
if (lean_is_scalar(x_110)) {
 x_114 = lean_alloc_ctor(0, 1, 0);
} else {
 x_114 = x_110;
}
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_106);
lean_dec_ref(x_47);
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_106);
lean_dec(x_51);
lean_dec_ref(x_47);
lean_dec_ref(x_38);
lean_dec(x_26);
x_118 = lean_ctor_get(x_107, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_119 = x_107;
} else {
 lean_dec_ref(x_107);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec_ref(x_47);
lean_dec_ref(x_38);
lean_dec(x_33);
lean_dec(x_26);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_121 = lean_ctor_get(x_98, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_122 = x_98;
} else {
 lean_dec_ref(x_98);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec_ref(x_47);
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_124 = !lean_is_exclusive(x_59);
if (x_124 == 0)
{
return x_59;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_59, 0);
lean_inc(x_125);
lean_dec(x_59);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_51);
lean_dec_ref(x_47);
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_127 = !lean_is_exclusive(x_52);
if (x_127 == 0)
{
return x_52;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_52, 0);
lean_inc(x_128);
lean_dec(x_52);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec_ref(x_47);
lean_dec_ref(x_38);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_130 = !lean_is_exclusive(x_48);
if (x_130 == 0)
{
return x_48;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_48, 0);
lean_inc(x_131);
lean_dec(x_48);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_40);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
x_133 = !lean_is_exclusive(x_43);
if (x_133 == 0)
{
return x_43;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_43, 0);
lean_inc(x_134);
lean_dec(x_43);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_40);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
x_136 = !lean_is_exclusive(x_41);
if (x_136 == 0)
{
return x_41;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_41, 0);
lean_inc(x_137);
lean_dec(x_41);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_11);
lean_dec(x_10);
x_139 = !lean_is_exclusive(x_39);
if (x_139 == 0)
{
return x_39;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_39, 0);
lean_inc(x_140);
lean_dec(x_39);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
block_166:
{
uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_156 = 0;
x_157 = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5));
lean_inc_ref(x_151);
lean_inc(x_146);
lean_inc(x_17);
x_158 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_158, 0, x_17);
lean_ctor_set(x_158, 1, x_146);
lean_ctor_set(x_158, 2, x_151);
x_159 = lean_mk_empty_array_with_capacity(x_144);
x_160 = lean_nat_dec_lt(x_144, x_143);
if (x_160 == 0)
{
lean_dec(x_13);
x_23 = x_156;
x_24 = lean_box(0);
x_25 = x_146;
x_26 = x_149;
x_27 = x_144;
x_28 = x_158;
x_29 = x_147;
x_30 = x_148;
x_31 = x_151;
x_32 = x_150;
x_33 = x_152;
x_34 = x_154;
x_35 = x_153;
x_36 = x_157;
x_37 = x_155;
x_38 = x_159;
goto block_142;
}
else
{
uint8_t x_161; 
x_161 = lean_nat_dec_le(x_143, x_143);
if (x_161 == 0)
{
if (x_160 == 0)
{
lean_dec(x_13);
x_23 = x_156;
x_24 = lean_box(0);
x_25 = x_146;
x_26 = x_149;
x_27 = x_144;
x_28 = x_158;
x_29 = x_147;
x_30 = x_148;
x_31 = x_151;
x_32 = x_150;
x_33 = x_152;
x_34 = x_154;
x_35 = x_153;
x_36 = x_157;
x_37 = x_155;
x_38 = x_159;
goto block_142;
}
else
{
size_t x_162; lean_object* x_163; 
x_162 = lean_usize_of_nat(x_143);
x_163 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(x_13, x_20, x_153, x_162, x_159);
lean_dec(x_13);
x_23 = x_156;
x_24 = lean_box(0);
x_25 = x_146;
x_26 = x_149;
x_27 = x_144;
x_28 = x_158;
x_29 = x_147;
x_30 = x_148;
x_31 = x_151;
x_32 = x_150;
x_33 = x_152;
x_34 = x_154;
x_35 = x_153;
x_36 = x_157;
x_37 = x_155;
x_38 = x_163;
goto block_142;
}
}
else
{
size_t x_164; lean_object* x_165; 
x_164 = lean_usize_of_nat(x_143);
x_165 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(x_13, x_20, x_153, x_164, x_159);
lean_dec(x_13);
x_23 = x_156;
x_24 = lean_box(0);
x_25 = x_146;
x_26 = x_149;
x_27 = x_144;
x_28 = x_158;
x_29 = x_147;
x_30 = x_148;
x_31 = x_151;
x_32 = x_150;
x_33 = x_152;
x_34 = x_154;
x_35 = x_153;
x_36 = x_157;
x_37 = x_155;
x_38 = x_165;
goto block_142;
}
}
}
block_186:
{
size_t x_173; size_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_173 = lean_array_size(x_20);
x_174 = 0;
lean_inc_ref(x_20);
x_175 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(x_13, x_173, x_174, x_20);
x_176 = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7));
lean_inc(x_17);
x_177 = l_Lean_Name_append(x_17, x_176);
x_178 = lean_unsigned_to_nat(0u);
x_179 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8;
x_180 = lean_nat_dec_lt(x_178, x_143);
if (x_180 == 0)
{
x_144 = x_178;
x_145 = lean_box(0);
x_146 = x_177;
x_147 = x_167;
x_148 = x_170;
x_149 = x_169;
x_150 = x_173;
x_151 = x_175;
x_152 = x_171;
x_153 = x_174;
x_154 = x_168;
x_155 = x_179;
goto block_166;
}
else
{
uint8_t x_181; 
x_181 = lean_nat_dec_le(x_143, x_143);
if (x_181 == 0)
{
if (x_180 == 0)
{
x_144 = x_178;
x_145 = lean_box(0);
x_146 = x_177;
x_147 = x_167;
x_148 = x_170;
x_149 = x_169;
x_150 = x_173;
x_151 = x_175;
x_152 = x_171;
x_153 = x_174;
x_154 = x_168;
x_155 = x_179;
goto block_166;
}
else
{
size_t x_182; lean_object* x_183; 
x_182 = lean_usize_of_nat(x_143);
x_183 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(x_13, x_20, x_174, x_182, x_179);
x_144 = x_178;
x_145 = lean_box(0);
x_146 = x_177;
x_147 = x_167;
x_148 = x_170;
x_149 = x_169;
x_150 = x_173;
x_151 = x_175;
x_152 = x_171;
x_153 = x_174;
x_154 = x_168;
x_155 = x_183;
goto block_166;
}
}
else
{
size_t x_184; lean_object* x_185; 
x_184 = lean_usize_of_nat(x_143);
x_185 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(x_13, x_20, x_174, x_184, x_179);
x_144 = x_178;
x_145 = lean_box(0);
x_146 = x_177;
x_147 = x_167;
x_148 = x_170;
x_149 = x_169;
x_150 = x_173;
x_151 = x_175;
x_152 = x_171;
x_153 = x_174;
x_154 = x_168;
x_155 = x_185;
goto block_166;
}
}
}
block_201:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_192 = lean_box(0);
x_193 = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(x_191, x_192);
x_194 = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(x_193, x_192);
x_195 = l_Lean_MessageData_ofList(x_194);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_188);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(x_190, x_196, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_197) == 0)
{
lean_dec_ref(x_197);
x_167 = x_189;
x_168 = x_2;
x_169 = x_3;
x_170 = x_4;
x_171 = x_5;
x_172 = lean_box(0);
goto block_186;
}
else
{
uint8_t x_198; 
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
return x_197;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
return x_200;
}
}
}
block_220:
{
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
lean_dec(x_14);
lean_inc(x_10);
lean_dec_ref(x_1);
x_203 = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11));
x_204 = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg(x_203, x_4);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = lean_unbox(x_205);
lean_dec(x_205);
if (x_206 == 0)
{
x_167 = x_202;
x_168 = x_2;
x_169 = x_3;
x_170 = x_4;
x_171 = x_5;
x_172 = lean_box(0);
goto block_186;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_inc(x_17);
x_207 = l_Lean_MessageData_ofName(x_17);
x_208 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13;
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_box(0);
x_211 = lean_array_get_size(x_16);
x_212 = lean_unsigned_to_nat(0u);
x_213 = lean_nat_dec_lt(x_212, x_211);
if (x_213 == 0)
{
x_187 = lean_box(0);
x_188 = x_209;
x_189 = x_202;
x_190 = x_203;
x_191 = x_210;
goto block_201;
}
else
{
size_t x_214; size_t x_215; lean_object* x_216; 
x_214 = lean_usize_of_nat(x_211);
x_215 = 0;
x_216 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12(x_16, x_214, x_215, x_210);
x_187 = lean_box(0);
x_188 = x_209;
x_189 = x_202;
x_190 = x_203;
x_191 = x_216;
goto block_201;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_217 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14;
x_218 = lean_array_push(x_217, x_1);
if (lean_is_scalar(x_14)) {
 x_219 = lean_alloc_ctor(0, 1, 0);
} else {
 x_219 = x_14;
}
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
}
else
{
uint8_t x_224; 
lean_dec_ref(x_11);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_224 = !lean_is_exclusive(x_12);
if (x_224 == 0)
{
return x_12;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_12, 0);
lean_inc(x_225);
lean_dec(x_12);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_227 = !lean_is_exclusive(x_7);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_7, 0);
lean_dec(x_228);
x_229 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14;
x_230 = lean_array_push(x_229, x_1);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_230);
return x_7;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_7);
x_231 = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14;
x_232 = lean_array_push(x_231, x_1);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Decl_reduceArity(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(x_1, x_2, x_3, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_2, x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_18 = l_Lean_Compiler_LCNF_Decl_reduceArity(x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Array_append___redArg(x_4, x_19);
lean_dec(x_19);
x_10 = x_20;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec_ref(x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_10 = x_21;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_18;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_4);
return x_22;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_mk_empty_array_with_capacity(x_1);
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_9);
if (x_12 == 0)
{
if (x_10 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_9);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(x_2, x_14, x_15, x_8, x_3, x_4, x_5, x_6);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_9);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(x_2, x_17, x_18, x_8, x_3, x_4, x_5, x_6);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_reduceArity___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2803462840u);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
x_2 = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
x_2 = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11));
x_3 = 1;
x_4 = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0 = _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0);
l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3);
l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4 = _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4);
l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0 = _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0);
l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1 = _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1);
l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2 = _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2);
l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3 = _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3();
l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5 = _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13);
l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14 = _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14);
l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
