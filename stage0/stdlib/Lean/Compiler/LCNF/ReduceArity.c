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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toArg___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_FindUsed_visit___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3;
static const lean_array_object l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_redArg"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value),LEAN_SCALAR_PTR_LITERAL(174, 35, 1, 83, 6, 52, 87, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_value;
static const lean_array_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceArity"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value),LEAN_SCALAR_PTR_LITERAL(89, 83, 236, 44, 104, 94, 232, 236)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ", used params: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; uint8_t v___x_44_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v___x_44_ = l_Lean_instBEqFVarId_beq(v_val_43_, v_query_2_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
lean_dec(v_val_43_);
v___x_45_ = lean_array_get_size(v_keyArray_17_);
v___x_46_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_47_ = lean_nat_dec_lt(v___x_46_, v___x_45_);
if (v___x_47_ == 0)
{
lean_dec(v___x_46_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_46_;
goto _start;
}
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_inc(v___x_41_);
v_val_50_ = lean_noption_get(v___x_41_);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v_x_5_);
lean_ctor_set(v___x_51_, 1, v_val_43_);
lean_ctor_set(v___x_51_, 2, v_val_50_);
return v___x_51_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg___boxed(lean_object* v_m_52_, lean_object* v_query_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_m_52_, v_query_53_, v_x_54_, v_x_55_, v_x_56_);
lean_dec(v_query_53_);
lean_dec_ref(v_m_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(lean_object* v_m_58_, lean_object* v_query_59_){
_start:
{
lean_object* v_keyArray_60_; lean_object* v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v_fold_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; size_t v___x_69_; size_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_keyArray_60_ = lean_ctor_get(v_m_58_, 1);
v___x_61_ = lean_array_get_size(v_keyArray_60_);
v___x_62_ = l_Lean_instHashableFVarId_hash(v_query_59_);
v___x_63_ = 32ULL;
v___x_64_ = lean_uint64_shift_right(v___x_62_, v___x_63_);
v_fold_65_ = lean_uint64_xor(v___x_62_, v___x_64_);
v___x_66_ = 16ULL;
v___x_67_ = lean_uint64_shift_right(v_fold_65_, v___x_66_);
v___x_68_ = lean_uint64_xor(v_fold_65_, v___x_67_);
v___x_69_ = lean_uint64_to_usize(v___x_68_);
v___x_70_ = lean_usize_of_nat(v___x_61_);
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_sub(v___x_70_, v___x_71_);
v___x_73_ = lean_usize_land(v___x_69_, v___x_72_);
v___x_74_ = lean_usize_to_nat(v___x_73_);
v___x_75_ = lean_box(0);
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_m_58_, v_query_59_, v___x_75_, v___x_61_, v___x_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg___boxed(lean_object* v_m_77_, lean_object* v_query_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v_m_77_, v_query_78_);
lean_dec(v_query_78_);
lean_dec_ref(v_m_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4___redArg(lean_object* v_b_80_, lean_object* v_acc_81_, lean_object* v_i_82_){
_start:
{
lean_object* v___y_84_; lean_object* v_keyArray_92_; lean_object* v_valueArray_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v_keyArray_92_ = lean_ctor_get(v_b_80_, 1);
v_valueArray_93_ = lean_ctor_get(v_b_80_, 2);
v___x_94_ = lean_array_get_size(v_keyArray_92_);
v___x_95_ = lean_nat_dec_lt(v_i_82_, v___x_94_);
if (v___x_95_ == 0)
{
lean_dec(v_i_82_);
return v_acc_81_;
}
else
{
lean_object* v___x_96_; uint8_t v_isSome_97_; 
v___x_96_ = lean_array_fget_borrowed(v_keyArray_92_, v_i_82_);
v_isSome_97_ = lean_noption_is_some(v___x_96_);
if (v_isSome_97_ == 0)
{
goto v___jp_88_;
}
else
{
lean_object* v___x_98_; uint8_t v_isSome_99_; 
v___x_98_ = lean_array_fget_borrowed(v_valueArray_93_, v_i_82_);
v_isSome_99_ = lean_noption_is_some(v___x_98_);
if (v_isSome_99_ == 0)
{
goto v___jp_88_;
}
else
{
lean_object* v_val_100_; lean_object* v_val_101_; lean_object* v_i_103_; lean_object* v___x_108_; 
lean_inc(v___x_96_);
v_val_100_ = lean_noption_get(v___x_96_);
lean_inc(v___x_98_);
v_val_101_ = lean_noption_get(v___x_98_);
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v_acc_81_, v_val_100_);
switch(lean_obj_tag(v___x_108_))
{
case 0:
{
lean_object* v_index_109_; lean_object* v_size_110_; lean_object* v___x_111_; 
v_index_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_index_109_);
lean_dec_ref_known(v___x_108_, 3);
v_size_110_ = lean_ctor_get(v_acc_81_, 0);
lean_inc(v_size_110_);
v___x_111_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_81_, v_size_110_, v_index_109_, v_val_100_, v_val_101_);
lean_dec(v_index_109_);
v___y_84_ = v___x_111_;
goto v___jp_83_;
}
case 1:
{
lean_object* v_index_112_; 
v_index_112_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_index_112_);
lean_dec_ref_known(v___x_108_, 1);
v_i_103_ = v_index_112_;
goto v___jp_102_;
}
default: 
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_81_, v___x_113_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_index_115_; 
v_index_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_index_115_);
lean_dec_ref_known(v___x_114_, 1);
v_i_103_ = v_index_115_;
goto v___jp_102_;
}
else
{
lean_dec(v_val_101_);
lean_dec(v_val_100_);
v___y_84_ = v_acc_81_;
goto v___jp_83_;
}
}
}
v___jp_102_:
{
lean_object* v_size_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_size_104_ = lean_ctor_get(v_acc_81_, 0);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_size_104_, v___x_105_);
v___x_107_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_81_, v___x_106_, v_i_103_, v_val_100_, v_val_101_);
lean_dec(v_i_103_);
v___y_84_ = v___x_107_;
goto v___jp_83_;
}
}
}
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_i_82_, v___x_85_);
lean_dec(v_i_82_);
v_acc_81_ = v___y_84_;
v_i_82_ = v___x_86_;
goto _start;
}
v___jp_88_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(1u);
v___x_90_ = lean_nat_add(v_i_82_, v___x_89_);
lean_dec(v_i_82_);
v_i_82_ = v___x_90_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_b_116_, lean_object* v_acc_117_, lean_object* v_i_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4___redArg(v_b_116_, v_acc_117_, v_i_118_);
lean_dec_ref(v_b_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3___redArg(lean_object* v_init_120_, lean_object* v_b_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4___redArg(v_b_121_, v_init_120_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3___redArg___boxed(lean_object* v_init_124_, lean_object* v_b_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3___redArg(v_init_124_, v_b_125_);
lean_dec_ref(v_b_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___redArg(lean_object* v_m_127_){
_start:
{
lean_object* v_keyArray_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_cellCount_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_target_135_; lean_object* v___x_136_; 
v_keyArray_128_ = lean_ctor_get(v_m_127_, 1);
v___x_129_ = lean_array_get_size(v_keyArray_128_);
v___x_130_ = lean_unsigned_to_nat(2u);
v_cellCount_131_ = lean_nat_mul(v___x_129_, v___x_130_);
v___x_132_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_131_);
v___x_133_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_131_);
v___x_134_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_131_);
v_target_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_135_, 0, v___x_132_);
lean_ctor_set(v_target_135_, 1, v___x_133_);
lean_ctor_set(v_target_135_, 2, v___x_134_);
v___x_136_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3___redArg(v_target_135_, v_m_127_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___redArg___boxed(lean_object* v_m_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___redArg(v_m_137_);
lean_dec_ref(v_m_137_);
return v_res_138_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(lean_object* v_k_139_, lean_object* v_t_140_){
_start:
{
if (lean_obj_tag(v_t_140_) == 0)
{
lean_object* v_k_141_; lean_object* v_l_142_; lean_object* v_r_143_; uint8_t v___x_144_; 
v_k_141_ = lean_ctor_get(v_t_140_, 1);
v_l_142_ = lean_ctor_get(v_t_140_, 3);
v_r_143_ = lean_ctor_get(v_t_140_, 4);
v___x_144_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_139_, v_k_141_);
switch(v___x_144_)
{
case 0:
{
v_t_140_ = v_l_142_;
goto _start;
}
case 1:
{
uint8_t v___x_146_; 
v___x_146_ = 1;
return v___x_146_;
}
default: 
{
v_t_140_ = v_r_143_;
goto _start;
}
}
}
else
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg___boxed(lean_object* v_k_149_, lean_object* v_t_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_149_, v_t_150_);
lean_dec(v_t_150_);
lean_dec(v_k_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object* v_fvarId_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_params_157_; uint8_t v___x_158_; 
v_params_157_ = lean_ctor_get(v_a_154_, 1);
v___x_158_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_fvarId_153_, v_params_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v_fvarId_153_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___y_164_; lean_object* v___y_168_; lean_object* v_i_169_; lean_object* v___y_175_; lean_object* v___y_185_; lean_object* v_i_186_; lean_object* v___x_201_; 
v___x_161_ = lean_st_ref_take(v_a_155_);
v___x_162_ = lean_box(0);
v___x_201_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v___x_161_, v_fvarId_153_);
switch(lean_obj_tag(v___x_201_))
{
case 0:
{
lean_dec_ref_known(v___x_201_, 3);
lean_dec(v_fvarId_153_);
v___y_164_ = v___x_161_;
goto v___jp_163_;
}
case 1:
{
lean_object* v_index_202_; lean_object* v_size_203_; lean_object* v_keyArray_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_index_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_index_202_);
lean_dec_ref_known(v___x_201_, 1);
v_size_203_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_size_203_);
v_keyArray_204_ = lean_ctor_get(v___x_161_, 1);
lean_inc_ref(v_keyArray_204_);
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_add(v_size_203_, v___x_205_);
lean_dec(v_size_203_);
v___x_207_ = lean_array_get_size(v_keyArray_204_);
lean_dec_ref(v_keyArray_204_);
v___x_208_ = lean_nat_dec_lt(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
lean_dec(v___x_206_);
lean_dec(v_index_202_);
goto v___jp_191_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_209_ = lean_unsigned_to_nat(4u);
v___x_210_ = lean_nat_mul(v___x_206_, v___x_209_);
v___x_211_ = lean_unsigned_to_nat(3u);
v___x_212_ = lean_nat_mul(v___x_207_, v___x_211_);
v___x_213_ = lean_nat_dec_le(v___x_210_, v___x_212_);
lean_dec(v___x_212_);
lean_dec(v___x_210_);
if (v___x_213_ == 0)
{
lean_dec(v___x_206_);
lean_dec(v_index_202_);
goto v___jp_191_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_161_, v___x_206_, v_index_202_, v_fvarId_153_, v___x_162_);
lean_dec(v_index_202_);
v___y_164_ = v___x_214_;
goto v___jp_163_;
}
}
}
default: 
{
lean_object* v_size_215_; lean_object* v_keyArray_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_size_215_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_size_215_);
v_keyArray_216_ = lean_ctor_get(v___x_161_, 1);
lean_inc_ref(v_keyArray_216_);
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_add(v_size_215_, v___x_217_);
lean_dec(v_size_215_);
v___x_219_ = lean_array_get_size(v_keyArray_216_);
lean_dec_ref(v_keyArray_216_);
v___x_220_ = lean_nat_dec_lt(v___x_218_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
lean_dec(v___x_218_);
v___x_221_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___redArg(v___x_161_);
lean_dec(v___x_161_);
v___y_175_ = v___x_221_;
goto v___jp_174_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_222_ = lean_unsigned_to_nat(4u);
v___x_223_ = lean_nat_mul(v___x_218_, v___x_222_);
lean_dec(v___x_218_);
v___x_224_ = lean_unsigned_to_nat(3u);
v___x_225_ = lean_nat_mul(v___x_219_, v___x_224_);
v___x_226_ = lean_nat_dec_le(v___x_223_, v___x_225_);
lean_dec(v___x_225_);
lean_dec(v___x_223_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___redArg(v___x_161_);
lean_dec(v___x_161_);
v___y_175_ = v___x_227_;
goto v___jp_174_;
}
else
{
v___y_175_ = v___x_161_;
goto v___jp_174_;
}
}
}
}
v___jp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_st_ref_put(v_a_155_, v___y_164_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_162_);
return v___x_166_;
}
v___jp_167_:
{
lean_object* v_size_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_size_170_ = lean_ctor_get(v___y_168_, 0);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_size_170_, v___x_171_);
v___x_173_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_168_, v___x_172_, v_i_169_, v_fvarId_153_, v___x_162_);
lean_dec(v_i_169_);
v___y_164_ = v___x_173_;
goto v___jp_163_;
}
v___jp_174_:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v___y_175_, v_fvarId_153_);
switch(lean_obj_tag(v___x_176_))
{
case 0:
{
lean_object* v_index_177_; lean_object* v_size_178_; lean_object* v___x_179_; 
v_index_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_index_177_);
lean_dec_ref_known(v___x_176_, 3);
v_size_178_ = lean_ctor_get(v___y_175_, 0);
lean_inc(v_size_178_);
v___x_179_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_175_, v_size_178_, v_index_177_, v_fvarId_153_, v___x_162_);
lean_dec(v_index_177_);
v___y_164_ = v___x_179_;
goto v___jp_163_;
}
case 1:
{
lean_object* v_index_180_; 
v_index_180_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_index_180_);
lean_dec_ref_known(v___x_176_, 1);
v___y_168_ = v___y_175_;
v_i_169_ = v_index_180_;
goto v___jp_167_;
}
default: 
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_175_, v___x_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_index_183_; 
v_index_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_index_183_);
lean_dec_ref_known(v___x_182_, 1);
v___y_168_ = v___y_175_;
v_i_169_ = v_index_183_;
goto v___jp_167_;
}
else
{
lean_dec(v_fvarId_153_);
v___y_164_ = v___y_175_;
goto v___jp_163_;
}
}
}
}
v___jp_184_:
{
lean_object* v_size_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_size_187_ = lean_ctor_get(v___y_185_, 0);
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = lean_nat_add(v_size_187_, v___x_188_);
v___x_190_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_185_, v___x_189_, v_i_186_, v_fvarId_153_, v___x_162_);
lean_dec(v_i_186_);
v___y_164_ = v___x_190_;
goto v___jp_163_;
}
v___jp_191_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___redArg(v___x_161_);
lean_dec(v___x_161_);
v___x_193_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v___x_192_, v_fvarId_153_);
switch(lean_obj_tag(v___x_193_))
{
case 0:
{
lean_object* v_index_194_; lean_object* v_size_195_; lean_object* v___x_196_; 
v_index_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_index_194_);
lean_dec_ref_known(v___x_193_, 3);
v_size_195_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_size_195_);
v___x_196_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_192_, v_size_195_, v_index_194_, v_fvarId_153_, v___x_162_);
lean_dec(v_index_194_);
v___y_164_ = v___x_196_;
goto v___jp_163_;
}
case 1:
{
lean_object* v_index_197_; 
v_index_197_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_index_197_);
lean_dec_ref_known(v___x_193_, 1);
v___y_185_ = v___x_192_;
v_i_186_ = v_index_197_;
goto v___jp_184_;
}
default: 
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_192_, v___x_198_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_index_200_; 
v_index_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_index_200_);
lean_dec_ref_known(v___x_199_, 1);
v___y_185_ = v___x_192_;
v_i_186_ = v_index_200_;
goto v___jp_184_;
}
else
{
lean_dec(v_fvarId_153_);
v___y_164_ = v___x_192_;
goto v___jp_163_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object* v_fvarId_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_228_, v_a_229_, v_a_230_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object* v_fvarId_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_233_, v_a_234_, v_a_235_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object* v_fvarId_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar(v_fvarId_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
return v_res_250_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(lean_object* v_00_u03b2_251_, lean_object* v_k_252_, lean_object* v_t_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_252_, v_t_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___boxed(lean_object* v_00_u03b2_255_, lean_object* v_k_256_, lean_object* v_t_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(v_00_u03b2_255_, v_k_256_, v_t_257_);
lean_dec(v_t_257_);
lean_dec(v_k_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1(lean_object* v_00_u03b2_260_, lean_object* v_m_261_, lean_object* v_query_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v_m_261_, v_query_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___boxed(lean_object* v_00_u03b2_264_, lean_object* v_m_265_, lean_object* v_query_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1(v_00_u03b2_264_, v_m_265_, v_query_266_);
lean_dec(v_query_266_);
lean_dec_ref(v_m_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2(lean_object* v_00_u03b2_268_, lean_object* v_m_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___redArg(v_m_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2___boxed(lean_object* v_00_u03b2_271_, lean_object* v_m_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2(v_00_u03b2_271_, v_m_272_);
lean_dec_ref(v_m_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(lean_object* v_00_u03b2_274_, lean_object* v_m_275_, lean_object* v_query_276_, lean_object* v_x_277_, lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_m_275_, v_query_276_, v_x_277_, v_x_278_, v_x_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___boxed(lean_object* v_00_u03b2_282_, lean_object* v_m_283_, lean_object* v_query_284_, lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(v_00_u03b2_282_, v_m_283_, v_query_284_, v_x_285_, v_x_286_, v_x_287_, v_x_288_);
lean_dec(v_query_284_);
lean_dec_ref(v_m_283_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3(lean_object* v_00_u03b2_290_, lean_object* v_init_291_, lean_object* v_b_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3___redArg(v_init_291_, v_b_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3___boxed(lean_object* v_00_u03b2_294_, lean_object* v_init_295_, lean_object* v_b_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3(v_00_u03b2_294_, v_init_295_, v_b_296_);
lean_dec_ref(v_b_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_298_, lean_object* v_b_299_, lean_object* v_acc_300_, lean_object* v_i_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4___redArg(v_b_299_, v_acc_300_, v_i_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_303_, lean_object* v_b_304_, lean_object* v_acc_305_, lean_object* v_i_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__2_spec__3_spec__4(v_00_u03b2_303_, v_b_304_, v_acc_305_, v_i_306_);
lean_dec_ref(v_b_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object* v_arg_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
if (lean_obj_tag(v_arg_308_) == 1)
{
lean_object* v_fvarId_312_; lean_object* v___x_313_; 
v_fvarId_312_ = lean_ctor_get(v_arg_308_, 0);
lean_inc(v_fvarId_312_);
lean_dec_ref_known(v_arg_308_, 1);
v___x_313_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_312_, v_a_309_, v_a_310_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_arg_308_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object* v_arg_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_316_, v_a_317_, v_a_318_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object* v_arg_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_321_, v_a_322_, v_a_323_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object* v_arg_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Compiler_LCNF_FindUsed_visitArg(v_arg_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object* v_as_339_, size_t v_sz_340_, size_t v_i_341_, lean_object* v_b_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_a_347_; uint8_t v___x_351_; 
v___x_351_ = lean_usize_dec_lt(v_i_341_, v_sz_340_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v_b_342_);
return v___x_352_;
}
else
{
lean_object* v_array_353_; lean_object* v_start_354_; lean_object* v_stop_355_; uint8_t v___x_356_; 
v_array_353_ = lean_ctor_get(v_b_342_, 0);
v_start_354_ = lean_ctor_get(v_b_342_, 1);
v_stop_355_ = lean_ctor_get(v_b_342_, 2);
v___x_356_ = lean_nat_dec_lt(v_start_354_, v_stop_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v_b_342_);
return v___x_357_;
}
else
{
lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_380_; 
lean_inc(v_stop_355_);
lean_inc(v_start_354_);
lean_inc_ref(v_array_353_);
v_isSharedCheck_380_ = !lean_is_exclusive(v_b_342_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; lean_object* v_unused_382_; lean_object* v_unused_383_; 
v_unused_381_ = lean_ctor_get(v_b_342_, 2);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v_b_342_, 1);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_b_342_, 0);
lean_dec(v_unused_383_);
v___x_359_ = v_b_342_;
v_isShared_360_ = v_isSharedCheck_380_;
goto v_resetjp_358_;
}
else
{
lean_dec(v_b_342_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_380_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_361_ = lean_array_fget(v_array_353_, v_start_354_);
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_add(v_start_354_, v___x_362_);
lean_dec(v_start_354_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v___x_363_);
v___x_365_ = v___x_359_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_array_353_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_stop_355_);
v___x_365_ = v_reuseFailAlloc_379_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
if (lean_obj_tag(v___x_361_) == 1)
{
lean_object* v_fvarId_366_; lean_object* v_a_367_; lean_object* v_fvarId_368_; uint8_t v___x_369_; 
v_fvarId_366_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_fvarId_366_);
lean_dec_ref_known(v___x_361_, 1);
v_a_367_ = lean_array_uget_borrowed(v_as_339_, v_i_341_);
v_fvarId_368_ = lean_ctor_get(v_a_367_, 0);
v___x_369_ = l_Lean_instBEqFVarId_beq(v_fvarId_366_, v_fvarId_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_366_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_dec_ref_known(v___x_370_, 1);
v_a_347_ = v___x_365_;
goto v___jp_346_;
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v___x_365_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_dec(v_fvarId_366_);
v_a_347_ = v___x_365_;
goto v___jp_346_;
}
}
else
{
lean_dec(v___x_361_);
v_a_347_ = v___x_365_;
goto v___jp_346_;
}
}
}
}
}
v___jp_346_:
{
size_t v___x_348_; size_t v___x_349_; 
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_add(v_i_341_, v___x_348_);
v_i_341_ = v___x_349_;
v_b_342_ = v_a_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object* v_as_384_, lean_object* v_sz_385_, lean_object* v_i_386_, lean_object* v_b_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
size_t v_sz_boxed_391_; size_t v_i_boxed_392_; lean_object* v_res_393_; 
v_sz_boxed_391_ = lean_unbox_usize(v_sz_385_);
lean_dec(v_sz_385_);
v_i_boxed_392_ = lean_unbox_usize(v_i_386_);
lean_dec(v_i_386_);
v_res_393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_384_, v_sz_boxed_391_, v_i_boxed_392_, v_b_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec_ref(v_as_384_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object* v_as_394_, size_t v_i_395_, size_t v_stop_396_, lean_object* v_b_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = lean_usize_dec_eq(v_i_395_, v_stop_396_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_array_uget_borrowed(v_as_394_, v_i_395_);
lean_inc(v___x_402_);
v___x_403_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v___x_402_, v___y_398_, v___y_399_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; size_t v___x_405_; size_t v___x_406_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_add(v_i_395_, v___x_405_);
v_i_395_ = v___x_406_;
v_b_397_ = v_a_404_;
goto _start;
}
else
{
return v___x_403_;
}
}
else
{
lean_object* v___x_408_; 
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v_b_397_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object* v_as_409_, lean_object* v_i_410_, lean_object* v_stop_411_, lean_object* v_b_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
size_t v_i_boxed_416_; size_t v_stop_boxed_417_; lean_object* v_res_418_; 
v_i_boxed_416_ = lean_unbox_usize(v_i_410_);
lean_dec(v_i_410_);
v_stop_boxed_417_ = lean_unbox_usize(v_stop_411_);
lean_dec(v_stop_411_);
v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_409_, v_i_boxed_416_, v_stop_boxed_417_, v_b_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec_ref(v_as_409_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object* v_a_419_, lean_object* v_b_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_array_424_; lean_object* v_start_425_; lean_object* v_stop_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_442_; 
v_array_424_ = lean_ctor_get(v_a_419_, 0);
v_start_425_ = lean_ctor_get(v_a_419_, 1);
v_stop_426_ = lean_ctor_get(v_a_419_, 2);
v_isSharedCheck_442_ = !lean_is_exclusive(v_a_419_);
if (v_isSharedCheck_442_ == 0)
{
v___x_428_ = v_a_419_;
v_isShared_429_ = v_isSharedCheck_442_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_stop_426_);
lean_inc(v_start_425_);
lean_inc(v_array_424_);
lean_dec(v_a_419_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_442_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint8_t v___x_430_; 
v___x_430_ = lean_nat_dec_lt(v_start_425_, v_stop_426_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_del_object(v___x_428_);
lean_dec(v_stop_426_);
lean_dec(v_start_425_);
lean_dec_ref(v_array_424_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_b_420_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v_fvarId_433_; lean_object* v___x_434_; 
v___x_432_ = lean_array_fget_borrowed(v_array_424_, v_start_425_);
v_fvarId_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_fvarId_433_);
v___x_434_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_433_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
lean_dec_ref_known(v___x_434_, 1);
v___x_435_ = lean_box(0);
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_add(v_start_425_, v___x_436_);
lean_dec(v_start_425_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_437_);
v___x_439_ = v___x_428_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_array_424_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_stop_426_);
v___x_439_ = v_reuseFailAlloc_441_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
v_a_419_ = v___x_439_;
v_b_420_ = v___x_435_;
goto _start;
}
}
else
{
lean_del_object(v___x_428_);
lean_dec(v_stop_426_);
lean_dec(v_start_425_);
lean_dec_ref(v_array_424_);
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object* v_a_443_, lean_object* v_b_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_443_, v_b_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object* v_a_449_, lean_object* v_b_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_array_454_; lean_object* v_start_455_; lean_object* v_stop_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_471_; 
v_array_454_ = lean_ctor_get(v_a_449_, 0);
v_start_455_ = lean_ctor_get(v_a_449_, 1);
v_stop_456_ = lean_ctor_get(v_a_449_, 2);
v_isSharedCheck_471_ = !lean_is_exclusive(v_a_449_);
if (v_isSharedCheck_471_ == 0)
{
v___x_458_ = v_a_449_;
v_isShared_459_ = v_isSharedCheck_471_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_stop_456_);
lean_inc(v_start_455_);
lean_inc(v_array_454_);
lean_dec(v_a_449_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_471_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
uint8_t v___x_460_; 
v___x_460_ = lean_nat_dec_lt(v_start_455_, v_stop_456_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_del_object(v___x_458_);
lean_dec(v_stop_456_);
lean_dec(v_start_455_);
lean_dec_ref(v_array_454_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v_b_450_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_array_fget_borrowed(v_array_454_, v_start_455_);
lean_inc(v___x_462_);
v___x_463_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v___x_462_, v___y_451_, v___y_452_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
lean_dec_ref_known(v___x_463_, 1);
v___x_464_ = lean_box(0);
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_add(v_start_455_, v___x_465_);
lean_dec(v_start_455_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_466_);
v___x_468_ = v___x_458_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_array_454_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v_stop_456_);
v___x_468_ = v_reuseFailAlloc_470_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
v_a_449_ = v___x_468_;
v_b_450_ = v___x_464_;
goto _start;
}
}
else
{
lean_del_object(v___x_458_);
lean_dec(v_stop_456_);
lean_dec(v_start_455_);
lean_dec_ref(v_array_454_);
return v___x_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_472_, v_b_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object* v_e_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
switch(lean_obj_tag(v_e_478_))
{
case 0:
{
lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_493_; 
v_isSharedCheck_493_ = !lean_is_exclusive(v_e_478_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_e_478_, 0);
lean_dec(v_unused_494_);
v___x_487_ = v_e_478_;
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
else
{
lean_dec(v_e_478_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_box(0);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
case 1:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_box(0);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
case 2:
{
lean_object* v_struct_497_; lean_object* v___x_498_; 
v_struct_497_ = lean_ctor_get(v_e_478_, 2);
lean_inc(v_struct_497_);
lean_dec_ref_known(v_e_478_, 3);
v___x_498_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_struct_497_, v_a_479_, v_a_480_);
return v___x_498_;
}
case 3:
{
lean_object* v_decl_499_; lean_object* v_toSignature_500_; lean_object* v_declName_501_; lean_object* v_args_502_; lean_object* v_name_503_; lean_object* v_params_504_; lean_object* v___y_506_; lean_object* v_lower_507_; lean_object* v_upper_508_; uint8_t v___x_519_; 
v_decl_499_ = lean_ctor_get(v_a_479_, 0);
v_toSignature_500_ = lean_ctor_get(v_decl_499_, 0);
v_declName_501_ = lean_ctor_get(v_e_478_, 0);
lean_inc(v_declName_501_);
v_args_502_ = lean_ctor_get(v_e_478_, 2);
lean_inc_ref(v_args_502_);
lean_dec_ref_known(v_e_478_, 3);
v_name_503_ = lean_ctor_get(v_toSignature_500_, 0);
v_params_504_ = lean_ctor_get(v_toSignature_500_, 3);
v___x_519_ = lean_name_eq(v_declName_501_, v_name_503_);
lean_dec(v_declName_501_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_array_get_size(v_args_502_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_nat_dec_lt(v___x_520_, v___x_521_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_dec_ref(v_args_502_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
return v___x_524_;
}
else
{
uint8_t v___x_525_; 
v___x_525_ = lean_nat_dec_le(v___x_521_, v___x_521_);
if (v___x_525_ == 0)
{
if (v___x_523_ == 0)
{
lean_object* v___x_526_; 
lean_dec_ref(v_args_502_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_522_);
return v___x_526_;
}
else
{
size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
v___x_527_ = ((size_t)0ULL);
v___x_528_ = lean_usize_of_nat(v___x_521_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_502_, v___x_527_, v___x_528_, v___x_522_, v_a_479_, v_a_480_);
lean_dec_ref(v_args_502_);
return v___x_529_;
}
}
else
{
size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((size_t)0ULL);
v___x_531_ = lean_usize_of_nat(v___x_521_);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_502_, v___x_530_, v___x_531_, v___x_522_, v_a_479_, v_a_480_);
lean_dec_ref(v_args_502_);
return v___x_532_;
}
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; size_t v_sz_536_; size_t v___x_537_; lean_object* v___x_538_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_array_get_size(v_args_502_);
lean_inc_ref(v_args_502_);
v___x_535_ = l_Array_toSubarray___redArg(v_args_502_, v___x_533_, v___x_534_);
v_sz_536_ = lean_array_size(v_params_504_);
v___x_537_ = ((size_t)0ULL);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_params_504_, v_sz_536_, v___x_537_, v___x_535_, v_a_479_, v_a_480_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_lower_540_; lean_object* v_upper_541_; lean_object* v___x_547_; uint8_t v___x_548_; 
lean_dec_ref_known(v___x_538_, 1);
v___x_547_ = lean_array_get_size(v_params_504_);
v___x_548_ = lean_nat_dec_le(v___x_547_, v___x_533_);
if (v___x_548_ == 0)
{
v_lower_540_ = v___x_547_;
v_upper_541_ = v___x_534_;
goto v___jp_539_;
}
else
{
v_lower_540_ = v___x_533_;
v_upper_541_ = v___x_534_;
goto v___jp_539_;
}
v___jp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = l_Array_toSubarray___redArg(v_args_502_, v_lower_540_, v_upper_541_);
v___x_543_ = lean_box(0);
v___x_544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v___x_542_, v___x_543_, v_a_479_, v_a_480_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_545_; uint8_t v___x_546_; 
lean_dec_ref_known(v___x_544_, 1);
v___x_545_ = lean_array_get_size(v_params_504_);
v___x_546_ = lean_nat_dec_le(v___x_534_, v___x_533_);
if (v___x_546_ == 0)
{
v___y_506_ = v___x_543_;
v_lower_507_ = v___x_534_;
v_upper_508_ = v___x_545_;
goto v___jp_505_;
}
else
{
v___y_506_ = v___x_543_;
v_lower_507_ = v___x_533_;
v_upper_508_ = v___x_545_;
goto v___jp_505_;
}
}
else
{
return v___x_544_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v_args_502_);
v_a_549_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_538_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_538_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
v___jp_505_:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_inc_ref(v_params_504_);
v___x_509_ = l_Array_toSubarray___redArg(v_params_504_, v_lower_507_, v_upper_508_);
v___x_510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v___x_509_, v___y_506_, v_a_479_, v_a_480_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v___x_510_, 0);
lean_dec(v_unused_518_);
v___x_512_ = v___x_510_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_dec(v___x_510_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___y_506_);
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___y_506_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
else
{
return v___x_510_;
}
}
}
default: 
{
lean_object* v_fvarId_557_; lean_object* v_args_558_; lean_object* v___x_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_580_; 
v_fvarId_557_ = lean_ctor_get(v_e_478_, 0);
lean_inc(v_fvarId_557_);
v_args_558_ = lean_ctor_get(v_e_478_, 1);
lean_inc_ref(v_args_558_);
lean_dec_ref_known(v_e_478_, 2);
v___x_559_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_557_, v_a_479_, v_a_480_);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v___x_559_, 0);
lean_dec(v_unused_581_);
v___x_561_ = v___x_559_;
v_isShared_562_ = v_isSharedCheck_580_;
goto v_resetjp_560_;
}
else
{
lean_dec(v___x_559_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_580_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_array_get_size(v_args_558_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_nat_dec_lt(v___x_563_, v___x_564_);
if (v___x_566_ == 0)
{
lean_object* v___x_568_; 
lean_dec_ref(v_args_558_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_565_);
v___x_568_ = v___x_561_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_565_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
else
{
uint8_t v___x_570_; 
v___x_570_ = lean_nat_dec_le(v___x_564_, v___x_564_);
if (v___x_570_ == 0)
{
if (v___x_566_ == 0)
{
lean_object* v___x_572_; 
lean_dec_ref(v_args_558_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_565_);
v___x_572_ = v___x_561_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_565_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
else
{
size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
lean_del_object(v___x_561_);
v___x_574_ = ((size_t)0ULL);
v___x_575_ = lean_usize_of_nat(v___x_564_);
v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_558_, v___x_574_, v___x_575_, v___x_565_, v_a_479_, v_a_480_);
lean_dec_ref(v_args_558_);
return v___x_576_;
}
}
else
{
size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; 
lean_del_object(v___x_561_);
v___x_577_ = ((size_t)0ULL);
v___x_578_ = lean_usize_of_nat(v___x_564_);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_558_, v___x_577_, v___x_578_, v___x_565_, v_a_479_, v_a_480_);
lean_dec_ref(v_args_558_);
return v___x_579_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object* v_e_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_e_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object* v_as_591_, size_t v_i_592_, size_t v_stop_593_, lean_object* v_b_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_591_, v_i_592_, v_stop_593_, v_b_594_, v___y_595_, v___y_596_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object* v_as_603_, lean_object* v_i_604_, lean_object* v_stop_605_, lean_object* v_b_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
size_t v_i_boxed_614_; size_t v_stop_boxed_615_; lean_object* v_res_616_; 
v_i_boxed_614_ = lean_unbox_usize(v_i_604_);
lean_dec(v_i_604_);
v_stop_boxed_615_ = lean_unbox_usize(v_stop_605_);
lean_dec(v_stop_605_);
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(v_as_603_, v_i_boxed_614_, v_stop_boxed_615_, v_b_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec_ref(v_as_603_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object* v_as_617_, size_t v_sz_618_, size_t v_i_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_617_, v_sz_618_, v_i_619_, v_b_620_, v___y_621_, v___y_622_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object* v_as_629_, lean_object* v_sz_630_, lean_object* v_i_631_, lean_object* v_b_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
size_t v_sz_boxed_640_; size_t v_i_boxed_641_; lean_object* v_res_642_; 
v_sz_boxed_640_ = lean_unbox_usize(v_sz_630_);
lean_dec(v_sz_630_);
v_i_boxed_641_ = lean_unbox_usize(v_i_631_);
lean_dec(v_i_631_);
v_res_642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(v_as_629_, v_sz_boxed_640_, v_i_boxed_641_, v_b_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec_ref(v_as_629_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object* v_inst_643_, lean_object* v_R_644_, lean_object* v_a_645_, lean_object* v_b_646_, lean_object* v_c_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_645_, v_b_646_, v___y_648_, v___y_649_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object* v_inst_656_, lean_object* v_R_657_, lean_object* v_a_658_, lean_object* v_b_659_, lean_object* v_c_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(v_inst_656_, v_R_657_, v_a_658_, v_b_659_, v_c_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object* v_inst_669_, lean_object* v_R_670_, lean_object* v_a_671_, lean_object* v_b_672_, lean_object* v_c_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_671_, v_b_672_, v___y_674_, v___y_675_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object* v_inst_682_, lean_object* v_R_683_, lean_object* v_a_684_, lean_object* v_b_685_, lean_object* v_c_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(v_inst_682_, v_R_683_, v_a_684_, v_b_685_, v_c_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object* v_code_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_decl_704_; lean_object* v_k_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; 
switch(lean_obj_tag(v_code_695_))
{
case 0:
{
lean_object* v_decl_715_; lean_object* v_k_716_; lean_object* v_value_717_; lean_object* v___x_718_; 
v_decl_715_ = lean_ctor_get(v_code_695_, 0);
lean_inc_ref(v_decl_715_);
v_k_716_ = lean_ctor_get(v_code_695_, 1);
lean_inc_ref(v_k_716_);
lean_dec_ref_known(v_code_695_, 2);
v_value_717_ = lean_ctor_get(v_decl_715_, 3);
lean_inc(v_value_717_);
lean_dec_ref(v_decl_715_);
v___x_718_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_value_717_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_dec_ref_known(v___x_718_, 1);
v_code_695_ = v_k_716_;
goto _start;
}
else
{
lean_dec_ref(v_k_716_);
return v___x_718_;
}
}
case 3:
{
lean_object* v_args_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_args_720_ = lean_ctor_get(v_code_695_, 1);
lean_inc_ref(v_args_720_);
lean_dec_ref_known(v_code_695_, 2);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_array_get_size(v_args_720_);
v___x_723_ = lean_box(0);
v___x_724_ = lean_nat_dec_lt(v___x_721_, v___x_722_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_dec_ref(v_args_720_);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
return v___x_725_;
}
else
{
uint8_t v___x_726_; 
v___x_726_ = lean_nat_dec_le(v___x_722_, v___x_722_);
if (v___x_726_ == 0)
{
if (v___x_724_ == 0)
{
lean_object* v___x_727_; 
lean_dec_ref(v_args_720_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_723_);
return v___x_727_;
}
else
{
size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v___x_728_ = ((size_t)0ULL);
v___x_729_ = lean_usize_of_nat(v___x_722_);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_720_, v___x_728_, v___x_729_, v___x_723_, v_a_696_, v_a_697_);
lean_dec_ref(v_args_720_);
return v___x_730_;
}
}
else
{
size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; 
v___x_731_ = ((size_t)0ULL);
v___x_732_ = lean_usize_of_nat(v___x_722_);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_720_, v___x_731_, v___x_732_, v___x_723_, v_a_696_, v_a_697_);
lean_dec_ref(v_args_720_);
return v___x_733_;
}
}
}
case 4:
{
lean_object* v_cases_734_; lean_object* v_discr_735_; lean_object* v_alts_736_; lean_object* v___x_737_; 
v_cases_734_ = lean_ctor_get(v_code_695_, 0);
lean_inc_ref(v_cases_734_);
lean_dec_ref_known(v_code_695_, 1);
v_discr_735_ = lean_ctor_get(v_cases_734_, 2);
lean_inc(v_discr_735_);
v_alts_736_ = lean_ctor_get(v_cases_734_, 3);
lean_inc_ref(v_alts_736_);
lean_dec_ref(v_cases_734_);
v___x_737_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_discr_735_, v_a_696_, v_a_697_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_758_; 
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v___x_737_, 0);
lean_dec(v_unused_759_);
v___x_739_ = v___x_737_;
v_isShared_740_ = v_isSharedCheck_758_;
goto v_resetjp_738_;
}
else
{
lean_dec(v___x_737_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_758_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_array_get_size(v_alts_736_);
v___x_743_ = lean_box(0);
v___x_744_ = lean_nat_dec_lt(v___x_741_, v___x_742_);
if (v___x_744_ == 0)
{
lean_object* v___x_746_; 
lean_dec_ref(v_alts_736_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_743_);
v___x_746_ = v___x_739_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_743_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
uint8_t v___x_748_; 
v___x_748_ = lean_nat_dec_le(v___x_742_, v___x_742_);
if (v___x_748_ == 0)
{
if (v___x_744_ == 0)
{
lean_object* v___x_750_; 
lean_dec_ref(v_alts_736_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_743_);
v___x_750_ = v___x_739_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_743_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
lean_del_object(v___x_739_);
v___x_752_ = ((size_t)0ULL);
v___x_753_ = lean_usize_of_nat(v___x_742_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_736_, v___x_752_, v___x_753_, v___x_743_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec_ref(v_alts_736_);
return v___x_754_;
}
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
lean_del_object(v___x_739_);
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_742_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_736_, v___x_755_, v___x_756_, v___x_743_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_);
lean_dec_ref(v_alts_736_);
return v___x_757_;
}
}
}
}
else
{
lean_dec_ref(v_alts_736_);
return v___x_737_;
}
}
case 5:
{
lean_object* v_fvarId_760_; lean_object* v___x_761_; 
v_fvarId_760_ = lean_ctor_get(v_code_695_, 0);
lean_inc(v_fvarId_760_);
lean_dec_ref_known(v_code_695_, 1);
v___x_761_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_760_, v_a_696_, v_a_697_);
return v___x_761_;
}
case 6:
{
lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
v_isSharedCheck_769_ = !lean_is_exclusive(v_code_695_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v_code_695_, 0);
lean_dec(v_unused_770_);
v___x_763_ = v_code_695_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_dec(v_code_695_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_box(0);
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 0);
lean_ctor_set(v___x_763_, 0, v___x_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
default: 
{
lean_object* v_decl_771_; lean_object* v_k_772_; 
v_decl_771_ = lean_ctor_get(v_code_695_, 0);
lean_inc_ref(v_decl_771_);
v_k_772_ = lean_ctor_get(v_code_695_, 1);
lean_inc_ref(v_k_772_);
lean_dec_ref(v_code_695_);
v_decl_704_ = v_decl_771_;
v_k_705_ = v_k_772_;
v___y_706_ = v_a_696_;
v___y_707_ = v_a_697_;
v___y_708_ = v_a_698_;
v___y_709_ = v_a_699_;
v___y_710_ = v_a_700_;
v___y_711_ = v_a_701_;
goto v___jp_703_;
}
}
v___jp_703_:
{
lean_object* v_value_712_; lean_object* v___x_713_; 
v_value_712_ = lean_ctor_get(v_decl_704_, 4);
lean_inc_ref(v_value_712_);
lean_dec_ref(v_decl_704_);
v___x_713_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_value_712_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_dec_ref_known(v___x_713_, 1);
v_code_695_ = v_k_705_;
v_a_696_ = v___y_706_;
v_a_697_ = v___y_707_;
v_a_698_ = v___y_708_;
v_a_699_ = v___y_709_;
v_a_700_ = v___y_710_;
v_a_701_ = v___y_711_;
goto _start;
}
else
{
lean_dec_ref(v_k_705_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object* v_as_773_, size_t v_i_774_, size_t v_stop_775_, lean_object* v_b_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___y_785_; uint8_t v___x_791_; 
v___x_791_ = lean_usize_dec_eq(v_i_774_, v_stop_775_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
v___x_792_ = lean_array_uget_borrowed(v_as_773_, v_i_774_);
switch(lean_obj_tag(v___x_792_))
{
case 0:
{
lean_object* v_code_793_; 
v_code_793_ = lean_ctor_get(v___x_792_, 2);
lean_inc_ref(v_code_793_);
v___y_785_ = v_code_793_;
goto v___jp_784_;
}
case 1:
{
lean_object* v_code_794_; 
v_code_794_ = lean_ctor_get(v___x_792_, 1);
lean_inc_ref(v_code_794_);
v___y_785_ = v_code_794_;
goto v___jp_784_;
}
default: 
{
lean_object* v_code_795_; 
v_code_795_ = lean_ctor_get(v___x_792_, 0);
lean_inc_ref(v_code_795_);
v___y_785_ = v_code_795_;
goto v___jp_784_;
}
}
}
else
{
lean_object* v___x_796_; 
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v_b_776_);
return v___x_796_;
}
v___jp_784_:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Compiler_LCNF_FindUsed_visit(v___y_785_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; size_t v___x_788_; size_t v___x_789_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v___x_788_ = ((size_t)1ULL);
v___x_789_ = lean_usize_add(v_i_774_, v___x_788_);
v_i_774_ = v___x_789_;
v_b_776_ = v_a_787_;
goto _start;
}
else
{
return v___x_786_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object* v_as_797_, lean_object* v_i_798_, lean_object* v_stop_799_, lean_object* v_b_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
size_t v_i_boxed_808_; size_t v_stop_boxed_809_; lean_object* v_res_810_; 
v_i_boxed_808_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_stop_boxed_809_ = lean_unbox_usize(v_stop_799_);
lean_dec(v_stop_799_);
v_res_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_as_797_, v_i_boxed_808_, v_stop_boxed_809_, v_b_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_as_797_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object* v_code_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_code_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(lean_object* v_f_820_, lean_object* v_v_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
if (lean_obj_tag(v_v_821_) == 0)
{
lean_object* v_code_829_; lean_object* v___x_830_; 
v_code_829_ = lean_ctor_get(v_v_821_, 0);
lean_inc_ref(v_code_829_);
lean_dec_ref_known(v_v_821_, 1);
lean_inc(v___y_827_);
lean_inc_ref(v___y_826_);
lean_inc(v___y_825_);
lean_inc_ref(v___y_824_);
lean_inc(v___y_823_);
lean_inc_ref(v___y_822_);
v___x_830_ = lean_apply_8(v_f_820_, v_code_829_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, lean_box(0));
return v___x_830_;
}
else
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_f_820_);
v_isSharedCheck_838_ = !lean_is_exclusive(v_v_821_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_v_821_, 0);
lean_dec(v_unused_839_);
v___x_832_ = v_v_821_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_dec(v_v_821_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_box(0);
if (v_isShared_833_ == 0)
{
lean_ctor_set_tag(v___x_832_, 0);
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg___boxed(lean_object* v_f_840_, lean_object* v_v_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_840_, v_v_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(uint8_t v_pu_850_, lean_object* v_f_851_, lean_object* v_v_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_851_, v_v_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___boxed(lean_object* v_pu_861_, lean_object* v_f_862_, lean_object* v_v_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
uint8_t v_pu_boxed_871_; lean_object* v_res_872_; 
v_pu_boxed_871_ = lean_unbox(v_pu_861_);
v_res_872_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(v_pu_boxed_871_, v_f_862_, v_v_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object* v_as_873_, size_t v_i_874_, size_t v_stop_875_, lean_object* v_b_876_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = lean_usize_dec_eq(v_i_874_, v_stop_875_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v_fvarId_879_; lean_object* v___x_880_; size_t v___x_881_; size_t v___x_882_; 
v___x_878_ = lean_array_uget_borrowed(v_as_873_, v_i_874_);
v_fvarId_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_fvarId_879_);
v___x_880_ = l_Lean_FVarIdSet_insert(v_b_876_, v_fvarId_879_);
v___x_881_ = ((size_t)1ULL);
v___x_882_ = lean_usize_add(v_i_874_, v___x_881_);
v_i_874_ = v___x_882_;
v_b_876_ = v___x_880_;
goto _start;
}
else
{
return v_b_876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object* v_as_884_, lean_object* v_i_885_, lean_object* v_stop_886_, lean_object* v_b_887_){
_start:
{
size_t v_i_boxed_888_; size_t v_stop_boxed_889_; lean_object* v_res_890_; 
v_i_boxed_888_ = lean_unbox_usize(v_i_885_);
lean_dec(v_i_885_);
v_stop_boxed_889_ = lean_unbox_usize(v_stop_886_);
lean_dec(v_stop_886_);
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_as_884_, v_i_boxed_888_, v_stop_boxed_889_, v_b_887_);
lean_dec_ref(v_as_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object* v_decl_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_toSignature_898_; lean_object* v_value_899_; lean_object* v_params_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___y_904_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_toSignature_898_ = lean_ctor_get(v_decl_892_, 0);
v_value_899_ = lean_ctor_get(v_decl_892_, 1);
lean_inc_ref(v_value_899_);
v_params_900_ = lean_ctor_get(v_toSignature_898_, 3);
v___x_901_ = lean_box(1);
v___x_902_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_array_get_size(v_params_900_);
v___x_928_ = lean_nat_dec_lt(v___x_926_, v___x_927_);
if (v___x_928_ == 0)
{
v___y_904_ = v___x_901_;
goto v___jp_903_;
}
else
{
uint8_t v___x_929_; 
v___x_929_ = lean_nat_dec_le(v___x_927_, v___x_927_);
if (v___x_929_ == 0)
{
if (v___x_928_ == 0)
{
v___y_904_ = v___x_901_;
goto v___jp_903_;
}
else
{
size_t v___x_930_; size_t v___x_931_; lean_object* v___x_932_; 
v___x_930_ = ((size_t)0ULL);
v___x_931_ = lean_usize_of_nat(v___x_927_);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_900_, v___x_930_, v___x_931_, v___x_901_);
v___y_904_ = v___x_932_;
goto v___jp_903_;
}
}
else
{
size_t v___x_933_; size_t v___x_934_; lean_object* v___x_935_; 
v___x_933_ = ((size_t)0ULL);
v___x_934_ = lean_usize_of_nat(v___x_927_);
v___x_935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_900_, v___x_933_, v___x_934_, v___x_901_);
v___y_904_ = v___x_935_;
goto v___jp_903_;
}
}
v___jp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_905_ = lean_st_mk_ref(v___x_902_);
v___x_906_ = ((lean_object*)(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0));
v___x_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_907_, 0, v_decl_892_);
lean_ctor_set(v___x_907_, 1, v___y_904_);
v___x_908_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v___x_906_, v_value_899_, v___x_907_, v___x_905_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec_ref_known(v___x_907_, 2);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v___x_908_, 0);
lean_dec(v_unused_917_);
v___x_910_ = v___x_908_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_dec(v___x_908_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_st_ref_get(v___x_905_);
lean_dec(v___x_905_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v___x_905_);
v_a_918_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_908_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_908_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(lean_object* v_decl_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
return v_res_942_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0(void){
_start:
{
uint8_t v___x_943_; lean_object* v___x_944_; 
v___x_943_ = 0;
v___x_944_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object* v_msg_945_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0);
v___x_947_ = lean_panic_fn_borrowed(v___x_946_, v_msg_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(lean_object* v_args_948_, lean_object* v_upperBound_949_, lean_object* v___x_950_, lean_object* v_a_951_, lean_object* v_b_952_){
_start:
{
lean_object* v_a_955_; uint8_t v___x_962_; 
v___x_962_ = lean_nat_dec_lt(v_a_951_, v_upperBound_949_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec(v_a_951_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_b_952_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = lean_array_get_size(v___x_950_);
v___x_965_ = lean_nat_dec_lt(v_a_951_, v___x_964_);
if (v___x_965_ == 0)
{
goto v___jp_959_;
}
else
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_array_fget_borrowed(v___x_950_, v_a_951_);
v___x_967_ = lean_unbox(v___x_966_);
if (v___x_967_ == 0)
{
v_a_955_ = v_b_952_;
goto v___jp_954_;
}
else
{
goto v___jp_959_;
}
}
}
v___jp_954_:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_add(v_a_951_, v___x_956_);
lean_dec(v_a_951_);
v_a_951_ = v___x_957_;
v_b_952_ = v_a_955_;
goto _start;
}
v___jp_959_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_array_fget_borrowed(v_args_948_, v_a_951_);
lean_inc(v___x_960_);
v___x_961_ = lean_array_push(v_b_952_, v___x_960_);
v_a_955_ = v___x_961_;
goto v___jp_954_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(lean_object* v_args_968_, lean_object* v_upperBound_969_, lean_object* v___x_970_, lean_object* v_a_971_, lean_object* v_b_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_968_, v_upperBound_969_, v___x_970_, v_a_971_, v_b_972_);
lean_dec_ref(v___x_970_);
lean_dec(v_upperBound_969_);
lean_dec_ref(v_args_968_);
return v_res_974_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_978_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2));
v___x_979_ = lean_unsigned_to_nat(9u);
v___x_980_ = lean_unsigned_to_nat(641u);
v___x_981_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1));
v___x_982_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0));
v___x_983_ = l_mkPanicMessageWithDecl(v___x_982_, v___x_981_, v___x_980_, v___x_979_, v___x_978_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* v_code_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___y_994_; lean_object* v___y_995_; uint8_t v___y_996_; lean_object* v___y_1001_; lean_object* v___y_1002_; uint8_t v___y_1003_; lean_object* v_decl_1008_; lean_object* v_k_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; 
switch(lean_obj_tag(v_code_986_))
{
case 0:
{
lean_object* v_decl_1060_; lean_object* v_value_1061_; 
v_decl_1060_ = lean_ctor_get(v_code_986_, 0);
v_value_1061_ = lean_ctor_get(v_decl_1060_, 3);
lean_inc(v_value_1061_);
if (lean_obj_tag(v_value_1061_) == 3)
{
lean_object* v_k_1062_; lean_object* v_declName_1063_; lean_object* v_args_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1157_; 
v_k_1062_ = lean_ctor_get(v_code_986_, 1);
v_declName_1063_ = lean_ctor_get(v_value_1061_, 0);
v_args_1064_ = lean_ctor_get(v_value_1061_, 2);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_value_1061_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v_value_1061_, 1);
lean_dec(v_unused_1158_);
v___x_1066_ = v_value_1061_;
v_isShared_1067_ = v_isSharedCheck_1157_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_args_1064_);
lean_inc(v_declName_1063_);
lean_dec(v_value_1061_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1157_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_declName_1068_; lean_object* v_auxDeclName_1069_; lean_object* v_paramMask_1070_; uint8_t v___x_1071_; 
v_declName_1068_ = lean_ctor_get(v_a_987_, 0);
v_auxDeclName_1069_ = lean_ctor_get(v_a_987_, 1);
v_paramMask_1070_ = lean_ctor_get(v_a_987_, 2);
v___x_1071_ = lean_name_eq(v_declName_1063_, v_declName_1068_);
lean_dec(v_declName_1063_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_del_object(v___x_1066_);
lean_dec_ref(v_args_1064_);
lean_inc_ref(v_k_1062_);
v___x_1072_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_1062_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1099_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1099_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1099_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
uint8_t v___y_1078_; size_t v___x_1094_; size_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1094_ = lean_ptr_addr(v_k_1062_);
v___x_1095_ = lean_ptr_addr(v_a_1073_);
v___x_1096_ = lean_usize_dec_eq(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
v___y_1078_ = v___x_1096_;
goto v___jp_1077_;
}
else
{
size_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_ptr_addr(v_decl_1060_);
v___x_1098_ = lean_usize_dec_eq(v___x_1097_, v___x_1097_);
v___y_1078_ = v___x_1098_;
goto v___jp_1077_;
}
v___jp_1077_:
{
if (v___y_1078_ == 0)
{
lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1088_; 
lean_inc_ref(v_decl_1060_);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_code_986_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; lean_object* v_unused_1090_; 
v_unused_1089_ = lean_ctor_get(v_code_986_, 1);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_code_986_, 0);
lean_dec(v_unused_1090_);
v___x_1080_ = v_code_986_;
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
else
{
lean_dec(v_code_986_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v_a_1073_);
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_decl_1060_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_a_1073_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1083_);
v___x_1085_ = v___x_1075_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v___x_1092_; 
lean_dec(v_a_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v_code_986_);
v___x_1092_ = v___x_1075_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_code_986_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_986_, 2);
return v___x_1072_;
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = lean_array_get_size(v_args_1064_);
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_1103_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1064_, v___x_1100_, v_paramMask_1070_, v___x_1101_, v___x_1102_);
lean_dec_ref(v_args_1064_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = 0;
v___x_1106_ = lean_box(0);
lean_inc(v_auxDeclName_1069_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 2, v_a_1104_);
lean_ctor_set(v___x_1066_, 1, v___x_1106_);
lean_ctor_set(v___x_1066_, 0, v_auxDeclName_1069_);
v___x_1108_ = v___x_1066_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_auxDeclName_1069_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_a_1104_);
v___x_1108_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; 
lean_inc_ref(v_decl_1060_);
v___x_1109_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1105_, v_decl_1060_, v___x_1108_, v_a_989_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1111_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
lean_inc_ref(v_k_1062_);
v___x_1111_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_1062_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1139_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1139_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1139_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
uint8_t v___y_1117_; size_t v___x_1133_; size_t v___x_1134_; uint8_t v___x_1135_; 
v___x_1133_ = lean_ptr_addr(v_k_1062_);
v___x_1134_ = lean_ptr_addr(v_a_1112_);
v___x_1135_ = lean_usize_dec_eq(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
v___y_1117_ = v___x_1135_;
goto v___jp_1116_;
}
else
{
size_t v___x_1136_; size_t v___x_1137_; uint8_t v___x_1138_; 
v___x_1136_ = lean_ptr_addr(v_decl_1060_);
v___x_1137_ = lean_ptr_addr(v_a_1110_);
v___x_1138_ = lean_usize_dec_eq(v___x_1136_, v___x_1137_);
v___y_1117_ = v___x_1138_;
goto v___jp_1116_;
}
v___jp_1116_:
{
if (v___y_1117_ == 0)
{
lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1127_; 
v_isSharedCheck_1127_ = !lean_is_exclusive(v_code_986_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; lean_object* v_unused_1129_; 
v_unused_1128_ = lean_ctor_get(v_code_986_, 1);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_code_986_, 0);
lean_dec(v_unused_1129_);
v___x_1119_ = v_code_986_;
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
else
{
lean_dec(v_code_986_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 1, v_a_1112_);
lean_ctor_set(v___x_1119_, 0, v_a_1110_);
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1110_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_a_1112_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1122_);
v___x_1124_ = v___x_1114_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v___x_1131_; 
lean_dec(v_a_1112_);
lean_dec(v_a_1110_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v_code_986_);
v___x_1131_ = v___x_1114_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_code_986_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
else
{
lean_dec(v_a_1110_);
lean_dec_ref_known(v_code_986_, 2);
return v___x_1111_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref_known(v_code_986_, 2);
v_a_1140_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1109_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1109_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_del_object(v___x_1066_);
lean_dec_ref_known(v_code_986_, 2);
v_a_1149_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1103_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1103_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
}
else
{
lean_object* v_k_1159_; lean_object* v___x_1160_; 
lean_dec(v_value_1061_);
v_k_1159_ = lean_ctor_get(v_code_986_, 1);
lean_inc_ref(v_k_1159_);
v___x_1160_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_1159_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1187_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1187_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1187_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
uint8_t v___y_1166_; size_t v___x_1182_; size_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = lean_ptr_addr(v_k_1159_);
v___x_1183_ = lean_ptr_addr(v_a_1161_);
v___x_1184_ = lean_usize_dec_eq(v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
v___y_1166_ = v___x_1184_;
goto v___jp_1165_;
}
else
{
size_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = lean_ptr_addr(v_decl_1060_);
v___x_1186_ = lean_usize_dec_eq(v___x_1185_, v___x_1185_);
v___y_1166_ = v___x_1186_;
goto v___jp_1165_;
}
v___jp_1165_:
{
if (v___y_1166_ == 0)
{
lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1176_; 
lean_inc_ref(v_decl_1060_);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_code_986_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; lean_object* v_unused_1178_; 
v_unused_1177_ = lean_ctor_get(v_code_986_, 1);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_code_986_, 0);
lean_dec(v_unused_1178_);
v___x_1168_ = v_code_986_;
v_isShared_1169_ = v_isSharedCheck_1176_;
goto v_resetjp_1167_;
}
else
{
lean_dec(v_code_986_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1176_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_a_1161_);
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_decl_1060_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_a_1161_);
v___x_1171_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1173_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1171_);
v___x_1173_ = v___x_1163_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v___x_1180_; 
lean_dec(v_a_1161_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v_code_986_);
v___x_1180_ = v___x_1163_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_code_986_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_986_, 2);
return v___x_1160_;
}
}
}
case 1:
{
lean_object* v_decl_1188_; lean_object* v_k_1189_; 
v_decl_1188_ = lean_ctor_get(v_code_986_, 0);
v_k_1189_ = lean_ctor_get(v_code_986_, 1);
lean_inc_ref(v_k_1189_);
lean_inc_ref(v_decl_1188_);
v_decl_1008_ = v_decl_1188_;
v_k_1009_ = v_k_1189_;
v___y_1010_ = v_a_987_;
v___y_1011_ = v_a_988_;
v___y_1012_ = v_a_989_;
v___y_1013_ = v_a_990_;
v___y_1014_ = v_a_991_;
goto v___jp_1007_;
}
case 2:
{
lean_object* v_decl_1190_; lean_object* v_k_1191_; 
v_decl_1190_ = lean_ctor_get(v_code_986_, 0);
v_k_1191_ = lean_ctor_get(v_code_986_, 1);
lean_inc_ref(v_k_1191_);
lean_inc_ref(v_decl_1190_);
v_decl_1008_ = v_decl_1190_;
v_k_1009_ = v_k_1191_;
v___y_1010_ = v_a_987_;
v___y_1011_ = v_a_988_;
v___y_1012_ = v_a_989_;
v___y_1013_ = v_a_990_;
v___y_1014_ = v_a_991_;
goto v___jp_1007_;
}
case 4:
{
lean_object* v_cases_1192_; lean_object* v_typeName_1193_; lean_object* v_resultType_1194_; lean_object* v_discr_1195_; lean_object* v_alts_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1235_; 
v_cases_1192_ = lean_ctor_get(v_code_986_, 0);
lean_inc_ref(v_cases_1192_);
v_typeName_1193_ = lean_ctor_get(v_cases_1192_, 0);
v_resultType_1194_ = lean_ctor_get(v_cases_1192_, 1);
v_discr_1195_ = lean_ctor_get(v_cases_1192_, 2);
v_alts_1196_ = lean_ctor_get(v_cases_1192_, 3);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_cases_1192_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1198_ = v_cases_1192_;
v_isShared_1199_ = v_isSharedCheck_1235_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_alts_1196_);
lean_inc(v_discr_1195_);
lean_inc(v_resultType_1194_);
lean_inc(v_typeName_1193_);
lean_dec(v_cases_1192_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1235_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1196_);
v___x_1201_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v___x_1200_, v_alts_1196_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1226_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1226_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1226_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
size_t v___x_1206_; size_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1206_ = lean_ptr_addr(v_alts_1196_);
lean_dec_ref(v_alts_1196_);
v___x_1207_ = lean_ptr_addr(v_a_1202_);
v___x_1208_ = lean_usize_dec_eq(v___x_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1221_; 
v_isSharedCheck_1221_ = !lean_is_exclusive(v_code_986_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v_code_986_, 0);
lean_dec(v_unused_1222_);
v___x_1210_ = v_code_986_;
v_isShared_1211_ = v_isSharedCheck_1221_;
goto v_resetjp_1209_;
}
else
{
lean_dec(v_code_986_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1221_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 3, v_a_1202_);
v___x_1213_ = v___x_1198_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_typeName_1193_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_resultType_1194_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_discr_1195_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v_a_1202_);
v___x_1213_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1213_);
v___x_1215_ = v___x_1210_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1217_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1215_);
v___x_1217_ = v___x_1204_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
else
{
lean_object* v___x_1224_; 
lean_dec(v_a_1202_);
lean_del_object(v___x_1198_);
lean_dec(v_discr_1195_);
lean_dec_ref(v_resultType_1194_);
lean_dec(v_typeName_1193_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v_code_986_);
v___x_1224_ = v___x_1204_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_code_986_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_del_object(v___x_1198_);
lean_dec_ref(v_alts_1196_);
lean_dec(v_discr_1195_);
lean_dec_ref(v_resultType_1194_);
lean_dec(v_typeName_1193_);
lean_dec_ref_known(v_code_986_, 1);
v_a_1227_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1201_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1201_);
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
default: 
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_code_986_);
return v___x_1236_;
}
}
v___jp_993_:
{
if (v___y_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
lean_dec_ref(v_code_986_);
v___x_997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_997_, 0, v___y_995_);
lean_ctor_set(v___x_997_, 1, v___y_994_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
else
{
lean_object* v___x_999_; 
lean_dec_ref(v___y_995_);
lean_dec_ref(v___y_994_);
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v_code_986_);
return v___x_999_;
}
}
v___jp_1000_:
{
if (v___y_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_dec_ref(v_code_986_);
v___x_1004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___y_1002_);
lean_ctor_set(v___x_1004_, 1, v___y_1001_);
v___x_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; 
lean_dec_ref(v___y_1002_);
lean_dec_ref(v___y_1001_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v_code_986_);
return v___x_1006_;
}
}
v___jp_1007_:
{
lean_object* v_params_1015_; lean_object* v_type_1016_; lean_object* v_value_1017_; lean_object* v___x_1018_; 
v_params_1015_ = lean_ctor_get(v_decl_1008_, 2);
lean_inc_ref(v_params_1015_);
v_type_1016_ = lean_ctor_get(v_decl_1008_, 3);
lean_inc_ref(v_type_1016_);
v_value_1017_ = lean_ctor_get(v_decl_1008_, 4);
lean_inc_ref(v_value_1017_);
v___x_1018_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_value_1017_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; uint8_t v___x_1020_; lean_object* v___x_1021_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = 0;
v___x_1021_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1020_, v_decl_1008_, v_type_1016_, v_params_1015_, v_a_1019_, v___y_1012_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1023_) == 0)
{
switch(lean_obj_tag(v_code_986_))
{
case 1:
{
lean_object* v_a_1024_; lean_object* v_decl_1025_; lean_object* v_k_1026_; size_t v___x_1027_; size_t v___x_1028_; uint8_t v___x_1029_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1024_);
lean_dec_ref_known(v___x_1023_, 1);
v_decl_1025_ = lean_ctor_get(v_code_986_, 0);
v_k_1026_ = lean_ctor_get(v_code_986_, 1);
v___x_1027_ = lean_ptr_addr(v_k_1026_);
v___x_1028_ = lean_ptr_addr(v_a_1024_);
v___x_1029_ = lean_usize_dec_eq(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
v___y_994_ = v_a_1024_;
v___y_995_ = v_a_1022_;
v___y_996_ = v___x_1029_;
goto v___jp_993_;
}
else
{
size_t v___x_1030_; size_t v___x_1031_; uint8_t v___x_1032_; 
v___x_1030_ = lean_ptr_addr(v_decl_1025_);
v___x_1031_ = lean_ptr_addr(v_a_1022_);
v___x_1032_ = lean_usize_dec_eq(v___x_1030_, v___x_1031_);
v___y_994_ = v_a_1024_;
v___y_995_ = v_a_1022_;
v___y_996_ = v___x_1032_;
goto v___jp_993_;
}
}
case 2:
{
lean_object* v_a_1033_; lean_object* v_decl_1034_; lean_object* v_k_1035_; size_t v___x_1036_; size_t v___x_1037_; uint8_t v___x_1038_; 
v_a_1033_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1023_, 1);
v_decl_1034_ = lean_ctor_get(v_code_986_, 0);
v_k_1035_ = lean_ctor_get(v_code_986_, 1);
v___x_1036_ = lean_ptr_addr(v_k_1035_);
v___x_1037_ = lean_ptr_addr(v_a_1033_);
v___x_1038_ = lean_usize_dec_eq(v___x_1036_, v___x_1037_);
if (v___x_1038_ == 0)
{
v___y_1001_ = v_a_1033_;
v___y_1002_ = v_a_1022_;
v___y_1003_ = v___x_1038_;
goto v___jp_1000_;
}
else
{
size_t v___x_1039_; size_t v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = lean_ptr_addr(v_decl_1034_);
v___x_1040_ = lean_ptr_addr(v_a_1022_);
v___x_1041_ = lean_usize_dec_eq(v___x_1039_, v___x_1040_);
v___y_1001_ = v_a_1033_;
v___y_1002_ = v_a_1022_;
v___y_1003_ = v___x_1041_;
goto v___jp_1000_;
}
}
default: 
{
lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1050_; 
lean_dec(v_a_1022_);
lean_dec_ref(v_code_986_);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v___x_1023_, 0);
lean_dec(v_unused_1051_);
v___x_1043_ = v___x_1023_;
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
else
{
lean_dec(v___x_1023_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1045_ = lean_obj_once(&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3, &l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once, _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3);
v___x_1046_ = l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(v___x_1045_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1046_);
v___x_1048_ = v___x_1043_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
lean_dec(v_a_1022_);
lean_dec_ref(v_code_986_);
return v___x_1023_;
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v_k_1009_);
lean_dec_ref(v_code_986_);
v_a_1052_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1021_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1021_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_dec_ref(v_type_1016_);
lean_dec_ref(v_params_1015_);
lean_dec_ref(v_k_1009_);
lean_dec_ref(v_decl_1008_);
lean_dec_ref(v_code_986_);
return v___x_1018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(lean_object* v_i_1237_, lean_object* v_as_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = lean_array_get_size(v_as_1238_);
v___x_1246_ = lean_nat_dec_lt(v_i_1237_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
lean_dec(v_i_1237_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v_as_1238_);
return v___x_1247_;
}
else
{
lean_object* v_a_1248_; lean_object* v___y_1250_; 
v_a_1248_ = lean_array_fget_borrowed(v_as_1238_, v_i_1237_);
switch(lean_obj_tag(v_a_1248_))
{
case 0:
{
lean_object* v_code_1272_; 
v_code_1272_ = lean_ctor_get(v_a_1248_, 2);
lean_inc_ref(v_code_1272_);
v___y_1250_ = v_code_1272_;
goto v___jp_1249_;
}
case 1:
{
lean_object* v_code_1273_; 
v_code_1273_ = lean_ctor_get(v_a_1248_, 1);
lean_inc_ref(v_code_1273_);
v___y_1250_ = v_code_1273_;
goto v___jp_1249_;
}
default: 
{
lean_object* v_code_1274_; 
v_code_1274_ = lean_ctor_get(v_a_1248_, 0);
lean_inc_ref(v_code_1274_);
v___y_1250_ = v_code_1274_;
goto v___jp_1249_;
}
}
v___jp_1249_:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v___y_1250_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v___x_1253_; size_t v___x_1254_; size_t v___x_1255_; uint8_t v___x_1256_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
lean_inc(v_a_1248_);
v___x_1253_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1248_, v_a_1252_);
v___x_1254_ = lean_ptr_addr(v_a_1248_);
v___x_1255_ = lean_ptr_addr(v___x_1253_);
v___x_1256_ = lean_usize_dec_eq(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_add(v_i_1237_, v___x_1257_);
v___x_1259_ = lean_array_fset(v_as_1238_, v_i_1237_, v___x_1253_);
lean_dec(v_i_1237_);
v_i_1237_ = v___x_1258_;
v_as_1238_ = v___x_1259_;
goto _start;
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec_ref(v___x_1253_);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = lean_nat_add(v_i_1237_, v___x_1261_);
lean_dec(v_i_1237_);
v_i_1237_ = v___x_1262_;
goto _start;
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_as_1238_);
lean_dec(v_i_1237_);
v_a_1264_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1251_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1251_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(lean_object* v_i_1275_, lean_object* v_as_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v_i_1275_, v_as_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object* v_code_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_code_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec_ref(v_a_1285_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object* v_args_1292_, lean_object* v_upperBound_1293_, lean_object* v___x_1294_, lean_object* v_inst_1295_, lean_object* v_R_1296_, lean_object* v_a_1297_, lean_object* v_b_1298_, lean_object* v_c_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1292_, v_upperBound_1293_, v___x_1294_, v_a_1297_, v_b_1298_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object* v_args_1307_, lean_object* v_upperBound_1308_, lean_object* v___x_1309_, lean_object* v_inst_1310_, lean_object* v_R_1311_, lean_object* v_a_1312_, lean_object* v_b_1313_, lean_object* v_c_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(v_args_1307_, v_upperBound_1308_, v___x_1309_, v_inst_1310_, v_R_1311_, v_a_1312_, v_b_1313_, v_c_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec_ref(v___x_1309_);
lean_dec(v_upperBound_1308_);
lean_dec_ref(v_args_1307_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object* v_f_1322_, lean_object* v_v_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
if (lean_obj_tag(v_v_1323_) == 0)
{
lean_object* v_code_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1354_; 
v_code_1330_ = lean_ctor_get(v_v_1323_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_v_1323_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1332_ = v_v_1323_;
v_isShared_1333_ = v_isSharedCheck_1354_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_code_1330_);
lean_dec(v_v_1323_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1354_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; 
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
lean_inc_ref(v___y_1324_);
v___x_1334_ = lean_apply_7(v_f_1322_, v_code_1330_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, lean_box(0));
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1345_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1345_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1345_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v_a_1335_);
v___x_1340_ = v___x_1332_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1342_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1340_);
v___x_1342_ = v___x_1337_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_del_object(v___x_1332_);
v_a_1346_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1334_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1334_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
else
{
lean_object* v___x_1355_; 
lean_dec_ref(v_f_1322_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_v_1323_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object* v_f_1356_, lean_object* v_v_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1356_, v_v_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(uint8_t v_pu_1365_, lean_object* v_f_1366_, lean_object* v_v_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1366_, v_v_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object* v_pu_1375_, lean_object* v_f_1376_, lean_object* v_v_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v_pu_boxed_1384_; lean_object* v_res_1385_; 
v_pu_boxed_1384_ = lean_unbox(v_pu_1375_);
v_res_1385_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(v_pu_boxed_1384_, v_f_1376_, v_v_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1385_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0(void){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1386_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1(void){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1);
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
lean_ctor_set(v___x_1391_, 2, v___x_1390_);
lean_ctor_set(v___x_1391_, 3, v___x_1390_);
lean_ctor_set(v___x_1391_, 4, v___x_1389_);
lean_ctor_set(v___x_1391_, 5, v___x_1389_);
lean_ctor_set(v___x_1391_, 6, v___x_1389_);
lean_ctor_set(v___x_1391_, 7, v___x_1389_);
lean_ctor_set(v___x_1391_, 8, v___x_1389_);
lean_ctor_set(v___x_1391_, 9, v___x_1389_);
lean_ctor_set(v___x_1391_, 10, v___x_1389_);
return v___x_1391_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3(void){
_start:
{
lean_object* v___x_1392_; double v___x_1393_; 
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = lean_float_of_nat(v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* v_cls_1397_, lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_options_1404_; lean_object* v_ref_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_options_1404_ = lean_ctor_get(v___y_1401_, 2);
v_ref_1405_ = lean_ctor_get(v___y_1401_, 5);
v___x_1406_ = lean_st_ref_get(v___y_1402_);
v___x_1407_ = lean_st_ref_get(v___y_1400_);
v___x_1408_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1399_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1467_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1467_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1467_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_env_1413_; lean_object* v_lctx_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1465_; 
v_env_1413_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_env_1413_);
lean_dec(v___x_1406_);
v_lctx_1414_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1407_, 1);
lean_dec(v_unused_1466_);
v___x_1416_ = v___x_1407_;
v_isShared_1417_ = v_isSharedCheck_1465_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_lctx_1414_);
lean_dec(v___x_1407_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1465_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v_traceState_1420_; lean_object* v_env_1421_; lean_object* v_nextMacroScope_1422_; lean_object* v_ngen_1423_; lean_object* v_auxDeclNGen_1424_; lean_object* v_cache_1425_; lean_object* v_messages_1426_; lean_object* v_infoState_1427_; lean_object* v_snapshotTasks_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1464_; 
v___x_1418_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2);
v___x_1419_ = lean_st_ref_take(v___y_1402_);
v_traceState_1420_ = lean_ctor_get(v___x_1419_, 4);
v_env_1421_ = lean_ctor_get(v___x_1419_, 0);
v_nextMacroScope_1422_ = lean_ctor_get(v___x_1419_, 1);
v_ngen_1423_ = lean_ctor_get(v___x_1419_, 2);
v_auxDeclNGen_1424_ = lean_ctor_get(v___x_1419_, 3);
v_cache_1425_ = lean_ctor_get(v___x_1419_, 5);
v_messages_1426_ = lean_ctor_get(v___x_1419_, 6);
v_infoState_1427_ = lean_ctor_get(v___x_1419_, 7);
v_snapshotTasks_1428_ = lean_ctor_get(v___x_1419_, 8);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1430_ = v___x_1419_;
v_isShared_1431_ = v_isSharedCheck_1464_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_snapshotTasks_1428_);
lean_inc(v_infoState_1427_);
lean_inc(v_messages_1426_);
lean_inc(v_cache_1425_);
lean_inc(v_traceState_1420_);
lean_inc(v_auxDeclNGen_1424_);
lean_inc(v_ngen_1423_);
lean_inc(v_nextMacroScope_1422_);
lean_inc(v_env_1421_);
lean_dec(v___x_1419_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1464_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
uint64_t v_tid_1432_; lean_object* v_traces_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1463_; 
v_tid_1432_ = lean_ctor_get_uint64(v_traceState_1420_, sizeof(void*)*1);
v_traces_1433_ = lean_ctor_get(v_traceState_1420_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_traceState_1420_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1435_ = v_traceState_1420_;
v_isShared_1436_ = v_isSharedCheck_1463_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_traces_1433_);
lean_dec(v_traceState_1420_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1463_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1437_ = lean_unbox(v_a_1409_);
lean_dec(v_a_1409_);
v___x_1438_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1414_, v___x_1437_);
lean_dec_ref(v_lctx_1414_);
lean_inc_ref(v_options_1404_);
v___x_1439_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1439_, 0, v_env_1413_);
lean_ctor_set(v___x_1439_, 1, v___x_1418_);
lean_ctor_set(v___x_1439_, 2, v___x_1438_);
lean_ctor_set(v___x_1439_, 3, v_options_1404_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 3);
lean_ctor_set(v___x_1416_, 1, v_msg_1398_);
lean_ctor_set(v___x_1416_, 0, v___x_1439_);
v___x_1441_ = v___x_1416_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_msg_1398_);
v___x_1441_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; double v___x_1443_; uint8_t v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1442_ = lean_box(0);
v___x_1443_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3);
v___x_1444_ = 0;
v___x_1445_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4));
v___x_1446_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1446_, 0, v_cls_1397_);
lean_ctor_set(v___x_1446_, 1, v___x_1442_);
lean_ctor_set(v___x_1446_, 2, v___x_1445_);
lean_ctor_set_float(v___x_1446_, sizeof(void*)*3, v___x_1443_);
lean_ctor_set_float(v___x_1446_, sizeof(void*)*3 + 8, v___x_1443_);
lean_ctor_set_uint8(v___x_1446_, sizeof(void*)*3 + 16, v___x_1444_);
v___x_1447_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5));
v___x_1448_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
lean_ctor_set(v___x_1448_, 1, v___x_1441_);
lean_ctor_set(v___x_1448_, 2, v___x_1447_);
lean_inc(v_ref_1405_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v_ref_1405_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = l_Lean_PersistentArray_push___redArg(v_traces_1433_, v___x_1449_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1450_);
v___x_1452_ = v___x_1435_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1450_);
lean_ctor_set_uint64(v_reuseFailAlloc_1461_, sizeof(void*)*1, v_tid_1432_);
v___x_1452_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1454_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v___x_1452_);
v___x_1454_ = v___x_1430_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_env_1421_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_nextMacroScope_1422_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_ngen_1423_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_auxDeclNGen_1424_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1460_, 5, v_cache_1425_);
lean_ctor_set(v_reuseFailAlloc_1460_, 6, v_messages_1426_);
lean_ctor_set(v_reuseFailAlloc_1460_, 7, v_infoState_1427_);
lean_ctor_set(v_reuseFailAlloc_1460_, 8, v_snapshotTasks_1428_);
v___x_1454_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1455_ = lean_st_ref_put(v___y_1402_, v___x_1454_);
v___x_1456_ = lean_box(0);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1456_);
v___x_1458_ = v___x_1411_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v___x_1407_);
lean_dec(v___x_1406_);
lean_dec_ref(v_msg_1398_);
lean_dec(v_cls_1397_);
v_a_1468_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1408_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1408_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object* v_cls_1476_, lean_object* v_msg_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_cls_1476_, v_msg_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0___redArg(lean_object* v_m_1484_, lean_object* v_query_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v_m_1484_, v_query_1485_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_index_1487_; lean_object* v_key_1488_; lean_object* v_value_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_index_1487_ = lean_ctor_get(v___x_1486_, 0);
v_key_1488_ = lean_ctor_get(v___x_1486_, 1);
v_value_1489_ = lean_ctor_get(v___x_1486_, 2);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1486_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_value_1489_);
lean_inc(v_key_1488_);
lean_inc(v_index_1487_);
lean_dec(v___x_1486_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_index_1487_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_key_1488_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_value_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
else
{
lean_object* v___x_1497_; 
lean_dec(v___x_1486_);
v___x_1497_ = lean_box(1);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0___redArg___boxed(lean_object* v_m_1498_, lean_object* v_query_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0___redArg(v_m_1498_, v_query_1499_);
lean_dec(v_query_1499_);
lean_dec_ref(v_m_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object* v_m_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0___redArg(v_m_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1503_) == 0)
{
uint8_t v___x_1504_; 
lean_dec_ref_known(v___x_1503_, 3);
v___x_1504_ = 1;
return v___x_1504_;
}
else
{
uint8_t v___x_1505_; 
v___x_1505_ = 0;
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object* v_m_1506_, lean_object* v_a_1507_){
_start:
{
uint8_t v_res_1508_; lean_object* v_r_1509_; 
v_res_1508_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_m_1506_);
v_r_1509_ = lean_box(v_res_1508_);
return v_r_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__8(lean_object* v_a_1510_, lean_object* v_as_1511_, size_t v_i_1512_, size_t v_stop_1513_, lean_object* v_b_1514_){
_start:
{
lean_object* v___y_1516_; uint8_t v___x_1520_; 
v___x_1520_ = lean_usize_dec_eq(v_i_1512_, v_stop_1513_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; lean_object* v_fvarId_1522_; uint8_t v___x_1523_; 
v___x_1521_ = lean_array_uget_borrowed(v_as_1511_, v_i_1512_);
v_fvarId_1522_ = lean_ctor_get(v___x_1521_, 0);
v___x_1523_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1510_, v_fvarId_1522_);
if (v___x_1523_ == 0)
{
v___y_1516_ = v_b_1514_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1524_; 
lean_inc(v___x_1521_);
v___x_1524_ = lean_array_push(v_b_1514_, v___x_1521_);
v___y_1516_ = v___x_1524_;
goto v___jp_1515_;
}
}
else
{
return v_b_1514_;
}
v___jp_1515_:
{
size_t v___x_1517_; size_t v___x_1518_; 
v___x_1517_ = ((size_t)1ULL);
v___x_1518_ = lean_usize_add(v_i_1512_, v___x_1517_);
v_i_1512_ = v___x_1518_;
v_b_1514_ = v___y_1516_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__8___boxed(lean_object* v_a_1525_, lean_object* v_as_1526_, lean_object* v_i_1527_, lean_object* v_stop_1528_, lean_object* v_b_1529_){
_start:
{
size_t v_i_boxed_1530_; size_t v_stop_boxed_1531_; lean_object* v_res_1532_; 
v_i_boxed_1530_ = lean_unbox_usize(v_i_1527_);
lean_dec(v_i_1527_);
v_stop_boxed_1531_ = lean_unbox_usize(v_stop_1528_);
lean_dec(v_stop_1528_);
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__8(v_a_1525_, v_as_1526_, v_i_boxed_1530_, v_stop_boxed_1531_, v_b_1529_);
lean_dec_ref(v_as_1526_);
lean_dec_ref(v_a_1525_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* v_a_1533_, lean_object* v_as_1534_, size_t v_i_1535_, size_t v_stop_1536_, lean_object* v_b_1537_){
_start:
{
lean_object* v___y_1539_; uint8_t v___x_1543_; 
v___x_1543_ = lean_usize_dec_eq(v_i_1535_, v_stop_1536_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v_fvarId_1545_; uint8_t v___x_1546_; 
v___x_1544_ = lean_array_uget_borrowed(v_as_1534_, v_i_1535_);
v_fvarId_1545_ = lean_ctor_get(v___x_1544_, 0);
v___x_1546_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1533_, v_fvarId_1545_);
if (v___x_1546_ == 0)
{
v___y_1539_ = v_b_1537_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1547_; 
lean_inc(v___x_1544_);
v___x_1547_ = lean_array_push(v_b_1537_, v___x_1544_);
v___y_1539_ = v___x_1547_;
goto v___jp_1538_;
}
}
else
{
return v_b_1537_;
}
v___jp_1538_:
{
size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = ((size_t)1ULL);
v___x_1541_ = lean_usize_add(v_i_1535_, v___x_1540_);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__8(v_a_1533_, v_as_1534_, v___x_1541_, v_stop_1536_, v___y_1539_);
return v___x_1542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* v_a_1548_, lean_object* v_as_1549_, lean_object* v_i_1550_, lean_object* v_stop_1551_, lean_object* v_b_1552_){
_start:
{
size_t v_i_boxed_1553_; size_t v_stop_boxed_1554_; lean_object* v_res_1555_; 
v_i_boxed_1553_ = lean_unbox_usize(v_i_1550_);
lean_dec(v_i_1550_);
v_stop_boxed_1554_ = lean_unbox_usize(v_stop_1551_);
lean_dec(v_stop_1551_);
v_res_1555_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1548_, v_as_1549_, v_i_boxed_1553_, v_stop_boxed_1554_, v_b_1552_);
lean_dec_ref(v_as_1549_);
lean_dec_ref(v_a_1548_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object* v_b_1556_, lean_object* v_acc_1557_, lean_object* v_i_1558_){
_start:
{
lean_object* v_keyArray_1563_; lean_object* v_valueArray_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v_keyArray_1563_ = lean_ctor_get(v_b_1556_, 1);
v_valueArray_1564_ = lean_ctor_get(v_b_1556_, 2);
v___x_1565_ = lean_array_get_size(v_keyArray_1563_);
v___x_1566_ = lean_nat_dec_lt(v_i_1558_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_dec(v_i_1558_);
lean_inc(v_acc_1557_);
return v_acc_1557_;
}
else
{
lean_object* v___x_1567_; uint8_t v_isSome_1568_; 
v___x_1567_ = lean_array_fget_borrowed(v_keyArray_1563_, v_i_1558_);
v_isSome_1568_ = lean_noption_is_some(v___x_1567_);
if (v_isSome_1568_ == 0)
{
goto v___jp_1559_;
}
else
{
lean_object* v___x_1569_; uint8_t v_isSome_1570_; 
v___x_1569_ = lean_array_fget_borrowed(v_valueArray_1564_, v_i_1558_);
v_isSome_1570_ = lean_noption_is_some(v___x_1569_);
if (v_isSome_1570_ == 0)
{
goto v___jp_1559_;
}
else
{
lean_object* v_val_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_inc(v___x_1567_);
v_val_1571_ = lean_noption_get(v___x_1567_);
v___x_1572_ = lean_unsigned_to_nat(1u);
v___x_1573_ = lean_nat_add(v_i_1558_, v___x_1572_);
lean_dec(v_i_1558_);
v___x_1574_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(v_b_1556_, v_acc_1557_, v___x_1573_);
v___x_1575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1575_, 0, v_val_1571_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
return v___x_1575_;
}
}
}
v___jp_1559_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_nat_add(v_i_1558_, v___x_1560_);
lean_dec(v_i_1558_);
v_i_1558_ = v___x_1561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___boxed(lean_object* v_b_1576_, lean_object* v_acc_1577_, lean_object* v_i_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(v_b_1576_, v_acc_1577_, v_i_1578_);
lean_dec(v_acc_1577_);
lean_dec_ref(v_b_1576_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object* v_as_1580_, size_t v_sz_1581_, size_t v_i_1582_, lean_object* v_b_1583_){
_start:
{
lean_object* v_a_1586_; uint8_t v___x_1590_; 
v___x_1590_ = lean_usize_dec_lt(v_i_1582_, v_sz_1581_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; 
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_b_1583_);
return v___x_1591_;
}
else
{
lean_object* v_snd_1592_; lean_object* v_fst_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1628_; 
v_snd_1592_ = lean_ctor_get(v_b_1583_, 1);
v_fst_1593_ = lean_ctor_get(v_b_1583_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_b_1583_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1595_ = v_b_1583_;
v_isShared_1596_ = v_isSharedCheck_1628_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_snd_1592_);
lean_inc(v_fst_1593_);
lean_dec(v_b_1583_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1628_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_array_1597_; lean_object* v_start_1598_; lean_object* v_stop_1599_; uint8_t v___x_1600_; 
v_array_1597_ = lean_ctor_get(v_snd_1592_, 0);
v_start_1598_ = lean_ctor_get(v_snd_1592_, 1);
v_stop_1599_ = lean_ctor_get(v_snd_1592_, 2);
v___x_1600_ = lean_nat_dec_lt(v_start_1598_, v_stop_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1602_; 
if (v_isShared_1596_ == 0)
{
v___x_1602_ = v___x_1595_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_fst_1593_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_snd_1592_);
v___x_1602_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
else
{
lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1624_; 
lean_inc(v_stop_1599_);
lean_inc(v_start_1598_);
lean_inc_ref(v_array_1597_);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_snd_1592_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; lean_object* v_unused_1626_; lean_object* v_unused_1627_; 
v_unused_1625_ = lean_ctor_get(v_snd_1592_, 2);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_snd_1592_, 1);
lean_dec(v_unused_1626_);
v_unused_1627_ = lean_ctor_get(v_snd_1592_, 0);
lean_dec(v_unused_1627_);
v___x_1606_ = v_snd_1592_;
v_isShared_1607_ = v_isSharedCheck_1624_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v_snd_1592_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1624_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_a_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v_a_1608_ = lean_array_uget_borrowed(v_as_1580_, v_i_1582_);
v___x_1609_ = lean_array_fget(v_array_1597_, v_start_1598_);
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_nat_add(v_start_1598_, v___x_1610_);
lean_dec(v_start_1598_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 1, v___x_1611_);
v___x_1613_ = v___x_1606_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_array_1597_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_stop_1599_);
v___x_1613_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_unbox(v_a_1608_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1616_; 
lean_dec(v___x_1609_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 1, v___x_1613_);
v___x_1616_ = v___x_1595_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_fst_1593_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v___x_1613_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
v_a_1586_ = v___x_1616_;
goto v___jp_1585_;
}
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1618_ = l_Lean_Compiler_LCNF_Param_toArg___redArg(v___x_1609_);
lean_dec(v___x_1609_);
v___x_1619_ = lean_array_push(v_fst_1593_, v___x_1618_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 1, v___x_1613_);
lean_ctor_set(v___x_1595_, 0, v___x_1619_);
v___x_1621_ = v___x_1595_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1613_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
v_a_1586_ = v___x_1621_;
goto v___jp_1585_;
}
}
}
}
}
}
}
v___jp_1585_:
{
size_t v___x_1587_; size_t v___x_1588_; 
v___x_1587_ = ((size_t)1ULL);
v___x_1588_ = lean_usize_add(v_i_1582_, v___x_1587_);
v_i_1582_ = v___x_1588_;
v_b_1583_ = v_a_1586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object* v_as_1629_, lean_object* v_sz_1630_, lean_object* v_i_1631_, lean_object* v_b_1632_, lean_object* v___y_1633_){
_start:
{
size_t v_sz_boxed_1634_; size_t v_i_boxed_1635_; lean_object* v_res_1636_; 
v_sz_boxed_1634_ = lean_unbox_usize(v_sz_1630_);
lean_dec(v_sz_1630_);
v_i_boxed_1635_ = lean_unbox_usize(v_i_1631_);
lean_dec(v_i_1631_);
v_res_1636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_1629_, v_sz_boxed_1634_, v_i_boxed_1635_, v_b_1632_);
lean_dec_ref(v_as_1629_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
if (lean_obj_tag(v_a_1637_) == 0)
{
lean_object* v___x_1639_; 
v___x_1639_ = l_List_reverse___redArg(v_a_1638_);
return v___x_1639_;
}
else
{
lean_object* v_head_1640_; lean_object* v_tail_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1650_; 
v_head_1640_ = lean_ctor_get(v_a_1637_, 0);
v_tail_1641_ = lean_ctor_get(v_a_1637_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_a_1637_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1643_ = v_a_1637_;
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_tail_1641_);
lean_inc(v_head_1640_);
lean_dec(v_a_1637_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = l_Lean_mkFVar(v_head_1640_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 1, v_a_1638_);
lean_ctor_set(v___x_1643_, 0, v___x_1645_);
v___x_1647_ = v___x_1643_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_a_1638_);
v___x_1647_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
v_a_1637_ = v_tail_1641_;
v_a_1638_ = v___x_1647_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t v_sz_1651_, size_t v_i_1652_, lean_object* v_bs_1653_, uint8_t v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_usize_dec_lt(v_i_1652_, v_sz_1651_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_bs_1653_);
return v___x_1662_;
}
else
{
uint8_t v___x_1663_; lean_object* v_v_1664_; lean_object* v___x_1665_; 
v___x_1663_ = 0;
v_v_1664_ = lean_array_uget_borrowed(v_bs_1653_, v_i_1652_);
lean_inc(v_v_1664_);
v___x_1665_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_1663_, v_v_1664_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; lean_object* v_bs_x27_1668_; size_t v___x_1669_; size_t v___x_1670_; lean_object* v___x_1671_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = lean_unsigned_to_nat(0u);
v_bs_x27_1668_ = lean_array_uset(v_bs_1653_, v_i_1652_, v___x_1667_);
v___x_1669_ = ((size_t)1ULL);
v___x_1670_ = lean_usize_add(v_i_1652_, v___x_1669_);
v___x_1671_ = lean_array_uset(v_bs_x27_1668_, v_i_1652_, v_a_1666_);
v_i_1652_ = v___x_1670_;
v_bs_1653_ = v___x_1671_;
goto _start;
}
else
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1680_; 
lean_dec_ref(v_bs_1653_);
v_a_1673_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1675_ = v___x_1665_;
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1665_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1680_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1676_ == 0)
{
v___x_1678_ = v___x_1675_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1673_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* v_sz_1681_, lean_object* v_i_1682_, lean_object* v_bs_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
size_t v_sz_boxed_1691_; size_t v_i_boxed_1692_; uint8_t v___y_12358__boxed_1693_; lean_object* v_res_1694_; 
v_sz_boxed_1691_ = lean_unbox_usize(v_sz_1681_);
lean_dec(v_sz_1681_);
v_i_boxed_1692_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v___y_12358__boxed_1693_ = lean_unbox(v___y_1684_);
v_res_1694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_boxed_1691_, v_i_boxed_1692_, v_bs_1683_, v___y_12358__boxed_1693_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object* v_a_1695_, lean_object* v_as_1696_, size_t v_i_1697_, size_t v_stop_1698_, lean_object* v_b_1699_){
_start:
{
lean_object* v___y_1701_; uint8_t v___x_1705_; 
v___x_1705_ = lean_usize_dec_eq(v_i_1697_, v_stop_1698_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v_fvarId_1707_; uint8_t v___x_1708_; 
v___x_1706_ = lean_array_uget_borrowed(v_as_1696_, v_i_1697_);
v_fvarId_1707_ = lean_ctor_get(v___x_1706_, 0);
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1695_, v_fvarId_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
lean_inc(v___x_1706_);
v___x_1709_ = lean_array_push(v_b_1699_, v___x_1706_);
v___y_1701_ = v___x_1709_;
goto v___jp_1700_;
}
else
{
v___y_1701_ = v_b_1699_;
goto v___jp_1700_;
}
}
else
{
return v_b_1699_;
}
v___jp_1700_:
{
size_t v___x_1702_; size_t v___x_1703_; 
v___x_1702_ = ((size_t)1ULL);
v___x_1703_ = lean_usize_add(v_i_1697_, v___x_1702_);
v_i_1697_ = v___x_1703_;
v_b_1699_ = v___y_1701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object* v_a_1710_, lean_object* v_as_1711_, lean_object* v_i_1712_, lean_object* v_stop_1713_, lean_object* v_b_1714_){
_start:
{
size_t v_i_boxed_1715_; size_t v_stop_boxed_1716_; lean_object* v_res_1717_; 
v_i_boxed_1715_ = lean_unbox_usize(v_i_1712_);
lean_dec(v_i_1712_);
v_stop_boxed_1716_ = lean_unbox_usize(v_stop_1713_);
lean_dec(v_stop_1713_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1710_, v_as_1711_, v_i_boxed_1715_, v_stop_boxed_1716_, v_b_1714_);
lean_dec_ref(v_as_1711_);
lean_dec_ref(v_a_1710_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__2(lean_object* v_a_1718_, size_t v_sz_1719_, size_t v_i_1720_, lean_object* v_bs_1721_){
_start:
{
uint8_t v___x_1722_; 
v___x_1722_ = lean_usize_dec_lt(v_i_1720_, v_sz_1719_);
if (v___x_1722_ == 0)
{
return v_bs_1721_;
}
else
{
lean_object* v_v_1723_; lean_object* v_fvarId_1724_; lean_object* v___x_1725_; lean_object* v_bs_x27_1726_; uint8_t v___x_1727_; size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_v_1723_ = lean_array_uget_borrowed(v_bs_1721_, v_i_1720_);
v_fvarId_1724_ = lean_ctor_get(v_v_1723_, 0);
lean_inc(v_fvarId_1724_);
v___x_1725_ = lean_unsigned_to_nat(0u);
v_bs_x27_1726_ = lean_array_uset(v_bs_1721_, v_i_1720_, v___x_1725_);
v___x_1727_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1718_, v_fvarId_1724_);
lean_dec(v_fvarId_1724_);
v___x_1728_ = ((size_t)1ULL);
v___x_1729_ = lean_usize_add(v_i_1720_, v___x_1728_);
v___x_1730_ = lean_box(v___x_1727_);
v___x_1731_ = lean_array_uset(v_bs_x27_1726_, v_i_1720_, v___x_1730_);
v_i_1720_ = v___x_1729_;
v_bs_1721_ = v___x_1731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__2___boxed(lean_object* v_a_1733_, lean_object* v_sz_1734_, lean_object* v_i_1735_, lean_object* v_bs_1736_){
_start:
{
size_t v_sz_boxed_1737_; size_t v_i_boxed_1738_; lean_object* v_res_1739_; 
v_sz_boxed_1737_ = lean_unbox_usize(v_sz_1734_);
lean_dec(v_sz_1734_);
v_i_boxed_1738_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__2(v_a_1733_, v_sz_boxed_1737_, v_i_boxed_1738_, v_bs_1736_);
lean_dec_ref(v_a_1733_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* v_a_1740_, size_t v_sz_1741_, size_t v_i_1742_, lean_object* v_bs_1743_){
_start:
{
uint8_t v___x_1744_; 
v___x_1744_ = lean_usize_dec_lt(v_i_1742_, v_sz_1741_);
if (v___x_1744_ == 0)
{
return v_bs_1743_;
}
else
{
lean_object* v_v_1745_; lean_object* v_fvarId_1746_; lean_object* v___x_1747_; lean_object* v_bs_x27_1748_; uint8_t v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_v_1745_ = lean_array_uget_borrowed(v_bs_1743_, v_i_1742_);
v_fvarId_1746_ = lean_ctor_get(v_v_1745_, 0);
lean_inc(v_fvarId_1746_);
v___x_1747_ = lean_unsigned_to_nat(0u);
v_bs_x27_1748_ = lean_array_uset(v_bs_1743_, v_i_1742_, v___x_1747_);
v___x_1749_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1740_, v_fvarId_1746_);
lean_dec(v_fvarId_1746_);
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_i_1742_, v___x_1750_);
v___x_1752_ = lean_box(v___x_1749_);
v___x_1753_ = lean_array_uset(v_bs_x27_1748_, v_i_1742_, v___x_1752_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__2(v_a_1740_, v_sz_1741_, v___x_1751_, v___x_1753_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object* v_a_1755_, lean_object* v_sz_1756_, lean_object* v_i_1757_, lean_object* v_bs_1758_){
_start:
{
size_t v_sz_boxed_1759_; size_t v_i_boxed_1760_; lean_object* v_res_1761_; 
v_sz_boxed_1759_ = lean_unbox_usize(v_sz_1756_);
lean_dec(v_sz_1756_);
v_i_boxed_1760_ = lean_unbox_usize(v_i_1757_);
lean_dec(v_i_1757_);
v_res_1761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1755_, v_sz_boxed_1759_, v_i_boxed_1760_, v_bs_1758_);
lean_dec_ref(v_a_1755_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
if (lean_obj_tag(v_a_1762_) == 0)
{
lean_object* v___x_1764_; 
v___x_1764_ = l_List_reverse___redArg(v_a_1763_);
return v___x_1764_;
}
else
{
lean_object* v_head_1765_; lean_object* v_tail_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1775_; 
v_head_1765_ = lean_ctor_get(v_a_1762_, 0);
v_tail_1766_ = lean_ctor_get(v_a_1762_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_a_1762_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1768_ = v_a_1762_;
v_isShared_1769_ = v_isSharedCheck_1775_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_tail_1766_);
lean_inc(v_head_1765_);
lean_dec(v_a_1762_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1775_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1770_ = l_Lean_MessageData_ofExpr(v_head_1765_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v_a_1763_);
lean_ctor_set(v___x_1768_, 0, v___x_1770_);
v___x_1772_ = v___x_1768_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_a_1763_);
v___x_1772_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
v_a_1762_ = v_tail_1766_;
v_a_1763_ = v___x_1772_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0(void){
_start:
{
lean_object* v_cellCount_1776_; lean_object* v___x_1777_; 
v_cellCount_1776_ = lean_unsigned_to_nat(16u);
v___x_1777_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1(void){
_start:
{
lean_object* v_cellCount_1778_; lean_object* v___x_1779_; 
v_cellCount_1778_ = lean_unsigned_to_nat(16u);
v___x_1779_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1778_);
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11));
v___x_1801_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13));
v___x_1802_ = l_Lean_Name_append(v___x_1801_, v___x_1800_);
return v___x_1802_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15));
v___x_1805_ = l_Lean_stringToMessageData(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* v_decl_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_value_1812_; 
v_value_1812_ = lean_ctor_get(v_decl_1806_, 1);
lean_inc_ref(v_value_1812_);
if (lean_obj_tag(v_value_1812_) == 0)
{
lean_object* v_toSignature_1813_; uint8_t v_recursive_1814_; lean_object* v_inlineAttr_x3f_1815_; lean_object* v_code_1816_; lean_object* v___x_1817_; 
v_toSignature_1813_ = lean_ctor_get(v_decl_1806_, 0);
lean_inc_ref(v_toSignature_1813_);
v_recursive_1814_ = lean_ctor_get_uint8(v_decl_1806_, sizeof(void*)*3);
v_inlineAttr_x3f_1815_ = lean_ctor_get(v_decl_1806_, 2);
v_code_1816_ = lean_ctor_get(v_value_1812_, 0);
lean_inc_ref(v_code_1816_);
lean_inc_ref(v_decl_1806_);
v___x_1817_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_2057_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_2057_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_2057_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_size_1822_; lean_object* v_name_1823_; lean_object* v_levelParams_1824_; lean_object* v_type_1825_; lean_object* v_params_1826_; uint8_t v_safe_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_2056_; 
v_size_1822_ = lean_ctor_get(v_a_1818_, 0);
v_name_1823_ = lean_ctor_get(v_toSignature_1813_, 0);
v_levelParams_1824_ = lean_ctor_get(v_toSignature_1813_, 1);
v_type_1825_ = lean_ctor_get(v_toSignature_1813_, 2);
v_params_1826_ = lean_ctor_get(v_toSignature_1813_, 3);
v_safe_1827_ = lean_ctor_get_uint8(v_toSignature_1813_, sizeof(void*)*4);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_toSignature_1813_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_1829_ = v_toSignature_1813_;
v_isShared_1830_ = v_isSharedCheck_2056_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_params_1826_);
lean_inc(v_type_1825_);
lean_inc(v_levelParams_1824_);
lean_inc(v_name_1823_);
lean_dec(v_toSignature_1813_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_2056_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; size_t v___y_1835_; lean_object* v___y_1836_; uint8_t v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; size_t v___y_1840_; uint8_t v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___x_1978_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; size_t v___y_1984_; uint8_t v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; size_t v___y_1989_; lean_object* v___y_1990_; uint8_t v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; uint8_t v___y_2021_; uint8_t v___x_2053_; 
v___x_1978_ = lean_array_get_size(v_params_1826_);
v___x_2053_ = lean_nat_dec_eq(v_size_1822_, v___x_1978_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = lean_nat_dec_eq(v_size_1822_, v___x_2054_);
v___y_2021_ = v___x_2055_;
goto v___jp_2020_;
}
else
{
v___y_2021_ = v___x_2053_;
goto v___jp_2020_;
}
v___jp_1831_:
{
lean_object* v___x_1847_; 
lean_inc_ref(v___y_1836_);
v___x_1847_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v___y_1836_, v_value_1812_, v___y_1842_, v___y_1832_, v___y_1844_, v___y_1843_, v___y_1838_);
lean_dec_ref(v___y_1842_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v___x_1849_ = l_Lean_Compiler_LCNF_Code_inferType(v___y_1837_, v_code_1816_, v___y_1832_, v___y_1844_, v___y_1843_, v___y_1838_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
lean_inc_ref(v___y_1839_);
v___x_1851_ = l_Lean_Compiler_LCNF_mkForallParams(v___y_1837_, v___y_1839_, v_a_1850_, v___y_1832_, v___y_1844_, v___y_1843_, v___y_1838_);
lean_dec(v_a_1850_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref_known(v___x_1851_, 1);
v___x_1853_ = lean_box(0);
lean_inc(v___y_1833_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 3, v___y_1839_);
lean_ctor_set(v___x_1829_, 2, v_a_1852_);
lean_ctor_set(v___x_1829_, 1, v___x_1853_);
lean_ctor_set(v___x_1829_, 0, v___y_1833_);
v___x_1855_ = v___x_1829_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___y_1833_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v_a_1852_);
lean_ctor_set(v_reuseFailAlloc_1953_, 3, v___y_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1953_, sizeof(void*)*4, v_safe_1827_);
v___x_1855_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v_a_1848_);
lean_ctor_set(v___x_1856_, 2, v_inlineAttr_x3f_1815_);
lean_ctor_set_uint8(v___x_1856_, sizeof(void*)*3, v_recursive_1814_);
lean_inc_ref(v___x_1856_);
v___x_1857_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1856_, v___y_1838_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_dec_ref_known(v___x_1857_, 1);
v___x_1858_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0);
v___x_1859_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1);
lean_inc(v___y_1845_);
v___x_1860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1860_, 0, v___y_1845_);
lean_ctor_set(v___x_1860_, 1, v___x_1858_);
lean_ctor_set(v___x_1860_, 2, v___x_1859_);
v___x_1861_ = lean_st_mk_ref(v___x_1860_);
v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v___y_1840_, v___y_1835_, v_params_1826_, v___y_1841_, v___x_1861_, v___y_1832_, v___y_1844_, v___y_1843_, v___y_1838_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; size_t v_sz_1868_; lean_object* v___x_1869_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc_n(v_a_1863_, 2);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1864_ = lean_mk_empty_array_with_capacity(v___y_1845_);
v___x_1865_ = lean_array_get_size(v_a_1863_);
v___x_1866_ = l_Array_toSubarray___redArg(v_a_1863_, v___y_1845_, v___x_1865_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1864_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v_sz_1868_ = lean_array_size(v___y_1834_);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v___y_1834_, v_sz_1868_, v___y_1835_, v___x_1867_);
lean_dec_ref(v___y_1834_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v_fst_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1927_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v_fst_1871_ = lean_ctor_get(v_a_1870_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_a_1870_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v_a_1870_, 1);
lean_dec(v_unused_1928_);
v___x_1873_ = v_a_1870_;
v_isShared_1874_ = v_isSharedCheck_1927_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_fst_1871_);
lean_dec(v_a_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1927_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1875_, 0, v___y_1833_);
lean_ctor_set(v___x_1875_, 1, v___x_1853_);
lean_ctor_set(v___x_1875_, 2, v_fst_1871_);
v___x_1876_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3));
v___x_1877_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___y_1837_, v___x_1875_, v___x_1876_, v___y_1832_, v___y_1844_, v___y_1843_, v___y_1838_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v_fvarId_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v_fvarId_1879_ = lean_ctor_get(v_a_1878_, 0);
lean_inc(v_fvarId_1879_);
v___x_1880_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1880_, 0, v_fvarId_1879_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 1, v___x_1880_);
lean_ctor_set(v___x_1873_, 0, v_a_1878_);
v___x_1882_ = v___x_1873_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1878_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1884_, 0, v_name_1823_);
lean_ctor_set(v___x_1884_, 1, v_levelParams_1824_);
lean_ctor_set(v___x_1884_, 2, v_type_1825_);
lean_ctor_set(v___x_1884_, 3, v_a_1863_);
lean_ctor_set_uint8(v___x_1884_, sizeof(void*)*4, v_safe_1827_);
v___x_1885_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4));
v___x_1886_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1883_);
lean_ctor_set(v___x_1886_, 2, v___x_1885_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*3, v___y_1841_);
lean_inc_ref(v___x_1886_);
v___x_1887_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1886_, v___y_1838_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref_known(v___x_1887_, 1);
v___x_1888_ = lean_st_ref_get(v___x_1861_);
lean_dec(v___x_1861_);
lean_dec(v___x_1888_);
v___x_1889_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___y_1837_, v___y_1846_, v___y_1844_);
lean_dec_ref(v___y_1846_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1900_; 
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v___x_1889_, 0);
lean_dec(v_unused_1901_);
v___x_1891_ = v___x_1889_;
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v___x_1889_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1900_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1893_ = lean_unsigned_to_nat(2u);
v___x_1894_ = lean_mk_empty_array_with_capacity(v___x_1893_);
v___x_1895_ = lean_array_push(v___x_1894_, v___x_1856_);
v___x_1896_ = lean_array_push(v___x_1895_, v___x_1886_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1896_);
v___x_1898_ = v___x_1891_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec_ref_known(v___x_1886_, 3);
lean_dec_ref_known(v___x_1856_, 3);
v_a_1902_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1889_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1889_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec_ref_known(v___x_1886_, 3);
lean_dec(v___x_1861_);
lean_dec_ref_known(v___x_1856_, 3);
lean_dec_ref(v___y_1846_);
v_a_1910_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1887_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1887_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_del_object(v___x_1873_);
lean_dec(v_a_1863_);
lean_dec(v___x_1861_);
lean_dec_ref_known(v___x_1856_, 3);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v_type_1825_);
lean_dec(v_levelParams_1824_);
lean_dec(v_name_1823_);
v_a_1919_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1877_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1877_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_a_1863_);
lean_dec(v___x_1861_);
lean_dec_ref_known(v___x_1856_, 3);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1833_);
lean_dec_ref(v_type_1825_);
lean_dec(v_levelParams_1824_);
lean_dec(v_name_1823_);
v_a_1929_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1869_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1869_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec(v___x_1861_);
lean_dec_ref_known(v___x_1856_, 3);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v_type_1825_);
lean_dec(v_levelParams_1824_);
lean_dec(v_name_1823_);
v_a_1937_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1862_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1862_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref_known(v___x_1856_, 3);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v_params_1826_);
lean_dec_ref(v_type_1825_);
lean_dec(v_levelParams_1824_);
lean_dec(v_name_1823_);
v_a_1945_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1857_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1857_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_a_1848_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_del_object(v___x_1829_);
lean_dec_ref(v_params_1826_);
lean_dec_ref(v_type_1825_);
lean_dec(v_levelParams_1824_);
lean_dec(v_name_1823_);
lean_dec(v_inlineAttr_x3f_1815_);
v_a_1954_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1851_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1851_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_a_1848_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_del_object(v___x_1829_);
lean_dec_ref(v_params_1826_);
lean_dec_ref(v_type_1825_);
lean_dec(v_levelParams_1824_);
lean_dec(v_name_1823_);
lean_dec(v_inlineAttr_x3f_1815_);
v_a_1962_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1849_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1849_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_del_object(v___x_1829_);
lean_dec_ref(v_params_1826_);
lean_dec_ref(v_type_1825_);
lean_dec(v_levelParams_1824_);
lean_dec(v_name_1823_);
lean_dec_ref(v_code_1816_);
lean_dec(v_inlineAttr_x3f_1815_);
v_a_1970_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1847_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1847_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
v___jp_1979_:
{
uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1991_ = 0;
v___x_1992_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5));
lean_inc_ref(v___y_1988_);
lean_inc(v___y_1983_);
lean_inc(v_name_1823_);
v___x_1993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1993_, 0, v_name_1823_);
lean_ctor_set(v___x_1993_, 1, v___y_1983_);
lean_ctor_set(v___x_1993_, 2, v___y_1988_);
v___x_1994_ = lean_mk_empty_array_with_capacity(v___y_1982_);
v___x_1995_ = lean_nat_dec_lt(v___y_1982_, v___x_1978_);
if (v___x_1995_ == 0)
{
lean_dec(v_a_1818_);
v___y_1832_ = v___y_1980_;
v___y_1833_ = v___y_1983_;
v___y_1834_ = v___y_1988_;
v___y_1835_ = v___y_1989_;
v___y_1836_ = v___x_1992_;
v___y_1837_ = v___x_1991_;
v___y_1838_ = v___y_1981_;
v___y_1839_ = v___y_1990_;
v___y_1840_ = v___y_1984_;
v___y_1841_ = v___y_1985_;
v___y_1842_ = v___x_1993_;
v___y_1843_ = v___y_1986_;
v___y_1844_ = v___y_1987_;
v___y_1845_ = v___y_1982_;
v___y_1846_ = v___x_1994_;
goto v___jp_1831_;
}
else
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_nat_dec_le(v___x_1978_, v___x_1978_);
if (v___x_1996_ == 0)
{
if (v___x_1995_ == 0)
{
lean_dec(v_a_1818_);
v___y_1832_ = v___y_1980_;
v___y_1833_ = v___y_1983_;
v___y_1834_ = v___y_1988_;
v___y_1835_ = v___y_1989_;
v___y_1836_ = v___x_1992_;
v___y_1837_ = v___x_1991_;
v___y_1838_ = v___y_1981_;
v___y_1839_ = v___y_1990_;
v___y_1840_ = v___y_1984_;
v___y_1841_ = v___y_1985_;
v___y_1842_ = v___x_1993_;
v___y_1843_ = v___y_1986_;
v___y_1844_ = v___y_1987_;
v___y_1845_ = v___y_1982_;
v___y_1846_ = v___x_1994_;
goto v___jp_1831_;
}
else
{
size_t v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_usize_of_nat(v___x_1978_);
v___x_1998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1818_, v_params_1826_, v___y_1989_, v___x_1997_, v___x_1994_);
lean_dec(v_a_1818_);
v___y_1832_ = v___y_1980_;
v___y_1833_ = v___y_1983_;
v___y_1834_ = v___y_1988_;
v___y_1835_ = v___y_1989_;
v___y_1836_ = v___x_1992_;
v___y_1837_ = v___x_1991_;
v___y_1838_ = v___y_1981_;
v___y_1839_ = v___y_1990_;
v___y_1840_ = v___y_1984_;
v___y_1841_ = v___y_1985_;
v___y_1842_ = v___x_1993_;
v___y_1843_ = v___y_1986_;
v___y_1844_ = v___y_1987_;
v___y_1845_ = v___y_1982_;
v___y_1846_ = v___x_1998_;
goto v___jp_1831_;
}
}
else
{
size_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_usize_of_nat(v___x_1978_);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1818_, v_params_1826_, v___y_1989_, v___x_1999_, v___x_1994_);
lean_dec(v_a_1818_);
v___y_1832_ = v___y_1980_;
v___y_1833_ = v___y_1983_;
v___y_1834_ = v___y_1988_;
v___y_1835_ = v___y_1989_;
v___y_1836_ = v___x_1992_;
v___y_1837_ = v___x_1991_;
v___y_1838_ = v___y_1981_;
v___y_1839_ = v___y_1990_;
v___y_1840_ = v___y_1984_;
v___y_1841_ = v___y_1985_;
v___y_1842_ = v___x_1993_;
v___y_1843_ = v___y_1986_;
v___y_1844_ = v___y_1987_;
v___y_1845_ = v___y_1982_;
v___y_1846_ = v___x_2000_;
goto v___jp_1831_;
}
}
}
v___jp_2001_:
{
size_t v_sz_2007_; size_t v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_sz_2007_ = lean_array_size(v_params_1826_);
v___x_2008_ = ((size_t)0ULL);
lean_inc_ref(v_params_1826_);
v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1818_, v_sz_2007_, v___x_2008_, v_params_1826_);
v___x_2010_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7));
lean_inc(v_name_1823_);
v___x_2011_ = l_Lean_Name_append(v_name_1823_, v___x_2010_);
v___x_2012_ = lean_unsigned_to_nat(0u);
v___x_2013_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8));
v___x_2014_ = lean_nat_dec_lt(v___x_2012_, v___x_1978_);
if (v___x_2014_ == 0)
{
v___y_1980_ = v___y_2003_;
v___y_1981_ = v___y_2006_;
v___y_1982_ = v___x_2012_;
v___y_1983_ = v___x_2011_;
v___y_1984_ = v_sz_2007_;
v___y_1985_ = v___y_2002_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2004_;
v___y_1988_ = v___x_2009_;
v___y_1989_ = v___x_2008_;
v___y_1990_ = v___x_2013_;
goto v___jp_1979_;
}
else
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_nat_dec_le(v___x_1978_, v___x_1978_);
if (v___x_2015_ == 0)
{
if (v___x_2014_ == 0)
{
v___y_1980_ = v___y_2003_;
v___y_1981_ = v___y_2006_;
v___y_1982_ = v___x_2012_;
v___y_1983_ = v___x_2011_;
v___y_1984_ = v_sz_2007_;
v___y_1985_ = v___y_2002_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2004_;
v___y_1988_ = v___x_2009_;
v___y_1989_ = v___x_2008_;
v___y_1990_ = v___x_2013_;
goto v___jp_1979_;
}
else
{
size_t v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = lean_usize_of_nat(v___x_1978_);
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1818_, v_params_1826_, v___x_2008_, v___x_2016_, v___x_2013_);
v___y_1980_ = v___y_2003_;
v___y_1981_ = v___y_2006_;
v___y_1982_ = v___x_2012_;
v___y_1983_ = v___x_2011_;
v___y_1984_ = v_sz_2007_;
v___y_1985_ = v___y_2002_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2004_;
v___y_1988_ = v___x_2009_;
v___y_1989_ = v___x_2008_;
v___y_1990_ = v___x_2017_;
goto v___jp_1979_;
}
}
else
{
size_t v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_usize_of_nat(v___x_1978_);
v___x_2019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1818_, v_params_1826_, v___x_2008_, v___x_2018_, v___x_2013_);
v___y_1980_ = v___y_2003_;
v___y_1981_ = v___y_2006_;
v___y_1982_ = v___x_2012_;
v___y_1983_ = v___x_2011_;
v___y_1984_ = v_sz_2007_;
v___y_1985_ = v___y_2002_;
v___y_1986_ = v___y_2005_;
v___y_1987_ = v___y_2004_;
v___y_1988_ = v___x_2009_;
v___y_1989_ = v___x_2008_;
v___y_1990_ = v___x_2019_;
goto v___jp_1979_;
}
}
}
v___jp_2020_:
{
if (v___y_2021_ == 0)
{
lean_object* v_options_2022_; uint8_t v_hasTrace_2023_; 
lean_inc(v_inlineAttr_x3f_1815_);
lean_del_object(v___x_1820_);
lean_dec_ref(v_decl_1806_);
v_options_2022_ = lean_ctor_get(v_a_1809_, 2);
v_hasTrace_2023_ = lean_ctor_get_uint8(v_options_2022_, sizeof(void*)*1);
if (v_hasTrace_2023_ == 0)
{
v___y_2002_ = v___y_2021_;
v___y_2003_ = v_a_1807_;
v___y_2004_ = v_a_1808_;
v___y_2005_ = v_a_1809_;
v___y_2006_ = v_a_1810_;
goto v___jp_2001_;
}
else
{
lean_object* v_inheritedTraceOptions_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v_inheritedTraceOptions_2024_ = lean_ctor_get(v_a_1809_, 13);
v___x_2025_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11));
v___x_2026_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14);
v___x_2027_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2024_, v_options_2022_, v___x_2026_);
if (v___x_2027_ == 0)
{
v___y_2002_ = v___y_2021_;
v___y_2003_ = v_a_1807_;
v___y_2004_ = v_a_1808_;
v___y_2005_ = v_a_1809_;
v___y_2006_ = v_a_1810_;
goto v___jp_2001_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_inc(v_name_1823_);
v___x_2028_ = l_Lean_MessageData_ofName(v_name_1823_);
v___x_2029_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16);
v___x_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_box(0);
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(v_a_1818_, v___x_2031_, v___x_2032_);
v___x_2034_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(v___x_2033_, v___x_2031_);
v___x_2035_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v___x_2034_, v___x_2031_);
v___x_2036_ = l_Lean_MessageData_ofList(v___x_2035_);
v___x_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2030_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v___x_2025_, v___x_2037_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_dec_ref_known(v___x_2038_, 1);
v___y_2002_ = v___y_2021_;
v___y_2003_ = v_a_1807_;
v___y_2004_ = v_a_1808_;
v___y_2005_ = v_a_1809_;
v___y_2006_ = v_a_1810_;
goto v___jp_2001_;
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_del_object(v___x_1829_);
lean_dec_ref(v_params_1826_);
lean_dec_ref(v_type_1825_);
lean_dec(v_levelParams_1824_);
lean_dec(v_name_1823_);
lean_dec(v_a_1818_);
lean_dec_ref(v_code_1816_);
lean_dec(v_inlineAttr_x3f_1815_);
lean_dec_ref_known(v_value_1812_, 1);
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2038_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
lean_del_object(v___x_1829_);
lean_dec_ref(v_params_1826_);
lean_dec_ref(v_type_1825_);
lean_dec(v_levelParams_1824_);
lean_dec(v_name_1823_);
lean_dec(v_a_1818_);
lean_dec_ref(v_code_1816_);
lean_dec_ref_known(v_value_1812_, 1);
v___x_2047_ = lean_unsigned_to_nat(1u);
v___x_2048_ = lean_mk_empty_array_with_capacity(v___x_2047_);
v___x_2049_ = lean_array_push(v___x_2048_, v_decl_1806_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_2049_);
v___x_2051_ = v___x_1820_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v_code_1816_);
lean_dec_ref_known(v_value_1812_, 1);
lean_dec_ref(v_toSignature_1813_);
lean_dec_ref(v_decl_1806_);
v_a_2058_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_1817_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_1817_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2075_; 
v_isSharedCheck_2075_ = !lean_is_exclusive(v_value_1812_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v_value_1812_, 0);
lean_dec(v_unused_2076_);
v___x_2067_ = v_value_1812_;
v_isShared_2068_ = v_isSharedCheck_2075_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v_value_1812_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2075_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2069_ = lean_unsigned_to_nat(1u);
v___x_2070_ = lean_mk_empty_array_with_capacity(v___x_2069_);
v___x_2071_ = lean_array_push(v___x_2070_, v_decl_1806_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set_tag(v___x_2067_, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2071_);
v___x_2073_ = v___x_2067_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object* v_decl_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v_decl_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
return v_res_2083_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* v_00_u03b2_2084_, lean_object* v_m_2085_, lean_object* v_a_2086_){
_start:
{
uint8_t v___x_2087_; 
v___x_2087_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_2085_, v_a_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* v_00_u03b2_2088_, lean_object* v_m_2089_, lean_object* v_a_2090_){
_start:
{
uint8_t v_res_2091_; lean_object* v_r_2092_; 
v_res_2091_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(v_00_u03b2_2088_, v_m_2089_, v_a_2090_);
lean_dec(v_a_2090_);
lean_dec_ref(v_m_2089_);
v_r_2092_ = lean_box(v_res_2091_);
return v_r_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* v_as_2093_, size_t v_sz_2094_, size_t v_i_2095_, lean_object* v_b_2096_, uint8_t v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_2093_, v_sz_2094_, v_i_2095_, v_b_2096_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* v_as_2105_, lean_object* v_sz_2106_, lean_object* v_i_2107_, lean_object* v_b_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
size_t v_sz_boxed_2116_; size_t v_i_boxed_2117_; uint8_t v___y_13091__boxed_2118_; lean_object* v_res_2119_; 
v_sz_boxed_2116_ = lean_unbox_usize(v_sz_2106_);
lean_dec(v_sz_2106_);
v_i_boxed_2117_ = lean_unbox_usize(v_i_2107_);
lean_dec(v_i_2107_);
v___y_13091__boxed_2118_ = lean_unbox(v___y_2109_);
v_res_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_2105_, v_sz_boxed_2116_, v_i_boxed_2117_, v_b_2108_, v___y_13091__boxed_2118_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v_as_2105_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0(lean_object* v_00_u03b2_2120_, lean_object* v_m_2121_, lean_object* v_query_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0___redArg(v_m_2121_, v_query_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2124_, lean_object* v_m_2125_, lean_object* v_query_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_spec__0(v_00_u03b2_2124_, v_m_2125_, v_query_2126_);
lean_dec(v_query_2126_);
lean_dec_ref(v_m_2125_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* v_as_2128_, size_t v_i_2129_, size_t v_stop_2130_, lean_object* v_b_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_a_2138_; uint8_t v___x_2142_; 
v___x_2142_ = lean_usize_dec_eq(v_i_2129_, v_stop_2130_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_array_uget_borrowed(v_as_2128_, v_i_2129_);
lean_inc(v___x_2143_);
v___x_2144_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v___x_2143_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l_Array_append___redArg(v_b_2131_, v_a_2145_);
lean_dec(v_a_2145_);
v_a_2138_ = v___x_2146_;
goto v___jp_2137_;
}
else
{
lean_dec_ref(v_b_2131_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2147_; 
v_a_2147_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2144_, 1);
v_a_2138_ = v_a_2147_;
goto v___jp_2137_;
}
else
{
return v___x_2144_;
}
}
}
else
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_b_2131_);
return v___x_2148_;
}
v___jp_2137_:
{
size_t v___x_2139_; size_t v___x_2140_; 
v___x_2139_ = ((size_t)1ULL);
v___x_2140_ = lean_usize_add(v_i_2129_, v___x_2139_);
v_i_2129_ = v___x_2140_;
v_b_2131_ = v_a_2138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* v_as_2149_, lean_object* v_i_2150_, lean_object* v_stop_2151_, lean_object* v_b_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
size_t v_i_boxed_2158_; size_t v_stop_boxed_2159_; lean_object* v_res_2160_; 
v_i_boxed_2158_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_stop_boxed_2159_ = lean_unbox_usize(v_stop_2151_);
lean_dec(v_stop_2151_);
v_res_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_2149_, v_i_boxed_2158_, v_stop_boxed_2159_, v_b_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec_ref(v_as_2149_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* v___x_2161_, lean_object* v_decls_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2168_ = lean_mk_empty_array_with_capacity(v___x_2161_);
v___x_2169_ = lean_array_get_size(v_decls_2162_);
v___x_2170_ = lean_nat_dec_lt(v___x_2161_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2168_);
return v___x_2171_;
}
else
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_nat_dec_le(v___x_2169_, v___x_2169_);
if (v___x_2172_ == 0)
{
if (v___x_2170_ == 0)
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2168_);
return v___x_2173_;
}
else
{
size_t v___x_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((size_t)0ULL);
v___x_2175_ = lean_usize_of_nat(v___x_2169_);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2162_, v___x_2174_, v___x_2175_, v___x_2168_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
return v___x_2176_;
}
}
else
{
size_t v___x_2177_; size_t v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = ((size_t)0ULL);
v___x_2178_ = lean_usize_of_nat(v___x_2169_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2162_, v___x_2177_, v___x_2178_, v___x_2168_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
return v___x_2179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* v___x_2180_, lean_object* v_decls_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(v___x_2180_, v_decls_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec_ref(v_decls_2181_);
lean_dec(v___x_2180_);
return v_res_2187_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_unsigned_to_nat(2803462840u);
v___x_2251_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2252_ = l_Lean_Name_num___override(v___x_2251_, v___x_2250_);
return v___x_2252_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2255_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2256_ = l_Lean_Name_str___override(v___x_2255_, v___x_2254_);
return v___x_2256_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2259_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2260_ = l_Lean_Name_str___override(v___x_2259_, v___x_2258_);
return v___x_2260_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = lean_unsigned_to_nat(2u);
v___x_2262_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2263_ = l_Lean_Name_num___override(v___x_2262_, v___x_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2265_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11));
v___x_2266_ = 1;
v___x_2267_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2268_ = l_Lean_registerTraceClass(v___x_2265_, v___x_2266_, v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
return v_res_2270_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
}
#ifdef __cplusplus
}
#endif
