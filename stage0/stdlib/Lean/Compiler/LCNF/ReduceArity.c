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
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Param_toArg___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_redArg"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value),LEAN_SCALAR_PTR_LITERAL(174, 35, 1, 83, 6, 52, 87, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value;
static const lean_array_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceArity"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value),LEAN_SCALAR_PTR_LITERAL(89, 83, 236, 44, 104, 94, 232, 236)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ", used params: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_reduceArity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_reduceArity___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_reduceArity___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_reduceArity___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value),LEAN_SCALAR_PTR_LITERAL(111, 96, 179, 183, 204, 167, 118, 86)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value),LEAN_SCALAR_PTR_LITERAL(14, 5, 205, 56, 180, 134, 217, 66)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value),LEAN_SCALAR_PTR_LITERAL(88, 65, 191, 26, 52, 74, 82, 47)}};
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_tail_5_; uint8_t v___x_6_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 2);
v___x_6_ = l_Lean_instBEqFVarId_beq(v_key_4_, v_a_1_);
if (v___x_6_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
if (lean_obj_tag(v_x_13_) == 0)
{
return v_x_12_;
}
else
{
lean_object* v_key_14_; lean_object* v_value_15_; lean_object* v_tail_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_39_; 
v_key_14_ = lean_ctor_get(v_x_13_, 0);
v_value_15_ = lean_ctor_get(v_x_13_, 1);
v_tail_16_ = lean_ctor_get(v_x_13_, 2);
v_isSharedCheck_39_ = !lean_is_exclusive(v_x_13_);
if (v_isSharedCheck_39_ == 0)
{
v___x_18_ = v_x_13_;
v_isShared_19_ = v_isSharedCheck_39_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_tail_16_);
lean_inc(v_value_15_);
lean_inc(v_key_14_);
lean_dec(v_x_13_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_39_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v_fold_24_; uint64_t v___x_25_; uint64_t v___x_26_; uint64_t v___x_27_; size_t v___x_28_; size_t v___x_29_; size_t v___x_30_; size_t v___x_31_; size_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_20_ = lean_array_get_size(v_x_12_);
v___x_21_ = l_Lean_instHashableFVarId_hash(v_key_14_);
v___x_22_ = 32ULL;
v___x_23_ = lean_uint64_shift_right(v___x_21_, v___x_22_);
v_fold_24_ = lean_uint64_xor(v___x_21_, v___x_23_);
v___x_25_ = 16ULL;
v___x_26_ = lean_uint64_shift_right(v_fold_24_, v___x_25_);
v___x_27_ = lean_uint64_xor(v_fold_24_, v___x_26_);
v___x_28_ = lean_uint64_to_usize(v___x_27_);
v___x_29_ = lean_usize_of_nat(v___x_20_);
v___x_30_ = ((size_t)1ULL);
v___x_31_ = lean_usize_sub(v___x_29_, v___x_30_);
v___x_32_ = lean_usize_land(v___x_28_, v___x_31_);
v___x_33_ = lean_array_uget_borrowed(v_x_12_, v___x_32_);
lean_inc(v___x_33_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 2, v___x_33_);
v___x_35_ = v___x_18_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_key_14_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_value_15_);
lean_ctor_set(v_reuseFailAlloc_38_, 2, v___x_33_);
v___x_35_ = v_reuseFailAlloc_38_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; 
v___x_36_ = lean_array_uset(v_x_12_, v___x_32_, v___x_35_);
v_x_12_ = v___x_36_;
v_x_13_ = v_tail_16_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(lean_object* v_i_40_, lean_object* v_source_41_, lean_object* v_target_42_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_array_get_size(v_source_41_);
v___x_44_ = lean_nat_dec_lt(v_i_40_, v___x_43_);
if (v___x_44_ == 0)
{
lean_dec_ref(v_source_41_);
lean_dec(v_i_40_);
return v_target_42_;
}
else
{
lean_object* v_es_45_; lean_object* v___x_46_; lean_object* v_source_47_; lean_object* v_target_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_es_45_ = lean_array_fget(v_source_41_, v_i_40_);
v___x_46_ = lean_box(0);
v_source_47_ = lean_array_fset(v_source_41_, v_i_40_, v___x_46_);
v_target_48_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(v_target_42_, v_es_45_);
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = lean_nat_add(v_i_40_, v___x_49_);
lean_dec(v_i_40_);
v_i_40_ = v___x_50_;
v_source_41_ = v_source_47_;
v_target_42_ = v_target_48_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(lean_object* v_data_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_nbuckets_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_53_ = lean_array_get_size(v_data_52_);
v___x_54_ = lean_unsigned_to_nat(2u);
v_nbuckets_55_ = lean_nat_mul(v___x_53_, v___x_54_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_box(0);
v___x_58_ = lean_mk_array(v_nbuckets_55_, v___x_57_);
v___x_59_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(v___x_56_, v_data_52_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(lean_object* v_m_60_, lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
lean_object* v_size_63_; lean_object* v_buckets_64_; lean_object* v___x_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v_fold_69_; uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; lean_object* v_bkt_78_; uint8_t v___x_79_; 
v_size_63_ = lean_ctor_get(v_m_60_, 0);
v_buckets_64_ = lean_ctor_get(v_m_60_, 1);
v___x_65_ = lean_array_get_size(v_buckets_64_);
v___x_66_ = l_Lean_instHashableFVarId_hash(v_a_61_);
v___x_67_ = 32ULL;
v___x_68_ = lean_uint64_shift_right(v___x_66_, v___x_67_);
v_fold_69_ = lean_uint64_xor(v___x_66_, v___x_68_);
v___x_70_ = 16ULL;
v___x_71_ = lean_uint64_shift_right(v_fold_69_, v___x_70_);
v___x_72_ = lean_uint64_xor(v_fold_69_, v___x_71_);
v___x_73_ = lean_uint64_to_usize(v___x_72_);
v___x_74_ = lean_usize_of_nat(v___x_65_);
v___x_75_ = ((size_t)1ULL);
v___x_76_ = lean_usize_sub(v___x_74_, v___x_75_);
v___x_77_ = lean_usize_land(v___x_73_, v___x_76_);
v_bkt_78_ = lean_array_uget_borrowed(v_buckets_64_, v___x_77_);
v___x_79_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_61_, v_bkt_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_100_; 
lean_inc_ref(v_buckets_64_);
lean_inc(v_size_63_);
v_isSharedCheck_100_ = !lean_is_exclusive(v_m_60_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; 
v_unused_101_ = lean_ctor_get(v_m_60_, 1);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_m_60_, 0);
lean_dec(v_unused_102_);
v___x_81_ = v_m_60_;
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_m_60_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_100_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v_size_x27_84_; lean_object* v___x_85_; lean_object* v_buckets_x27_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_83_ = lean_unsigned_to_nat(1u);
v_size_x27_84_ = lean_nat_add(v_size_63_, v___x_83_);
lean_dec(v_size_63_);
lean_inc(v_bkt_78_);
v___x_85_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_85_, 0, v_a_61_);
lean_ctor_set(v___x_85_, 1, v_b_62_);
lean_ctor_set(v___x_85_, 2, v_bkt_78_);
v_buckets_x27_86_ = lean_array_uset(v_buckets_64_, v___x_77_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(4u);
v___x_88_ = lean_nat_mul(v_size_x27_84_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_nat_div(v___x_88_, v___x_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_array_get_size(v_buckets_x27_86_);
v___x_92_ = lean_nat_dec_le(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
if (v___x_92_ == 0)
{
lean_object* v_val_93_; lean_object* v___x_95_; 
v_val_93_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(v_buckets_x27_86_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_val_93_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_95_ = v___x_81_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_val_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v___x_98_; 
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v_buckets_x27_86_);
lean_ctor_set(v___x_81_, 0, v_size_x27_84_);
v___x_98_ = v___x_81_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_size_x27_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_buckets_x27_86_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_dec(v_b_62_);
lean_dec(v_a_61_);
return v_m_60_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(lean_object* v_k_103_, lean_object* v_t_104_){
_start:
{
if (lean_obj_tag(v_t_104_) == 0)
{
lean_object* v_k_105_; lean_object* v_l_106_; lean_object* v_r_107_; uint8_t v___x_108_; 
v_k_105_ = lean_ctor_get(v_t_104_, 1);
v_l_106_ = lean_ctor_get(v_t_104_, 3);
v_r_107_ = lean_ctor_get(v_t_104_, 4);
v___x_108_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_103_, v_k_105_);
switch(v___x_108_)
{
case 0:
{
v_t_104_ = v_l_106_;
goto _start;
}
case 1:
{
uint8_t v___x_110_; 
v___x_110_ = 1;
return v___x_110_;
}
default: 
{
v_t_104_ = v_r_107_;
goto _start;
}
}
}
else
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg___boxed(lean_object* v_k_113_, lean_object* v_t_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_113_, v_t_114_);
lean_dec(v_t_114_);
lean_dec(v_k_113_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object* v_fvarId_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_params_121_; uint8_t v___x_122_; 
v_params_121_ = lean_ctor_get(v_a_118_, 1);
v___x_122_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_fvarId_117_, v_params_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_fvarId_117_);
v___x_123_ = lean_box(0);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_125_ = lean_st_ref_take(v_a_119_);
v___x_126_ = lean_box(0);
v___x_127_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v___x_125_, v_fvarId_117_, v___x_126_);
v___x_128_ = lean_st_ref_set(v_a_119_, v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_126_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object* v_fvarId_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_130_, v_a_131_, v_a_132_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object* v_fvarId_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_135_, v_a_136_, v_a_137_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object* v_fvarId_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar(v_fvarId_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_152_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(lean_object* v_00_u03b2_153_, lean_object* v_k_154_, lean_object* v_t_155_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_154_, v_t_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___boxed(lean_object* v_00_u03b2_157_, lean_object* v_k_158_, lean_object* v_t_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(v_00_u03b2_157_, v_k_158_, v_t_159_);
lean_dec(v_t_159_);
lean_dec(v_k_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1(lean_object* v_00_u03b2_162_, lean_object* v_m_163_, lean_object* v_a_164_, lean_object* v_b_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v_m_163_, v_a_164_, v_b_165_);
return v___x_166_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(lean_object* v_00_u03b2_167_, lean_object* v_a_168_, lean_object* v_x_169_){
_start:
{
uint8_t v___x_170_; 
v___x_170_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_168_, v_x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___boxed(lean_object* v_00_u03b2_171_, lean_object* v_a_172_, lean_object* v_x_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(v_00_u03b2_171_, v_a_172_, v_x_173_);
lean_dec(v_x_173_);
lean_dec(v_a_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2(lean_object* v_00_u03b2_176_, lean_object* v_data_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(v_data_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_179_, lean_object* v_i_180_, lean_object* v_source_181_, lean_object* v_target_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(v_i_180_, v_source_181_, v_target_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_184_, lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(v_x_185_, v_x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object* v_arg_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
if (lean_obj_tag(v_arg_188_) == 1)
{
lean_object* v_fvarId_192_; lean_object* v___x_193_; 
v_fvarId_192_ = lean_ctor_get(v_arg_188_, 0);
lean_inc(v_fvarId_192_);
lean_dec_ref(v_arg_188_);
v___x_193_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_192_, v_a_189_, v_a_190_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec(v_arg_188_);
v___x_194_ = lean_box(0);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object* v_arg_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object* v_arg_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_201_, v_a_202_, v_a_203_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object* v_arg_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Compiler_LCNF_FindUsed_visitArg(v_arg_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object* v_as_219_, size_t v_sz_220_, size_t v_i_221_, lean_object* v_b_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_a_227_; uint8_t v___x_231_; 
v___x_231_ = lean_usize_dec_lt(v_i_221_, v_sz_220_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v_b_222_);
return v___x_232_;
}
else
{
lean_object* v_array_233_; lean_object* v_start_234_; lean_object* v_stop_235_; uint8_t v___x_236_; 
v_array_233_ = lean_ctor_get(v_b_222_, 0);
v_start_234_ = lean_ctor_get(v_b_222_, 1);
v_stop_235_ = lean_ctor_get(v_b_222_, 2);
v___x_236_ = lean_nat_dec_lt(v_start_234_, v_stop_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v_b_222_);
return v___x_237_;
}
else
{
lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_260_; 
lean_inc(v_stop_235_);
lean_inc(v_start_234_);
lean_inc_ref(v_array_233_);
v_isSharedCheck_260_ = !lean_is_exclusive(v_b_222_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_261_ = lean_ctor_get(v_b_222_, 2);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_b_222_, 1);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_b_222_, 0);
lean_dec(v_unused_263_);
v___x_239_ = v_b_222_;
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
else
{
lean_dec(v_b_222_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_241_ = lean_array_fget(v_array_233_, v_start_234_);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_start_234_, v___x_242_);
lean_dec(v_start_234_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_243_);
v___x_245_ = v___x_239_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_array_233_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_stop_235_);
v___x_245_ = v_reuseFailAlloc_259_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
if (lean_obj_tag(v___x_241_) == 1)
{
lean_object* v_fvarId_246_; lean_object* v_a_247_; lean_object* v_fvarId_248_; uint8_t v___x_249_; 
v_fvarId_246_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_fvarId_246_);
lean_dec_ref(v___x_241_);
v_a_247_ = lean_array_uget_borrowed(v_as_219_, v_i_221_);
v_fvarId_248_ = lean_ctor_get(v_a_247_, 0);
v___x_249_ = l_Lean_instBEqFVarId_beq(v_fvarId_246_, v_fvarId_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_246_, v___y_223_, v___y_224_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_dec_ref(v___x_250_);
v_a_227_ = v___x_245_;
goto v___jp_226_;
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref(v___x_245_);
v_a_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
else
{
lean_dec(v_fvarId_246_);
v_a_227_ = v___x_245_;
goto v___jp_226_;
}
}
else
{
lean_dec(v___x_241_);
v_a_227_ = v___x_245_;
goto v___jp_226_;
}
}
}
}
}
v___jp_226_:
{
size_t v___x_228_; size_t v___x_229_; 
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_i_221_, v___x_228_);
v_i_221_ = v___x_229_;
v_b_222_ = v_a_227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object* v_as_264_, lean_object* v_sz_265_, lean_object* v_i_266_, lean_object* v_b_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
size_t v_sz_boxed_271_; size_t v_i_boxed_272_; lean_object* v_res_273_; 
v_sz_boxed_271_ = lean_unbox_usize(v_sz_265_);
lean_dec(v_sz_265_);
v_i_boxed_272_ = lean_unbox_usize(v_i_266_);
lean_dec(v_i_266_);
v_res_273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_264_, v_sz_boxed_271_, v_i_boxed_272_, v_b_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec_ref(v_as_264_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object* v_a_274_, lean_object* v_b_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_array_279_; lean_object* v_start_280_; lean_object* v_stop_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_297_; 
v_array_279_ = lean_ctor_get(v_a_274_, 0);
v_start_280_ = lean_ctor_get(v_a_274_, 1);
v_stop_281_ = lean_ctor_get(v_a_274_, 2);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_274_);
if (v_isSharedCheck_297_ == 0)
{
v___x_283_ = v_a_274_;
v_isShared_284_ = v_isSharedCheck_297_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_stop_281_);
lean_inc(v_start_280_);
lean_inc(v_array_279_);
lean_dec(v_a_274_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_297_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
uint8_t v___x_285_; 
v___x_285_ = lean_nat_dec_lt(v_start_280_, v_stop_281_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
lean_del_object(v___x_283_);
lean_dec(v_stop_281_);
lean_dec(v_start_280_);
lean_dec_ref(v_array_279_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_b_275_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; lean_object* v_fvarId_288_; lean_object* v___x_289_; 
v___x_287_ = lean_array_fget_borrowed(v_array_279_, v_start_280_);
v_fvarId_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_fvarId_288_);
v___x_289_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_288_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec_ref(v___x_289_);
v___x_290_ = lean_box(0);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_start_280_, v___x_291_);
lean_dec(v_start_280_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_292_);
v___x_294_ = v___x_283_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_array_279_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_stop_281_);
v___x_294_ = v_reuseFailAlloc_296_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
v_a_274_ = v___x_294_;
v_b_275_ = v___x_290_;
goto _start;
}
}
else
{
lean_del_object(v___x_283_);
lean_dec(v_stop_281_);
lean_dec(v_start_280_);
lean_dec_ref(v_array_279_);
return v___x_289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object* v_a_298_, lean_object* v_b_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_298_, v_b_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object* v_as_304_, size_t v_i_305_, size_t v_stop_306_, lean_object* v_b_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
uint8_t v___x_311_; 
v___x_311_ = lean_usize_dec_eq(v_i_305_, v_stop_306_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_array_uget_borrowed(v_as_304_, v_i_305_);
lean_inc(v___x_312_);
v___x_313_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v___x_312_, v___y_308_, v___y_309_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; size_t v___x_315_; size_t v___x_316_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref(v___x_313_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_i_305_, v___x_315_);
v_i_305_ = v___x_316_;
v_b_307_ = v_a_314_;
goto _start;
}
else
{
return v___x_313_;
}
}
else
{
lean_object* v___x_318_; 
v___x_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_318_, 0, v_b_307_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object* v_as_319_, lean_object* v_i_320_, lean_object* v_stop_321_, lean_object* v_b_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
size_t v_i_boxed_326_; size_t v_stop_boxed_327_; lean_object* v_res_328_; 
v_i_boxed_326_ = lean_unbox_usize(v_i_320_);
lean_dec(v_i_320_);
v_stop_boxed_327_ = lean_unbox_usize(v_stop_321_);
lean_dec(v_stop_321_);
v_res_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_319_, v_i_boxed_326_, v_stop_boxed_327_, v_b_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec_ref(v_as_319_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object* v_a_329_, lean_object* v_b_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_array_334_; lean_object* v_start_335_; lean_object* v_stop_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_351_; 
v_array_334_ = lean_ctor_get(v_a_329_, 0);
v_start_335_ = lean_ctor_get(v_a_329_, 1);
v_stop_336_ = lean_ctor_get(v_a_329_, 2);
v_isSharedCheck_351_ = !lean_is_exclusive(v_a_329_);
if (v_isSharedCheck_351_ == 0)
{
v___x_338_ = v_a_329_;
v_isShared_339_ = v_isSharedCheck_351_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_stop_336_);
lean_inc(v_start_335_);
lean_inc(v_array_334_);
lean_dec(v_a_329_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_351_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
uint8_t v___x_340_; 
v___x_340_ = lean_nat_dec_lt(v_start_335_, v_stop_336_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_del_object(v___x_338_);
lean_dec(v_stop_336_);
lean_dec(v_start_335_);
lean_dec_ref(v_array_334_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v_b_330_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_array_fget_borrowed(v_array_334_, v_start_335_);
lean_inc(v___x_342_);
v___x_343_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v___x_342_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
lean_dec_ref(v___x_343_);
v___x_344_ = lean_box(0);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_add(v_start_335_, v___x_345_);
lean_dec(v_start_335_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v___x_346_);
v___x_348_ = v___x_338_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_array_334_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_350_, 2, v_stop_336_);
v___x_348_ = v_reuseFailAlloc_350_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
v_a_329_ = v___x_348_;
v_b_330_ = v___x_344_;
goto _start;
}
}
else
{
lean_del_object(v___x_338_);
lean_dec(v_stop_336_);
lean_dec(v_start_335_);
lean_dec_ref(v_array_334_);
return v___x_343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object* v_a_352_, lean_object* v_b_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_352_, v_b_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object* v_e_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
switch(lean_obj_tag(v_e_358_))
{
case 0:
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v_a_359_);
v_isSharedCheck_373_ = !lean_is_exclusive(v_e_358_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v_e_358_, 0);
lean_dec(v_unused_374_);
v___x_367_ = v_e_358_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_dec(v_e_358_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_box(0);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
case 1:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
lean_dec_ref(v_a_359_);
v___x_375_ = lean_box(0);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
case 2:
{
lean_object* v_struct_377_; lean_object* v___x_378_; 
v_struct_377_ = lean_ctor_get(v_e_358_, 2);
lean_inc(v_struct_377_);
lean_dec_ref(v_e_358_);
v___x_378_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_struct_377_, v_a_359_, v_a_360_);
lean_dec_ref(v_a_359_);
return v___x_378_;
}
case 3:
{
lean_object* v_decl_379_; lean_object* v_toSignature_380_; lean_object* v_declName_381_; lean_object* v_args_382_; lean_object* v_name_383_; lean_object* v_params_384_; lean_object* v___y_386_; lean_object* v_lower_387_; lean_object* v_upper_388_; uint8_t v___x_399_; 
v_decl_379_ = lean_ctor_get(v_a_359_, 0);
v_toSignature_380_ = lean_ctor_get(v_decl_379_, 0);
v_declName_381_ = lean_ctor_get(v_e_358_, 0);
lean_inc(v_declName_381_);
v_args_382_ = lean_ctor_get(v_e_358_, 2);
lean_inc_ref(v_args_382_);
lean_dec_ref(v_e_358_);
v_name_383_ = lean_ctor_get(v_toSignature_380_, 0);
v_params_384_ = lean_ctor_get(v_toSignature_380_, 3);
v___x_399_ = lean_name_eq(v_declName_381_, v_name_383_);
lean_dec(v_declName_381_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_array_get_size(v_args_382_);
v___x_402_ = lean_box(0);
v___x_403_ = lean_nat_dec_lt(v___x_400_, v___x_401_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
lean_dec_ref(v_args_382_);
lean_dec_ref(v_a_359_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
return v___x_404_;
}
else
{
uint8_t v___x_405_; 
v___x_405_ = lean_nat_dec_le(v___x_401_, v___x_401_);
if (v___x_405_ == 0)
{
if (v___x_403_ == 0)
{
lean_object* v___x_406_; 
lean_dec_ref(v_args_382_);
lean_dec_ref(v_a_359_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_402_);
return v___x_406_;
}
else
{
size_t v___x_407_; size_t v___x_408_; lean_object* v___x_409_; 
v___x_407_ = ((size_t)0ULL);
v___x_408_ = lean_usize_of_nat(v___x_401_);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_382_, v___x_407_, v___x_408_, v___x_402_, v_a_359_, v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_args_382_);
return v___x_409_;
}
}
else
{
size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; 
v___x_410_ = ((size_t)0ULL);
v___x_411_ = lean_usize_of_nat(v___x_401_);
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_382_, v___x_410_, v___x_411_, v___x_402_, v_a_359_, v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_args_382_);
return v___x_412_;
}
}
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; size_t v_sz_416_; size_t v___x_417_; lean_object* v___x_418_; 
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_array_get_size(v_args_382_);
lean_inc_ref(v_args_382_);
v___x_415_ = l_Array_toSubarray___redArg(v_args_382_, v___x_413_, v___x_414_);
v_sz_416_ = lean_array_size(v_params_384_);
v___x_417_ = ((size_t)0ULL);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_params_384_, v_sz_416_, v___x_417_, v___x_415_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_lower_420_; lean_object* v_upper_421_; lean_object* v___x_427_; uint8_t v___x_428_; 
lean_dec_ref(v___x_418_);
v___x_427_ = lean_array_get_size(v_params_384_);
v___x_428_ = lean_nat_dec_le(v___x_427_, v___x_413_);
if (v___x_428_ == 0)
{
v_lower_420_ = v___x_427_;
v_upper_421_ = v___x_414_;
goto v___jp_419_;
}
else
{
v_lower_420_ = v___x_413_;
v_upper_421_ = v___x_414_;
goto v___jp_419_;
}
v___jp_419_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = l_Array_toSubarray___redArg(v_args_382_, v_lower_420_, v_upper_421_);
v___x_423_ = lean_box(0);
v___x_424_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v___x_422_, v___x_423_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v___x_425_; uint8_t v___x_426_; 
lean_dec_ref(v___x_424_);
v___x_425_ = lean_array_get_size(v_params_384_);
v___x_426_ = lean_nat_dec_le(v___x_414_, v___x_413_);
if (v___x_426_ == 0)
{
v___y_386_ = v___x_423_;
v_lower_387_ = v___x_414_;
v_upper_388_ = v___x_425_;
goto v___jp_385_;
}
else
{
v___y_386_ = v___x_423_;
v_lower_387_ = v___x_413_;
v_upper_388_ = v___x_425_;
goto v___jp_385_;
}
}
else
{
lean_dec_ref(v_a_359_);
return v___x_424_;
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_args_382_);
lean_dec_ref(v_a_359_);
v_a_429_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_418_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_418_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
v___jp_385_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_inc_ref(v_params_384_);
v___x_389_ = l_Array_toSubarray___redArg(v_params_384_, v_lower_387_, v_upper_388_);
v___x_390_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v___x_389_, v___y_386_, v_a_359_, v_a_360_);
lean_dec_ref(v_a_359_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_390_, 0);
lean_dec(v_unused_398_);
v___x_392_ = v___x_390_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_dec(v___x_390_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___y_386_);
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___y_386_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
return v___x_390_;
}
}
}
default: 
{
lean_object* v_fvarId_437_; lean_object* v_args_438_; lean_object* v___x_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_460_; 
v_fvarId_437_ = lean_ctor_get(v_e_358_, 0);
lean_inc(v_fvarId_437_);
v_args_438_ = lean_ctor_get(v_e_358_, 1);
lean_inc_ref(v_args_438_);
lean_dec_ref(v_e_358_);
v___x_439_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_437_, v_a_359_, v_a_360_);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v___x_439_, 0);
lean_dec(v_unused_461_);
v___x_441_ = v___x_439_;
v_isShared_442_ = v_isSharedCheck_460_;
goto v_resetjp_440_;
}
else
{
lean_dec(v___x_439_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_460_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_array_get_size(v_args_438_);
v___x_445_ = lean_box(0);
v___x_446_ = lean_nat_dec_lt(v___x_443_, v___x_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_448_; 
lean_dec_ref(v_args_438_);
lean_dec_ref(v_a_359_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_445_);
v___x_448_ = v___x_441_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_445_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
else
{
uint8_t v___x_450_; 
v___x_450_ = lean_nat_dec_le(v___x_444_, v___x_444_);
if (v___x_450_ == 0)
{
if (v___x_446_ == 0)
{
lean_object* v___x_452_; 
lean_dec_ref(v_args_438_);
lean_dec_ref(v_a_359_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_445_);
v___x_452_ = v___x_441_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_445_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; 
lean_del_object(v___x_441_);
v___x_454_ = ((size_t)0ULL);
v___x_455_ = lean_usize_of_nat(v___x_444_);
v___x_456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_438_, v___x_454_, v___x_455_, v___x_445_, v_a_359_, v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_args_438_);
return v___x_456_;
}
}
else
{
size_t v___x_457_; size_t v___x_458_; lean_object* v___x_459_; 
lean_del_object(v___x_441_);
v___x_457_ = ((size_t)0ULL);
v___x_458_ = lean_usize_of_nat(v___x_444_);
v___x_459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_438_, v___x_457_, v___x_458_, v___x_445_, v_a_359_, v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_args_438_);
return v___x_459_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object* v_e_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_e_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object* v_as_471_, size_t v_i_472_, size_t v_stop_473_, lean_object* v_b_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_471_, v_i_472_, v_stop_473_, v_b_474_, v___y_475_, v___y_476_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object* v_as_483_, lean_object* v_i_484_, lean_object* v_stop_485_, lean_object* v_b_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
size_t v_i_boxed_494_; size_t v_stop_boxed_495_; lean_object* v_res_496_; 
v_i_boxed_494_ = lean_unbox_usize(v_i_484_);
lean_dec(v_i_484_);
v_stop_boxed_495_ = lean_unbox_usize(v_stop_485_);
lean_dec(v_stop_485_);
v_res_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(v_as_483_, v_i_boxed_494_, v_stop_boxed_495_, v_b_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec_ref(v_as_483_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object* v_as_497_, size_t v_sz_498_, size_t v_i_499_, lean_object* v_b_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_497_, v_sz_498_, v_i_499_, v_b_500_, v___y_501_, v___y_502_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object* v_as_509_, lean_object* v_sz_510_, lean_object* v_i_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
size_t v_sz_boxed_520_; size_t v_i_boxed_521_; lean_object* v_res_522_; 
v_sz_boxed_520_ = lean_unbox_usize(v_sz_510_);
lean_dec(v_sz_510_);
v_i_boxed_521_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(v_as_509_, v_sz_boxed_520_, v_i_boxed_521_, v_b_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v_as_509_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object* v_inst_523_, lean_object* v_R_524_, lean_object* v_a_525_, lean_object* v_b_526_, lean_object* v_c_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_525_, v_b_526_, v___y_528_, v___y_529_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object* v_inst_536_, lean_object* v_R_537_, lean_object* v_a_538_, lean_object* v_b_539_, lean_object* v_c_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(v_inst_536_, v_R_537_, v_a_538_, v_b_539_, v_c_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object* v_inst_549_, lean_object* v_R_550_, lean_object* v_a_551_, lean_object* v_b_552_, lean_object* v_c_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_551_, v_b_552_, v___y_554_, v___y_555_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object* v_inst_562_, lean_object* v_R_563_, lean_object* v_a_564_, lean_object* v_b_565_, lean_object* v_c_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(v_inst_562_, v_R_563_, v_a_564_, v_b_565_, v_c_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object* v_code_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_decl_584_; lean_object* v_k_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; 
switch(lean_obj_tag(v_code_575_))
{
case 0:
{
lean_object* v_decl_595_; lean_object* v_k_596_; lean_object* v_value_597_; lean_object* v___x_598_; 
v_decl_595_ = lean_ctor_get(v_code_575_, 0);
lean_inc_ref(v_decl_595_);
v_k_596_ = lean_ctor_get(v_code_575_, 1);
lean_inc_ref(v_k_596_);
lean_dec_ref(v_code_575_);
v_value_597_ = lean_ctor_get(v_decl_595_, 3);
lean_inc(v_value_597_);
lean_dec_ref(v_decl_595_);
lean_inc_ref(v_a_576_);
v___x_598_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_value_597_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_dec_ref(v___x_598_);
v_code_575_ = v_k_596_;
goto _start;
}
else
{
lean_dec_ref(v_k_596_);
lean_dec_ref(v_a_576_);
return v___x_598_;
}
}
case 3:
{
lean_object* v_args_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_args_600_ = lean_ctor_get(v_code_575_, 1);
lean_inc_ref(v_args_600_);
lean_dec_ref(v_code_575_);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_array_get_size(v_args_600_);
v___x_603_ = lean_box(0);
v___x_604_ = lean_nat_dec_lt(v___x_601_, v___x_602_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_dec_ref(v_args_600_);
lean_dec_ref(v_a_576_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
return v___x_605_;
}
else
{
uint8_t v___x_606_; 
v___x_606_ = lean_nat_dec_le(v___x_602_, v___x_602_);
if (v___x_606_ == 0)
{
if (v___x_604_ == 0)
{
lean_object* v___x_607_; 
lean_dec_ref(v_args_600_);
lean_dec_ref(v_a_576_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_603_);
return v___x_607_;
}
else
{
size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; 
v___x_608_ = ((size_t)0ULL);
v___x_609_ = lean_usize_of_nat(v___x_602_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_600_, v___x_608_, v___x_609_, v___x_603_, v_a_576_, v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec_ref(v_args_600_);
return v___x_610_;
}
}
else
{
size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
v___x_611_ = ((size_t)0ULL);
v___x_612_ = lean_usize_of_nat(v___x_602_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_600_, v___x_611_, v___x_612_, v___x_603_, v_a_576_, v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec_ref(v_args_600_);
return v___x_613_;
}
}
}
case 4:
{
lean_object* v_cases_614_; lean_object* v_discr_615_; lean_object* v_alts_616_; lean_object* v___x_617_; 
v_cases_614_ = lean_ctor_get(v_code_575_, 0);
lean_inc_ref(v_cases_614_);
lean_dec_ref(v_code_575_);
v_discr_615_ = lean_ctor_get(v_cases_614_, 2);
lean_inc(v_discr_615_);
v_alts_616_ = lean_ctor_get(v_cases_614_, 3);
lean_inc_ref(v_alts_616_);
lean_dec_ref(v_cases_614_);
v___x_617_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_discr_615_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_638_; 
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_638_ == 0)
{
lean_object* v_unused_639_; 
v_unused_639_ = lean_ctor_get(v___x_617_, 0);
lean_dec(v_unused_639_);
v___x_619_ = v___x_617_;
v_isShared_620_ = v_isSharedCheck_638_;
goto v_resetjp_618_;
}
else
{
lean_dec(v___x_617_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_638_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_array_get_size(v_alts_616_);
v___x_623_ = lean_box(0);
v___x_624_ = lean_nat_dec_lt(v___x_621_, v___x_622_);
if (v___x_624_ == 0)
{
lean_object* v___x_626_; 
lean_dec_ref(v_alts_616_);
lean_dec_ref(v_a_576_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_623_);
v___x_626_ = v___x_619_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_623_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
uint8_t v___x_628_; 
v___x_628_ = lean_nat_dec_le(v___x_622_, v___x_622_);
if (v___x_628_ == 0)
{
if (v___x_624_ == 0)
{
lean_object* v___x_630_; 
lean_dec_ref(v_alts_616_);
lean_dec_ref(v_a_576_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_623_);
v___x_630_ = v___x_619_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_623_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
else
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
lean_del_object(v___x_619_);
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_622_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_616_, v___x_632_, v___x_633_, v___x_623_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec_ref(v_alts_616_);
return v___x_634_;
}
}
else
{
size_t v___x_635_; size_t v___x_636_; lean_object* v___x_637_; 
lean_del_object(v___x_619_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = lean_usize_of_nat(v___x_622_);
v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_616_, v___x_635_, v___x_636_, v___x_623_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec_ref(v_alts_616_);
return v___x_637_;
}
}
}
}
else
{
lean_dec_ref(v_alts_616_);
lean_dec_ref(v_a_576_);
return v___x_617_;
}
}
case 5:
{
lean_object* v_fvarId_640_; lean_object* v___x_641_; 
v_fvarId_640_ = lean_ctor_get(v_code_575_, 0);
lean_inc(v_fvarId_640_);
lean_dec_ref(v_code_575_);
v___x_641_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_640_, v_a_576_, v_a_577_);
lean_dec_ref(v_a_576_);
return v___x_641_;
}
case 6:
{
lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
lean_dec_ref(v_a_576_);
v_isSharedCheck_649_ = !lean_is_exclusive(v_code_575_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_code_575_, 0);
lean_dec(v_unused_650_);
v___x_643_ = v_code_575_;
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
else
{
lean_dec(v_code_575_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_649_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = lean_box(0);
if (v_isShared_644_ == 0)
{
lean_ctor_set_tag(v___x_643_, 0);
lean_ctor_set(v___x_643_, 0, v___x_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
default: 
{
lean_object* v_decl_651_; lean_object* v_k_652_; 
v_decl_651_ = lean_ctor_get(v_code_575_, 0);
lean_inc_ref(v_decl_651_);
v_k_652_ = lean_ctor_get(v_code_575_, 1);
lean_inc_ref(v_k_652_);
lean_dec_ref(v_code_575_);
v_decl_584_ = v_decl_651_;
v_k_585_ = v_k_652_;
v___y_586_ = v_a_576_;
v___y_587_ = v_a_577_;
v___y_588_ = v_a_578_;
v___y_589_ = v_a_579_;
v___y_590_ = v_a_580_;
v___y_591_ = v_a_581_;
goto v___jp_583_;
}
}
v___jp_583_:
{
lean_object* v_value_592_; lean_object* v___x_593_; 
v_value_592_ = lean_ctor_get(v_decl_584_, 4);
lean_inc_ref(v_value_592_);
lean_dec_ref(v_decl_584_);
lean_inc_ref(v___y_586_);
v___x_593_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_value_592_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_dec_ref(v___x_593_);
v_code_575_ = v_k_585_;
v_a_576_ = v___y_586_;
v_a_577_ = v___y_587_;
v_a_578_ = v___y_588_;
v_a_579_ = v___y_589_;
v_a_580_ = v___y_590_;
v_a_581_ = v___y_591_;
goto _start;
}
else
{
lean_dec_ref(v___y_586_);
lean_dec_ref(v_k_585_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object* v_as_653_, size_t v_i_654_, size_t v_stop_655_, lean_object* v_b_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___y_665_; uint8_t v___x_671_; 
v___x_671_ = lean_usize_dec_eq(v_i_654_, v_stop_655_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_array_uget_borrowed(v_as_653_, v_i_654_);
switch(lean_obj_tag(v___x_672_))
{
case 0:
{
lean_object* v_code_673_; 
v_code_673_ = lean_ctor_get(v___x_672_, 2);
lean_inc_ref(v_code_673_);
v___y_665_ = v_code_673_;
goto v___jp_664_;
}
case 1:
{
lean_object* v_code_674_; 
v_code_674_ = lean_ctor_get(v___x_672_, 1);
lean_inc_ref(v_code_674_);
v___y_665_ = v_code_674_;
goto v___jp_664_;
}
default: 
{
lean_object* v_code_675_; 
v_code_675_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_code_675_);
v___y_665_ = v_code_675_;
goto v___jp_664_;
}
}
}
else
{
lean_object* v___x_676_; 
lean_dec_ref(v___y_657_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_b_656_);
return v___x_676_;
}
v___jp_664_:
{
lean_object* v___x_666_; 
lean_inc_ref(v___y_657_);
v___x_666_ = l_Lean_Compiler_LCNF_FindUsed_visit(v___y_665_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; size_t v___x_668_; size_t v___x_669_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v___x_666_);
v___x_668_ = ((size_t)1ULL);
v___x_669_ = lean_usize_add(v_i_654_, v___x_668_);
v_i_654_ = v___x_669_;
v_b_656_ = v_a_667_;
goto _start;
}
else
{
lean_dec_ref(v___y_657_);
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object* v_as_677_, lean_object* v_i_678_, lean_object* v_stop_679_, lean_object* v_b_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
size_t v_i_boxed_688_; size_t v_stop_boxed_689_; lean_object* v_res_690_; 
v_i_boxed_688_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_stop_boxed_689_ = lean_unbox_usize(v_stop_679_);
lean_dec(v_stop_679_);
v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_as_677_, v_i_boxed_688_, v_stop_boxed_689_, v_b_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v_as_677_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object* v_code_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_code_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(lean_object* v_f_700_, lean_object* v_v_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
if (lean_obj_tag(v_v_701_) == 0)
{
lean_object* v_code_709_; lean_object* v___x_710_; 
v_code_709_ = lean_ctor_get(v_v_701_, 0);
lean_inc_ref(v_code_709_);
lean_dec_ref(v_v_701_);
v___x_710_ = lean_apply_8(v_f_700_, v_code_709_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, lean_box(0));
return v___x_710_;
}
else
{
lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_718_; 
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec_ref(v_f_700_);
v_isSharedCheck_718_ = !lean_is_exclusive(v_v_701_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_v_701_, 0);
lean_dec(v_unused_719_);
v___x_712_ = v_v_701_;
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
else
{
lean_dec(v_v_701_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_box(0);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 0);
lean_ctor_set(v___x_712_, 0, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg___boxed(lean_object* v_f_720_, lean_object* v_v_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_720_, v_v_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(uint8_t v_pu_730_, lean_object* v_f_731_, lean_object* v_v_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_731_, v_v_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___boxed(lean_object* v_pu_741_, lean_object* v_f_742_, lean_object* v_v_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
uint8_t v_pu_boxed_751_; lean_object* v_res_752_; 
v_pu_boxed_751_ = lean_unbox(v_pu_741_);
v_res_752_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(v_pu_boxed_751_, v_f_742_, v_v_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object* v_as_753_, size_t v_i_754_, size_t v_stop_755_, lean_object* v_b_756_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = lean_usize_dec_eq(v_i_754_, v_stop_755_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v_fvarId_759_; lean_object* v___x_760_; size_t v___x_761_; size_t v___x_762_; 
v___x_758_ = lean_array_uget_borrowed(v_as_753_, v_i_754_);
v_fvarId_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_fvarId_759_);
v___x_760_ = l_Lean_FVarIdSet_insert(v_b_756_, v_fvarId_759_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_754_, v___x_761_);
v_i_754_ = v___x_762_;
v_b_756_ = v___x_760_;
goto _start;
}
else
{
return v_b_756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object* v_as_764_, lean_object* v_i_765_, lean_object* v_stop_766_, lean_object* v_b_767_){
_start:
{
size_t v_i_boxed_768_; size_t v_stop_boxed_769_; lean_object* v_res_770_; 
v_i_boxed_768_ = lean_unbox_usize(v_i_765_);
lean_dec(v_i_765_);
v_stop_boxed_769_ = lean_unbox_usize(v_stop_766_);
lean_dec(v_stop_766_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_as_764_, v_i_boxed_768_, v_stop_boxed_769_, v_b_767_);
lean_dec_ref(v_as_764_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object* v_decl_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_toSignature_778_; lean_object* v_value_779_; lean_object* v_params_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___y_784_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_toSignature_778_ = lean_ctor_get(v_decl_772_, 0);
v_value_779_ = lean_ctor_get(v_decl_772_, 1);
lean_inc_ref(v_value_779_);
v_params_780_ = lean_ctor_get(v_toSignature_778_, 3);
v___x_781_ = lean_box(1);
v___x_782_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = lean_array_get_size(v_params_780_);
v___x_808_ = lean_nat_dec_lt(v___x_806_, v___x_807_);
if (v___x_808_ == 0)
{
v___y_784_ = v___x_781_;
goto v___jp_783_;
}
else
{
uint8_t v___x_809_; 
v___x_809_ = lean_nat_dec_le(v___x_807_, v___x_807_);
if (v___x_809_ == 0)
{
if (v___x_808_ == 0)
{
v___y_784_ = v___x_781_;
goto v___jp_783_;
}
else
{
size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v___x_810_ = ((size_t)0ULL);
v___x_811_ = lean_usize_of_nat(v___x_807_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_780_, v___x_810_, v___x_811_, v___x_781_);
v___y_784_ = v___x_812_;
goto v___jp_783_;
}
}
else
{
size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
v___x_813_ = ((size_t)0ULL);
v___x_814_ = lean_usize_of_nat(v___x_807_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_780_, v___x_813_, v___x_814_, v___x_781_);
v___y_784_ = v___x_815_;
goto v___jp_783_;
}
}
v___jp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_785_ = lean_st_mk_ref(v___x_782_);
v___x_786_ = ((lean_object*)(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0));
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_decl_772_);
lean_ctor_set(v___x_787_, 1, v___y_784_);
lean_inc(v___x_785_);
v___x_788_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v___x_786_, v_value_779_, v___x_787_, v___x_785_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v___x_788_, 0);
lean_dec(v_unused_797_);
v___x_790_ = v___x_788_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_dec(v___x_788_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_st_ref_get(v___x_785_);
lean_dec(v___x_785_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v___x_785_);
v_a_798_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_788_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_788_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(lean_object* v_decl_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v_res_822_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0(void){
_start:
{
uint8_t v___x_823_; lean_object* v___x_824_; 
v___x_823_ = 0;
v___x_824_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object* v_msg_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0);
v___x_827_ = lean_panic_fn(v___x_826_, v_msg_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(lean_object* v_args_828_, lean_object* v_upperBound_829_, lean_object* v___x_830_, lean_object* v_a_831_, lean_object* v_b_832_){
_start:
{
lean_object* v_a_835_; uint8_t v___x_842_; 
v___x_842_ = lean_nat_dec_lt(v_a_831_, v_upperBound_829_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec(v_a_831_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v_b_832_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_array_get_size(v___x_830_);
v___x_845_ = lean_nat_dec_lt(v_a_831_, v___x_844_);
if (v___x_845_ == 0)
{
goto v___jp_839_;
}
else
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_array_fget_borrowed(v___x_830_, v_a_831_);
v___x_847_ = lean_unbox(v___x_846_);
if (v___x_847_ == 0)
{
v_a_835_ = v_b_832_;
goto v___jp_834_;
}
else
{
goto v___jp_839_;
}
}
}
v___jp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lean_nat_add(v_a_831_, v___x_836_);
lean_dec(v_a_831_);
v_a_831_ = v___x_837_;
v_b_832_ = v_a_835_;
goto _start;
}
v___jp_839_:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_array_fget_borrowed(v_args_828_, v_a_831_);
lean_inc(v___x_840_);
v___x_841_ = lean_array_push(v_b_832_, v___x_840_);
v_a_835_ = v___x_841_;
goto v___jp_834_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(lean_object* v_args_848_, lean_object* v_upperBound_849_, lean_object* v___x_850_, lean_object* v_a_851_, lean_object* v_b_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_848_, v_upperBound_849_, v___x_850_, v_a_851_, v_b_852_);
lean_dec_ref(v___x_850_);
lean_dec(v_upperBound_849_);
lean_dec_ref(v_args_848_);
return v_res_854_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_858_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2));
v___x_859_ = lean_unsigned_to_nat(9u);
v___x_860_ = lean_unsigned_to_nat(635u);
v___x_861_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1));
v___x_862_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0));
v___x_863_ = l_mkPanicMessageWithDecl(v___x_862_, v___x_861_, v___x_860_, v___x_859_, v___x_858_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* v_code_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v___y_874_; lean_object* v___y_875_; uint8_t v___y_876_; lean_object* v___y_881_; lean_object* v___y_882_; uint8_t v___y_883_; lean_object* v_decl_888_; lean_object* v_k_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; 
switch(lean_obj_tag(v_code_866_))
{
case 0:
{
lean_object* v_decl_940_; lean_object* v_value_941_; 
v_decl_940_ = lean_ctor_get(v_code_866_, 0);
v_value_941_ = lean_ctor_get(v_decl_940_, 3);
lean_inc(v_value_941_);
if (lean_obj_tag(v_value_941_) == 3)
{
lean_object* v_k_942_; lean_object* v_declName_943_; lean_object* v_args_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1037_; 
v_k_942_ = lean_ctor_get(v_code_866_, 1);
v_declName_943_ = lean_ctor_get(v_value_941_, 0);
v_args_944_ = lean_ctor_get(v_value_941_, 2);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_value_941_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_value_941_, 1);
lean_dec(v_unused_1038_);
v___x_946_ = v_value_941_;
v_isShared_947_ = v_isSharedCheck_1037_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_args_944_);
lean_inc(v_declName_943_);
lean_dec(v_value_941_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1037_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_declName_948_; lean_object* v_auxDeclName_949_; lean_object* v_paramMask_950_; uint8_t v___x_951_; 
v_declName_948_ = lean_ctor_get(v_a_867_, 0);
v_auxDeclName_949_ = lean_ctor_get(v_a_867_, 1);
v_paramMask_950_ = lean_ctor_get(v_a_867_, 2);
v___x_951_ = lean_name_eq(v_declName_943_, v_declName_948_);
lean_dec(v_declName_943_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_del_object(v___x_946_);
lean_dec_ref(v_args_944_);
lean_inc_ref(v_k_942_);
v___x_952_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_942_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_979_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_979_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_979_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_979_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
uint8_t v___y_958_; size_t v___x_974_; size_t v___x_975_; uint8_t v___x_976_; 
v___x_974_ = lean_ptr_addr(v_k_942_);
v___x_975_ = lean_ptr_addr(v_a_953_);
v___x_976_ = lean_usize_dec_eq(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
v___y_958_ = v___x_976_;
goto v___jp_957_;
}
else
{
size_t v___x_977_; uint8_t v___x_978_; 
v___x_977_ = lean_ptr_addr(v_decl_940_);
v___x_978_ = lean_usize_dec_eq(v___x_977_, v___x_977_);
v___y_958_ = v___x_978_;
goto v___jp_957_;
}
v___jp_957_:
{
if (v___y_958_ == 0)
{
lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_968_; 
lean_inc_ref(v_decl_940_);
v_isSharedCheck_968_ = !lean_is_exclusive(v_code_866_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; lean_object* v_unused_970_; 
v_unused_969_ = lean_ctor_get(v_code_866_, 1);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_code_866_, 0);
lean_dec(v_unused_970_);
v___x_960_ = v_code_866_;
v_isShared_961_ = v_isSharedCheck_968_;
goto v_resetjp_959_;
}
else
{
lean_dec(v_code_866_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_968_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_a_953_);
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_decl_940_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_a_953_);
v___x_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_965_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_963_);
v___x_965_ = v___x_955_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_object* v___x_972_; 
lean_dec(v_a_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v_code_866_);
v___x_972_ = v___x_955_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_code_866_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
else
{
lean_dec_ref(v_code_866_);
return v___x_952_;
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_980_ = lean_array_get_size(v_args_944_);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_944_, v___x_980_, v_paramMask_950_, v___x_981_, v___x_982_);
lean_dec_ref(v_args_944_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; uint8_t v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref(v___x_983_);
v___x_985_ = 0;
v___x_986_ = lean_box(0);
lean_inc(v_auxDeclName_949_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 2, v_a_984_);
lean_ctor_set(v___x_946_, 1, v___x_986_);
lean_ctor_set(v___x_946_, 0, v_auxDeclName_949_);
v___x_988_ = v___x_946_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_auxDeclName_949_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_a_984_);
v___x_988_ = v_reuseFailAlloc_1028_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; 
lean_inc_ref(v_decl_940_);
v___x_989_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_985_, v_decl_940_, v___x_988_, v_a_869_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref(v___x_989_);
lean_inc_ref(v_k_942_);
v___x_991_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_942_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1019_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1019_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1019_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
uint8_t v___y_997_; size_t v___x_1013_; size_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1013_ = lean_ptr_addr(v_k_942_);
v___x_1014_ = lean_ptr_addr(v_a_992_);
v___x_1015_ = lean_usize_dec_eq(v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
v___y_997_ = v___x_1015_;
goto v___jp_996_;
}
else
{
size_t v___x_1016_; size_t v___x_1017_; uint8_t v___x_1018_; 
v___x_1016_ = lean_ptr_addr(v_decl_940_);
v___x_1017_ = lean_ptr_addr(v_a_990_);
v___x_1018_ = lean_usize_dec_eq(v___x_1016_, v___x_1017_);
v___y_997_ = v___x_1018_;
goto v___jp_996_;
}
v___jp_996_:
{
if (v___y_997_ == 0)
{
lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1007_; 
v_isSharedCheck_1007_ = !lean_is_exclusive(v_code_866_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; lean_object* v_unused_1009_; 
v_unused_1008_ = lean_ctor_get(v_code_866_, 1);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_code_866_, 0);
lean_dec(v_unused_1009_);
v___x_999_ = v_code_866_;
v_isShared_1000_ = v_isSharedCheck_1007_;
goto v_resetjp_998_;
}
else
{
lean_dec(v_code_866_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1007_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 1, v_a_992_);
lean_ctor_set(v___x_999_, 0, v_a_990_);
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_990_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_a_992_);
v___x_1002_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_1002_);
v___x_1004_ = v___x_994_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v___x_1011_; 
lean_dec(v_a_992_);
lean_dec(v_a_990_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v_code_866_);
v___x_1011_ = v___x_994_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_code_866_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
else
{
lean_dec(v_a_990_);
lean_dec_ref(v_code_866_);
return v___x_991_;
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec_ref(v_code_866_);
v_a_1020_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_989_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_989_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_del_object(v___x_946_);
lean_dec_ref(v_code_866_);
v_a_1029_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_983_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_983_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
}
else
{
lean_object* v_k_1039_; lean_object* v___x_1040_; 
lean_dec(v_value_941_);
v_k_1039_ = lean_ctor_get(v_code_866_, 1);
lean_inc_ref(v_k_1039_);
v___x_1040_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_1039_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1067_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1067_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1067_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
uint8_t v___y_1046_; size_t v___x_1062_; size_t v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = lean_ptr_addr(v_k_1039_);
v___x_1063_ = lean_ptr_addr(v_a_1041_);
v___x_1064_ = lean_usize_dec_eq(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
v___y_1046_ = v___x_1064_;
goto v___jp_1045_;
}
else
{
size_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_ptr_addr(v_decl_940_);
v___x_1066_ = lean_usize_dec_eq(v___x_1065_, v___x_1065_);
v___y_1046_ = v___x_1066_;
goto v___jp_1045_;
}
v___jp_1045_:
{
if (v___y_1046_ == 0)
{
lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1056_; 
lean_inc_ref(v_decl_940_);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_code_866_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; lean_object* v_unused_1058_; 
v_unused_1057_ = lean_ctor_get(v_code_866_, 1);
lean_dec(v_unused_1057_);
v_unused_1058_ = lean_ctor_get(v_code_866_, 0);
lean_dec(v_unused_1058_);
v___x_1048_ = v_code_866_;
v_isShared_1049_ = v_isSharedCheck_1056_;
goto v_resetjp_1047_;
}
else
{
lean_dec(v_code_866_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1056_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v_a_1041_);
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_decl_940_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_a_1041_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1051_);
v___x_1053_ = v___x_1043_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v___x_1060_; 
lean_dec(v_a_1041_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v_code_866_);
v___x_1060_ = v___x_1043_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_code_866_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
else
{
lean_dec_ref(v_code_866_);
return v___x_1040_;
}
}
}
case 1:
{
lean_object* v_decl_1068_; lean_object* v_k_1069_; 
v_decl_1068_ = lean_ctor_get(v_code_866_, 0);
v_k_1069_ = lean_ctor_get(v_code_866_, 1);
lean_inc_ref(v_k_1069_);
lean_inc_ref(v_decl_1068_);
v_decl_888_ = v_decl_1068_;
v_k_889_ = v_k_1069_;
v___y_890_ = v_a_867_;
v___y_891_ = v_a_868_;
v___y_892_ = v_a_869_;
v___y_893_ = v_a_870_;
v___y_894_ = v_a_871_;
goto v___jp_887_;
}
case 2:
{
lean_object* v_decl_1070_; lean_object* v_k_1071_; 
v_decl_1070_ = lean_ctor_get(v_code_866_, 0);
v_k_1071_ = lean_ctor_get(v_code_866_, 1);
lean_inc_ref(v_k_1071_);
lean_inc_ref(v_decl_1070_);
v_decl_888_ = v_decl_1070_;
v_k_889_ = v_k_1071_;
v___y_890_ = v_a_867_;
v___y_891_ = v_a_868_;
v___y_892_ = v_a_869_;
v___y_893_ = v_a_870_;
v___y_894_ = v_a_871_;
goto v___jp_887_;
}
case 4:
{
lean_object* v_cases_1072_; lean_object* v_typeName_1073_; lean_object* v_resultType_1074_; lean_object* v_discr_1075_; lean_object* v_alts_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1115_; 
v_cases_1072_ = lean_ctor_get(v_code_866_, 0);
lean_inc_ref(v_cases_1072_);
v_typeName_1073_ = lean_ctor_get(v_cases_1072_, 0);
v_resultType_1074_ = lean_ctor_get(v_cases_1072_, 1);
v_discr_1075_ = lean_ctor_get(v_cases_1072_, 2);
v_alts_1076_ = lean_ctor_get(v_cases_1072_, 3);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_cases_1072_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1078_ = v_cases_1072_;
v_isShared_1079_ = v_isSharedCheck_1115_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_alts_1076_);
lean_inc(v_discr_1075_);
lean_inc(v_resultType_1074_);
lean_inc(v_typeName_1073_);
lean_dec(v_cases_1072_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1115_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1076_);
v___x_1081_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v___x_1080_, v_alts_1076_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1106_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1106_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1106_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
size_t v___x_1086_; size_t v___x_1087_; uint8_t v___x_1088_; 
v___x_1086_ = lean_ptr_addr(v_alts_1076_);
lean_dec_ref(v_alts_1076_);
v___x_1087_ = lean_ptr_addr(v_a_1082_);
v___x_1088_ = lean_usize_dec_eq(v___x_1086_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1101_; 
v_isSharedCheck_1101_ = !lean_is_exclusive(v_code_866_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; 
v_unused_1102_ = lean_ctor_get(v_code_866_, 0);
lean_dec(v_unused_1102_);
v___x_1090_ = v_code_866_;
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v_code_866_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 3, v_a_1082_);
v___x_1093_ = v___x_1078_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_typeName_1073_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_resultType_1074_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v_discr_1075_);
lean_ctor_set(v_reuseFailAlloc_1100_, 3, v_a_1082_);
v___x_1093_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v___x_1093_);
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1095_);
v___x_1097_ = v___x_1084_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
else
{
lean_object* v___x_1104_; 
lean_dec(v_a_1082_);
lean_del_object(v___x_1078_);
lean_dec(v_discr_1075_);
lean_dec_ref(v_resultType_1074_);
lean_dec(v_typeName_1073_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v_code_866_);
v___x_1104_ = v___x_1084_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_code_866_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_del_object(v___x_1078_);
lean_dec_ref(v_alts_1076_);
lean_dec(v_discr_1075_);
lean_dec_ref(v_resultType_1074_);
lean_dec(v_typeName_1073_);
lean_dec_ref(v_code_866_);
v_a_1107_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1081_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1081_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
default: 
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_code_866_);
return v___x_1116_;
}
}
v___jp_873_:
{
if (v___y_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec_ref(v_code_866_);
v___x_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_877_, 0, v___y_875_);
lean_ctor_set(v___x_877_, 1, v___y_874_);
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
else
{
lean_object* v___x_879_; 
lean_dec_ref(v___y_875_);
lean_dec_ref(v___y_874_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v_code_866_);
return v___x_879_;
}
}
v___jp_880_:
{
if (v___y_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec_ref(v_code_866_);
v___x_884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_884_, 0, v___y_882_);
lean_ctor_set(v___x_884_, 1, v___y_881_);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
return v___x_885_;
}
else
{
lean_object* v___x_886_; 
lean_dec_ref(v___y_882_);
lean_dec_ref(v___y_881_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v_code_866_);
return v___x_886_;
}
}
v___jp_887_:
{
lean_object* v_params_895_; lean_object* v_type_896_; lean_object* v_value_897_; lean_object* v___x_898_; 
v_params_895_ = lean_ctor_get(v_decl_888_, 2);
lean_inc_ref(v_params_895_);
v_type_896_ = lean_ctor_get(v_decl_888_, 3);
lean_inc_ref(v_type_896_);
v_value_897_ = lean_ctor_get(v_decl_888_, 4);
lean_inc_ref(v_value_897_);
v___x_898_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_value_897_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; uint8_t v___x_900_; lean_object* v___x_901_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref(v___x_898_);
v___x_900_ = 0;
v___x_901_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_900_, v_decl_888_, v_type_896_, v_params_895_, v_a_899_, v___y_892_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_903_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_902_);
lean_dec_ref(v___x_901_);
v___x_903_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_903_) == 0)
{
switch(lean_obj_tag(v_code_866_))
{
case 1:
{
lean_object* v_a_904_; lean_object* v_decl_905_; lean_object* v_k_906_; size_t v___x_907_; size_t v___x_908_; uint8_t v___x_909_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref(v___x_903_);
v_decl_905_ = lean_ctor_get(v_code_866_, 0);
v_k_906_ = lean_ctor_get(v_code_866_, 1);
v___x_907_ = lean_ptr_addr(v_k_906_);
v___x_908_ = lean_ptr_addr(v_a_904_);
v___x_909_ = lean_usize_dec_eq(v___x_907_, v___x_908_);
if (v___x_909_ == 0)
{
v___y_874_ = v_a_904_;
v___y_875_ = v_a_902_;
v___y_876_ = v___x_909_;
goto v___jp_873_;
}
else
{
size_t v___x_910_; size_t v___x_911_; uint8_t v___x_912_; 
v___x_910_ = lean_ptr_addr(v_decl_905_);
v___x_911_ = lean_ptr_addr(v_a_902_);
v___x_912_ = lean_usize_dec_eq(v___x_910_, v___x_911_);
v___y_874_ = v_a_904_;
v___y_875_ = v_a_902_;
v___y_876_ = v___x_912_;
goto v___jp_873_;
}
}
case 2:
{
lean_object* v_a_913_; lean_object* v_decl_914_; lean_object* v_k_915_; size_t v___x_916_; size_t v___x_917_; uint8_t v___x_918_; 
v_a_913_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_913_);
lean_dec_ref(v___x_903_);
v_decl_914_ = lean_ctor_get(v_code_866_, 0);
v_k_915_ = lean_ctor_get(v_code_866_, 1);
v___x_916_ = lean_ptr_addr(v_k_915_);
v___x_917_ = lean_ptr_addr(v_a_913_);
v___x_918_ = lean_usize_dec_eq(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
v___y_881_ = v_a_913_;
v___y_882_ = v_a_902_;
v___y_883_ = v___x_918_;
goto v___jp_880_;
}
else
{
size_t v___x_919_; size_t v___x_920_; uint8_t v___x_921_; 
v___x_919_ = lean_ptr_addr(v_decl_914_);
v___x_920_ = lean_ptr_addr(v_a_902_);
v___x_921_ = lean_usize_dec_eq(v___x_919_, v___x_920_);
v___y_881_ = v_a_913_;
v___y_882_ = v_a_902_;
v___y_883_ = v___x_921_;
goto v___jp_880_;
}
}
default: 
{
lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_930_; 
lean_dec(v_a_902_);
lean_dec_ref(v_code_866_);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v___x_903_, 0);
lean_dec(v_unused_931_);
v___x_923_ = v___x_903_;
v_isShared_924_ = v_isSharedCheck_930_;
goto v_resetjp_922_;
}
else
{
lean_dec(v___x_903_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_930_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_925_ = lean_obj_once(&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3, &l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once, _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3);
v___x_926_ = l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(v___x_925_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_926_);
v___x_928_ = v___x_923_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
else
{
lean_dec(v_a_902_);
lean_dec_ref(v_code_866_);
return v___x_903_;
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v_k_889_);
lean_dec_ref(v_code_866_);
v_a_932_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_901_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_901_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_dec_ref(v_type_896_);
lean_dec_ref(v_params_895_);
lean_dec_ref(v_k_889_);
lean_dec_ref(v_decl_888_);
lean_dec_ref(v_code_866_);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(lean_object* v_i_1117_, lean_object* v_as_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_array_get_size(v_as_1118_);
v___x_1126_ = lean_nat_dec_lt(v_i_1117_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
lean_dec(v_i_1117_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v_as_1118_);
return v___x_1127_;
}
else
{
lean_object* v_a_1128_; lean_object* v___y_1130_; 
v_a_1128_ = lean_array_fget_borrowed(v_as_1118_, v_i_1117_);
switch(lean_obj_tag(v_a_1128_))
{
case 0:
{
lean_object* v_code_1152_; 
v_code_1152_ = lean_ctor_get(v_a_1128_, 2);
lean_inc_ref(v_code_1152_);
v___y_1130_ = v_code_1152_;
goto v___jp_1129_;
}
case 1:
{
lean_object* v_code_1153_; 
v_code_1153_ = lean_ctor_get(v_a_1128_, 1);
lean_inc_ref(v_code_1153_);
v___y_1130_ = v_code_1153_;
goto v___jp_1129_;
}
default: 
{
lean_object* v_code_1154_; 
v_code_1154_ = lean_ctor_get(v_a_1128_, 0);
lean_inc_ref(v_code_1154_);
v___y_1130_ = v_code_1154_;
goto v___jp_1129_;
}
}
v___jp_1129_:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v___y_1130_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; uint8_t v___x_1136_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref(v___x_1131_);
lean_inc(v_a_1128_);
v___x_1133_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1128_, v_a_1132_);
v___x_1134_ = lean_ptr_addr(v_a_1128_);
v___x_1135_ = lean_ptr_addr(v___x_1133_);
v___x_1136_ = lean_usize_dec_eq(v___x_1134_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_nat_add(v_i_1117_, v___x_1137_);
v___x_1139_ = lean_array_fset(v_as_1118_, v_i_1117_, v___x_1133_);
lean_dec(v_i_1117_);
v_i_1117_ = v___x_1138_;
v_as_1118_ = v___x_1139_;
goto _start;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v___x_1133_);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_add(v_i_1117_, v___x_1141_);
lean_dec(v_i_1117_);
v_i_1117_ = v___x_1142_;
goto _start;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec_ref(v_as_1118_);
lean_dec(v_i_1117_);
v_a_1144_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1131_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1131_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(lean_object* v_i_1155_, lean_object* v_as_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v_i_1155_, v_as_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec_ref(v___y_1157_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object* v_code_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_code_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object* v_args_1172_, lean_object* v_upperBound_1173_, lean_object* v___x_1174_, lean_object* v_inst_1175_, lean_object* v_R_1176_, lean_object* v_a_1177_, lean_object* v_b_1178_, lean_object* v_c_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1172_, v_upperBound_1173_, v___x_1174_, v_a_1177_, v_b_1178_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object* v_args_1187_, lean_object* v_upperBound_1188_, lean_object* v___x_1189_, lean_object* v_inst_1190_, lean_object* v_R_1191_, lean_object* v_a_1192_, lean_object* v_b_1193_, lean_object* v_c_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(v_args_1187_, v_upperBound_1188_, v___x_1189_, v_inst_1190_, v_R_1191_, v_a_1192_, v_b_1193_, v_c_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___x_1189_);
lean_dec(v_upperBound_1188_);
lean_dec_ref(v_args_1187_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object* v_f_1202_, lean_object* v_v_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
if (lean_obj_tag(v_v_1203_) == 0)
{
lean_object* v_code_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1234_; 
v_code_1210_ = lean_ctor_get(v_v_1203_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_v_1203_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1212_ = v_v_1203_;
v_isShared_1213_ = v_isSharedCheck_1234_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_code_1210_);
lean_dec(v_v_1203_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1234_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_apply_7(v_f_1202_, v_code_1210_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, lean_box(0));
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1225_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v_a_1215_);
v___x_1220_ = v___x_1212_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1220_);
v___x_1222_ = v___x_1217_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_del_object(v___x_1212_);
v_a_1226_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1214_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1214_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
else
{
lean_object* v___x_1235_; 
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_f_1202_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_v_1203_);
return v___x_1235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object* v_f_1236_, lean_object* v_v_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1236_, v_v_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(uint8_t v_pu_1245_, lean_object* v_f_1246_, lean_object* v_v_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1246_, v_v_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object* v_pu_1255_, lean_object* v_f_1256_, lean_object* v_v_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
uint8_t v_pu_boxed_1264_; lean_object* v_res_1265_; 
v_pu_boxed_1264_ = lean_unbox(v_pu_1255_);
v_res_1265_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(v_pu_boxed_1264_, v_f_1256_, v_v_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg(lean_object* v_cls_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_options_1272_; uint8_t v_hasTrace_1273_; 
v_options_1272_ = lean_ctor_get(v___y_1270_, 2);
v_hasTrace_1273_ = lean_ctor_get_uint8(v_options_1272_, sizeof(void*)*1);
if (v_hasTrace_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_dec(v_cls_1269_);
v___x_1274_ = lean_box(v_hasTrace_1273_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
return v___x_1275_;
}
else
{
lean_object* v_inheritedTraceOptions_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_inheritedTraceOptions_1276_ = lean_ctor_get(v___y_1270_, 13);
v___x_1277_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___closed__1));
v___x_1278_ = l_Lean_Name_append(v___x_1277_, v_cls_1269_);
v___x_1279_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1276_, v_options_1272_, v___x_1278_);
lean_dec(v___x_1278_);
v___x_1280_ = lean_box(v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg___boxed(lean_object* v_cls_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg(v_cls_1282_, v___y_1283_);
lean_dec_ref(v___y_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object* v_cls_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg(v_cls_1286_, v___y_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___boxed(lean_object* v_cls_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(v_cls_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1299_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0(void){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__0);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__1);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
lean_ctor_set(v___x_1305_, 2, v___x_1304_);
lean_ctor_set(v___x_1305_, 3, v___x_1303_);
lean_ctor_set(v___x_1305_, 4, v___x_1303_);
lean_ctor_set(v___x_1305_, 5, v___x_1303_);
lean_ctor_set(v___x_1305_, 6, v___x_1303_);
lean_ctor_set(v___x_1305_, 7, v___x_1303_);
lean_ctor_set(v___x_1305_, 8, v___x_1303_);
return v___x_1305_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3(void){
_start:
{
lean_object* v___x_1306_; double v___x_1307_; 
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_float_of_nat(v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* v_cls_1311_, lean_object* v_msg_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_options_1318_; lean_object* v_ref_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v_options_1318_ = lean_ctor_get(v___y_1315_, 2);
v_ref_1319_ = lean_ctor_get(v___y_1315_, 5);
v___x_1320_ = lean_st_ref_get(v___y_1316_);
v___x_1321_ = lean_st_ref_get(v___y_1314_);
v___x_1322_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1313_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1381_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1381_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1381_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v_env_1327_; lean_object* v_lctx_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1379_; 
v_env_1327_ = lean_ctor_get(v___x_1320_, 0);
lean_inc_ref(v_env_1327_);
lean_dec(v___x_1320_);
v_lctx_1328_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v___x_1321_, 1);
lean_dec(v_unused_1380_);
v___x_1330_ = v___x_1321_;
v_isShared_1331_ = v_isSharedCheck_1379_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_lctx_1328_);
lean_dec(v___x_1321_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1379_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_traceState_1334_; lean_object* v_env_1335_; lean_object* v_nextMacroScope_1336_; lean_object* v_ngen_1337_; lean_object* v_auxDeclNGen_1338_; lean_object* v_cache_1339_; lean_object* v_messages_1340_; lean_object* v_infoState_1341_; lean_object* v_snapshotTasks_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1378_; 
v___x_1332_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__2);
v___x_1333_ = lean_st_ref_take(v___y_1316_);
v_traceState_1334_ = lean_ctor_get(v___x_1333_, 4);
v_env_1335_ = lean_ctor_get(v___x_1333_, 0);
v_nextMacroScope_1336_ = lean_ctor_get(v___x_1333_, 1);
v_ngen_1337_ = lean_ctor_get(v___x_1333_, 2);
v_auxDeclNGen_1338_ = lean_ctor_get(v___x_1333_, 3);
v_cache_1339_ = lean_ctor_get(v___x_1333_, 5);
v_messages_1340_ = lean_ctor_get(v___x_1333_, 6);
v_infoState_1341_ = lean_ctor_get(v___x_1333_, 7);
v_snapshotTasks_1342_ = lean_ctor_get(v___x_1333_, 8);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1344_ = v___x_1333_;
v_isShared_1345_ = v_isSharedCheck_1378_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snapshotTasks_1342_);
lean_inc(v_infoState_1341_);
lean_inc(v_messages_1340_);
lean_inc(v_cache_1339_);
lean_inc(v_traceState_1334_);
lean_inc(v_auxDeclNGen_1338_);
lean_inc(v_ngen_1337_);
lean_inc(v_nextMacroScope_1336_);
lean_inc(v_env_1335_);
lean_dec(v___x_1333_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1378_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
uint64_t v_tid_1346_; lean_object* v_traces_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1377_; 
v_tid_1346_ = lean_ctor_get_uint64(v_traceState_1334_, sizeof(void*)*1);
v_traces_1347_ = lean_ctor_get(v_traceState_1334_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_traceState_1334_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1349_ = v_traceState_1334_;
v_isShared_1350_ = v_isSharedCheck_1377_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_traces_1347_);
lean_dec(v_traceState_1334_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1377_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1351_ = lean_unbox(v_a_1323_);
lean_dec(v_a_1323_);
v___x_1352_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1328_, v___x_1351_);
lean_dec_ref(v_lctx_1328_);
lean_inc_ref(v_options_1318_);
v___x_1353_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1353_, 0, v_env_1327_);
lean_ctor_set(v___x_1353_, 1, v___x_1332_);
lean_ctor_set(v___x_1353_, 2, v___x_1352_);
lean_ctor_set(v___x_1353_, 3, v_options_1318_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 3);
lean_ctor_set(v___x_1330_, 1, v_msg_1312_);
lean_ctor_set(v___x_1330_, 0, v___x_1353_);
v___x_1355_ = v___x_1330_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_msg_1312_);
v___x_1355_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; double v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__3);
v___x_1358_ = 0;
v___x_1359_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__4));
v___x_1360_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1360_, 0, v_cls_1311_);
lean_ctor_set(v___x_1360_, 1, v___x_1356_);
lean_ctor_set(v___x_1360_, 2, v___x_1359_);
lean_ctor_set_float(v___x_1360_, sizeof(void*)*3, v___x_1357_);
lean_ctor_set_float(v___x_1360_, sizeof(void*)*3 + 8, v___x_1357_);
lean_ctor_set_uint8(v___x_1360_, sizeof(void*)*3 + 16, v___x_1358_);
v___x_1361_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___closed__5));
v___x_1362_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1360_);
lean_ctor_set(v___x_1362_, 1, v___x_1355_);
lean_ctor_set(v___x_1362_, 2, v___x_1361_);
lean_inc(v_ref_1319_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_ref_1319_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l_Lean_PersistentArray_push___redArg(v_traces_1347_, v___x_1363_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1364_);
v___x_1366_ = v___x_1349_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1364_);
lean_ctor_set_uint64(v_reuseFailAlloc_1375_, sizeof(void*)*1, v_tid_1346_);
v___x_1366_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 4, v___x_1366_);
v___x_1368_ = v___x_1344_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_env_1335_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_nextMacroScope_1336_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_ngen_1337_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_auxDeclNGen_1338_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1374_, 5, v_cache_1339_);
lean_ctor_set(v_reuseFailAlloc_1374_, 6, v_messages_1340_);
lean_ctor_set(v_reuseFailAlloc_1374_, 7, v_infoState_1341_);
lean_ctor_set(v_reuseFailAlloc_1374_, 8, v_snapshotTasks_1342_);
v___x_1368_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1369_ = lean_st_ref_set(v___y_1316_, v___x_1368_);
v___x_1370_ = lean_box(0);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1370_);
v___x_1372_ = v___x_1325_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
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
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v___x_1321_);
lean_dec(v___x_1320_);
lean_dec_ref(v_msg_1312_);
lean_dec(v_cls_1311_);
v_a_1382_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1322_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1322_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object* v_cls_1390_, lean_object* v_msg_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_cls_1390_, v_msg_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object* v_m_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_buckets_1400_; lean_object* v___x_1401_; uint64_t v___x_1402_; uint64_t v___x_1403_; uint64_t v___x_1404_; uint64_t v_fold_1405_; uint64_t v___x_1406_; uint64_t v___x_1407_; uint64_t v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v_buckets_1400_ = lean_ctor_get(v_m_1398_, 1);
v___x_1401_ = lean_array_get_size(v_buckets_1400_);
v___x_1402_ = l_Lean_instHashableFVarId_hash(v_a_1399_);
v___x_1403_ = 32ULL;
v___x_1404_ = lean_uint64_shift_right(v___x_1402_, v___x_1403_);
v_fold_1405_ = lean_uint64_xor(v___x_1402_, v___x_1404_);
v___x_1406_ = 16ULL;
v___x_1407_ = lean_uint64_shift_right(v_fold_1405_, v___x_1406_);
v___x_1408_ = lean_uint64_xor(v_fold_1405_, v___x_1407_);
v___x_1409_ = lean_uint64_to_usize(v___x_1408_);
v___x_1410_ = lean_usize_of_nat(v___x_1401_);
v___x_1411_ = ((size_t)1ULL);
v___x_1412_ = lean_usize_sub(v___x_1410_, v___x_1411_);
v___x_1413_ = lean_usize_land(v___x_1409_, v___x_1412_);
v___x_1414_ = lean_array_uget_borrowed(v_buckets_1400_, v___x_1413_);
v___x_1415_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_1399_, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object* v_m_1416_, lean_object* v_a_1417_){
_start:
{
uint8_t v_res_1418_; lean_object* v_r_1419_; 
v_res_1418_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1416_, v_a_1417_);
lean_dec(v_a_1417_);
lean_dec_ref(v_m_1416_);
v_r_1419_ = lean_box(v_res_1418_);
return v_r_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(lean_object* v_a_1420_, lean_object* v_as_1421_, size_t v_i_1422_, size_t v_stop_1423_, lean_object* v_b_1424_){
_start:
{
lean_object* v___y_1426_; uint8_t v___x_1430_; 
v___x_1430_ = lean_usize_dec_eq(v_i_1422_, v_stop_1423_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v_fvarId_1432_; uint8_t v___x_1433_; 
v___x_1431_ = lean_array_uget_borrowed(v_as_1421_, v_i_1422_);
v_fvarId_1432_ = lean_ctor_get(v___x_1431_, 0);
v___x_1433_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1420_, v_fvarId_1432_);
if (v___x_1433_ == 0)
{
v___y_1426_ = v_b_1424_;
goto v___jp_1425_;
}
else
{
lean_object* v___x_1434_; 
lean_inc(v___x_1431_);
v___x_1434_ = lean_array_push(v_b_1424_, v___x_1431_);
v___y_1426_ = v___x_1434_;
goto v___jp_1425_;
}
}
else
{
return v_b_1424_;
}
v___jp_1425_:
{
size_t v___x_1427_; size_t v___x_1428_; 
v___x_1427_ = ((size_t)1ULL);
v___x_1428_ = lean_usize_add(v_i_1422_, v___x_1427_);
v_i_1422_ = v___x_1428_;
v_b_1424_ = v___y_1426_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7___boxed(lean_object* v_a_1435_, lean_object* v_as_1436_, lean_object* v_i_1437_, lean_object* v_stop_1438_, lean_object* v_b_1439_){
_start:
{
size_t v_i_boxed_1440_; size_t v_stop_boxed_1441_; lean_object* v_res_1442_; 
v_i_boxed_1440_ = lean_unbox_usize(v_i_1437_);
lean_dec(v_i_1437_);
v_stop_boxed_1441_ = lean_unbox_usize(v_stop_1438_);
lean_dec(v_stop_1438_);
v_res_1442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(v_a_1435_, v_as_1436_, v_i_boxed_1440_, v_stop_boxed_1441_, v_b_1439_);
lean_dec_ref(v_as_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* v_a_1443_, lean_object* v_as_1444_, size_t v_i_1445_, size_t v_stop_1446_, lean_object* v_b_1447_){
_start:
{
lean_object* v___y_1449_; uint8_t v___x_1453_; 
v___x_1453_ = lean_usize_dec_eq(v_i_1445_, v_stop_1446_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; lean_object* v_fvarId_1455_; uint8_t v___x_1456_; 
v___x_1454_ = lean_array_uget_borrowed(v_as_1444_, v_i_1445_);
v_fvarId_1455_ = lean_ctor_get(v___x_1454_, 0);
v___x_1456_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1443_, v_fvarId_1455_);
if (v___x_1456_ == 0)
{
v___y_1449_ = v_b_1447_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1457_; 
lean_inc(v___x_1454_);
v___x_1457_ = lean_array_push(v_b_1447_, v___x_1454_);
v___y_1449_ = v___x_1457_;
goto v___jp_1448_;
}
}
else
{
return v_b_1447_;
}
v___jp_1448_:
{
size_t v___x_1450_; size_t v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = ((size_t)1ULL);
v___x_1451_ = lean_usize_add(v_i_1445_, v___x_1450_);
v___x_1452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(v_a_1443_, v_as_1444_, v___x_1451_, v_stop_1446_, v___y_1449_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* v_a_1458_, lean_object* v_as_1459_, lean_object* v_i_1460_, lean_object* v_stop_1461_, lean_object* v_b_1462_){
_start:
{
size_t v_i_boxed_1463_; size_t v_stop_boxed_1464_; lean_object* v_res_1465_; 
v_i_boxed_1463_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_stop_boxed_1464_ = lean_unbox_usize(v_stop_1461_);
lean_dec(v_stop_1461_);
v_res_1465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1458_, v_as_1459_, v_i_boxed_1463_, v_stop_boxed_1464_, v_b_1462_);
lean_dec_ref(v_as_1459_);
lean_dec_ref(v_a_1458_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
if (lean_obj_tag(v_a_1466_) == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = l_List_reverse___redArg(v_a_1467_);
return v___x_1468_;
}
else
{
lean_object* v_head_1469_; lean_object* v_tail_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1479_; 
v_head_1469_ = lean_ctor_get(v_a_1466_, 0);
v_tail_1470_ = lean_ctor_get(v_a_1466_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_a_1466_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1472_ = v_a_1466_;
v_isShared_1473_ = v_isSharedCheck_1479_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_tail_1470_);
lean_inc(v_head_1469_);
lean_dec(v_a_1466_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1479_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = l_Lean_mkFVar(v_head_1469_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v_a_1467_);
lean_ctor_set(v___x_1472_, 0, v___x_1474_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_a_1467_);
v___x_1476_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
v_a_1466_ = v_tail_1470_;
v_a_1467_ = v___x_1476_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object* v_as_1480_, size_t v_sz_1481_, size_t v_i_1482_, lean_object* v_b_1483_){
_start:
{
lean_object* v_a_1486_; uint8_t v___x_1490_; 
v___x_1490_ = lean_usize_dec_lt(v_i_1482_, v_sz_1481_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_b_1483_);
return v___x_1491_;
}
else
{
lean_object* v_snd_1492_; lean_object* v_fst_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1528_; 
v_snd_1492_ = lean_ctor_get(v_b_1483_, 1);
v_fst_1493_ = lean_ctor_get(v_b_1483_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_b_1483_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1495_ = v_b_1483_;
v_isShared_1496_ = v_isSharedCheck_1528_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snd_1492_);
lean_inc(v_fst_1493_);
lean_dec(v_b_1483_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1528_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v_array_1497_; lean_object* v_start_1498_; lean_object* v_stop_1499_; uint8_t v___x_1500_; 
v_array_1497_ = lean_ctor_get(v_snd_1492_, 0);
v_start_1498_ = lean_ctor_get(v_snd_1492_, 1);
v_stop_1499_ = lean_ctor_get(v_snd_1492_, 2);
v___x_1500_ = lean_nat_dec_lt(v_start_1498_, v_stop_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1502_; 
if (v_isShared_1496_ == 0)
{
v___x_1502_ = v___x_1495_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_fst_1493_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_snd_1492_);
v___x_1502_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
}
else
{
lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1524_; 
lean_inc(v_stop_1499_);
lean_inc(v_start_1498_);
lean_inc_ref(v_array_1497_);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_snd_1492_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; lean_object* v_unused_1526_; lean_object* v_unused_1527_; 
v_unused_1525_ = lean_ctor_get(v_snd_1492_, 2);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_snd_1492_, 1);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v_snd_1492_, 0);
lean_dec(v_unused_1527_);
v___x_1506_ = v_snd_1492_;
v_isShared_1507_ = v_isSharedCheck_1524_;
goto v_resetjp_1505_;
}
else
{
lean_dec(v_snd_1492_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1524_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v_a_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v_a_1508_ = lean_array_uget_borrowed(v_as_1480_, v_i_1482_);
v___x_1509_ = lean_array_fget(v_array_1497_, v_start_1498_);
v___x_1510_ = lean_unsigned_to_nat(1u);
v___x_1511_ = lean_nat_add(v_start_1498_, v___x_1510_);
lean_dec(v_start_1498_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v___x_1511_);
v___x_1513_ = v___x_1506_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_array_1497_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_stop_1499_);
v___x_1513_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_unbox(v_a_1508_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1516_; 
lean_dec(v___x_1509_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1513_);
v___x_1516_ = v___x_1495_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_fst_1493_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1513_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
v_a_1486_ = v___x_1516_;
goto v___jp_1485_;
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1518_ = l_Lean_Compiler_LCNF_Param_toArg___redArg(v___x_1509_);
lean_dec(v___x_1509_);
v___x_1519_ = lean_array_push(v_fst_1493_, v___x_1518_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1513_);
lean_ctor_set(v___x_1495_, 0, v___x_1519_);
v___x_1521_ = v___x_1495_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v___x_1513_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
v_a_1486_ = v___x_1521_;
goto v___jp_1485_;
}
}
}
}
}
}
}
v___jp_1485_:
{
size_t v___x_1487_; size_t v___x_1488_; 
v___x_1487_ = ((size_t)1ULL);
v___x_1488_ = lean_usize_add(v_i_1482_, v___x_1487_);
v_i_1482_ = v___x_1488_;
v_b_1483_ = v_a_1486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object* v_as_1529_, lean_object* v_sz_1530_, lean_object* v_i_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_){
_start:
{
size_t v_sz_boxed_1534_; size_t v_i_boxed_1535_; lean_object* v_res_1536_; 
v_sz_boxed_1534_ = lean_unbox_usize(v_sz_1530_);
lean_dec(v_sz_1530_);
v_i_boxed_1535_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_res_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_1529_, v_sz_boxed_1534_, v_i_boxed_1535_, v_b_1532_);
lean_dec_ref(v_as_1529_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t v_sz_1537_, size_t v_i_1538_, lean_object* v_bs_1539_, uint8_t v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_usize_dec_lt(v_i_1538_, v_sz_1537_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v_bs_1539_);
return v___x_1548_;
}
else
{
uint8_t v___x_1549_; lean_object* v_v_1550_; lean_object* v___x_1551_; 
v___x_1549_ = 0;
v_v_1550_ = lean_array_uget_borrowed(v_bs_1539_, v_i_1538_);
lean_inc(v___y_1545_);
lean_inc_ref(v___y_1544_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc(v_v_1550_);
v___x_1551_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_1549_, v_v_1550_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; lean_object* v_bs_x27_1554_; size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
v___x_1553_ = lean_unsigned_to_nat(0u);
v_bs_x27_1554_ = lean_array_uset(v_bs_1539_, v_i_1538_, v___x_1553_);
v___x_1555_ = ((size_t)1ULL);
v___x_1556_ = lean_usize_add(v_i_1538_, v___x_1555_);
v___x_1557_ = lean_array_uset(v_bs_x27_1554_, v_i_1538_, v_a_1552_);
v_i_1538_ = v___x_1556_;
v_bs_1539_ = v___x_1557_;
goto _start;
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v_bs_1539_);
v_a_1559_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1551_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1551_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* v_sz_1567_, lean_object* v_i_1568_, lean_object* v_bs_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
size_t v_sz_boxed_1577_; size_t v_i_boxed_1578_; uint8_t v___y_12313__boxed_1579_; lean_object* v_res_1580_; 
v_sz_boxed_1577_ = lean_unbox_usize(v_sz_1567_);
lean_dec(v_sz_1567_);
v_i_boxed_1578_ = lean_unbox_usize(v_i_1568_);
lean_dec(v_i_1568_);
v___y_12313__boxed_1579_ = lean_unbox(v___y_1570_);
v_res_1580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_boxed_1577_, v_i_boxed_1578_, v_bs_1569_, v___y_12313__boxed_1579_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object* v_x_1581_, lean_object* v_x_1582_){
_start:
{
if (lean_obj_tag(v_x_1582_) == 0)
{
lean_inc(v_x_1581_);
return v_x_1581_;
}
else
{
lean_object* v_key_1583_; lean_object* v_tail_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_key_1583_ = lean_ctor_get(v_x_1582_, 0);
v_tail_1584_ = lean_ctor_get(v_x_1582_, 2);
v___x_1585_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_x_1581_, v_tail_1584_);
lean_inc(v_key_1583_);
v___x_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_key_1583_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_x_1587_, v_x_1588_);
lean_dec(v_x_1588_);
lean_dec(v_x_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12(lean_object* v_as_1590_, size_t v_i_1591_, size_t v_stop_1592_, lean_object* v_b_1593_){
_start:
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_usize_dec_eq(v_i_1591_, v_stop_1592_);
if (v___x_1594_ == 0)
{
size_t v___x_1595_; size_t v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1595_ = ((size_t)1ULL);
v___x_1596_ = lean_usize_sub(v_i_1591_, v___x_1595_);
v___x_1597_ = lean_array_uget_borrowed(v_as_1590_, v___x_1596_);
v___x_1598_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_b_1593_, v___x_1597_);
lean_dec(v_b_1593_);
v_i_1591_ = v___x_1596_;
v_b_1593_ = v___x_1598_;
goto _start;
}
else
{
return v_b_1593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12___boxed(lean_object* v_as_1600_, lean_object* v_i_1601_, lean_object* v_stop_1602_, lean_object* v_b_1603_){
_start:
{
size_t v_i_boxed_1604_; size_t v_stop_boxed_1605_; lean_object* v_res_1606_; 
v_i_boxed_1604_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_stop_boxed_1605_ = lean_unbox_usize(v_stop_1602_);
lean_dec(v_stop_1602_);
v_res_1606_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12(v_as_1600_, v_i_boxed_1604_, v_stop_boxed_1605_, v_b_1603_);
lean_dec_ref(v_as_1600_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
if (lean_obj_tag(v_a_1607_) == 0)
{
lean_object* v___x_1609_; 
v___x_1609_ = l_List_reverse___redArg(v_a_1608_);
return v___x_1609_;
}
else
{
lean_object* v_head_1610_; lean_object* v_tail_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1620_; 
v_head_1610_ = lean_ctor_get(v_a_1607_, 0);
v_tail_1611_ = lean_ctor_get(v_a_1607_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_a_1607_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1613_ = v_a_1607_;
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_tail_1611_);
lean_inc(v_head_1610_);
lean_dec(v_a_1607_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = l_Lean_MessageData_ofExpr(v_head_1610_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 1, v_a_1608_);
lean_ctor_set(v___x_1613_, 0, v___x_1615_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_a_1608_);
v___x_1617_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
v_a_1607_ = v_tail_1611_;
v_a_1608_ = v___x_1617_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object* v_a_1621_, size_t v_sz_1622_, size_t v_i_1623_, lean_object* v_bs_1624_){
_start:
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_usize_dec_lt(v_i_1623_, v_sz_1622_);
if (v___x_1625_ == 0)
{
return v_bs_1624_;
}
else
{
lean_object* v_v_1626_; lean_object* v_fvarId_1627_; lean_object* v___x_1628_; lean_object* v_bs_x27_1629_; uint8_t v___x_1630_; size_t v___x_1631_; size_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_v_1626_ = lean_array_uget_borrowed(v_bs_1624_, v_i_1623_);
v_fvarId_1627_ = lean_ctor_get(v_v_1626_, 0);
lean_inc(v_fvarId_1627_);
v___x_1628_ = lean_unsigned_to_nat(0u);
v_bs_x27_1629_ = lean_array_uset(v_bs_1624_, v_i_1623_, v___x_1628_);
v___x_1630_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1621_, v_fvarId_1627_);
lean_dec(v_fvarId_1627_);
v___x_1631_ = ((size_t)1ULL);
v___x_1632_ = lean_usize_add(v_i_1623_, v___x_1631_);
v___x_1633_ = lean_box(v___x_1630_);
v___x_1634_ = lean_array_uset(v_bs_x27_1629_, v_i_1623_, v___x_1633_);
v_i_1623_ = v___x_1632_;
v_bs_1624_ = v___x_1634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object* v_a_1636_, lean_object* v_sz_1637_, lean_object* v_i_1638_, lean_object* v_bs_1639_){
_start:
{
size_t v_sz_boxed_1640_; size_t v_i_boxed_1641_; lean_object* v_res_1642_; 
v_sz_boxed_1640_ = lean_unbox_usize(v_sz_1637_);
lean_dec(v_sz_1637_);
v_i_boxed_1641_ = lean_unbox_usize(v_i_1638_);
lean_dec(v_i_1638_);
v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1636_, v_sz_boxed_1640_, v_i_boxed_1641_, v_bs_1639_);
lean_dec_ref(v_a_1636_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* v_a_1643_, size_t v_sz_1644_, size_t v_i_1645_, lean_object* v_bs_1646_){
_start:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_usize_dec_lt(v_i_1645_, v_sz_1644_);
if (v___x_1647_ == 0)
{
return v_bs_1646_;
}
else
{
lean_object* v_v_1648_; lean_object* v_fvarId_1649_; lean_object* v___x_1650_; lean_object* v_bs_x27_1651_; uint8_t v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_v_1648_ = lean_array_uget_borrowed(v_bs_1646_, v_i_1645_);
v_fvarId_1649_ = lean_ctor_get(v_v_1648_, 0);
lean_inc(v_fvarId_1649_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v_bs_x27_1651_ = lean_array_uset(v_bs_1646_, v_i_1645_, v___x_1650_);
v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1643_, v_fvarId_1649_);
lean_dec(v_fvarId_1649_);
v___x_1653_ = ((size_t)1ULL);
v___x_1654_ = lean_usize_add(v_i_1645_, v___x_1653_);
v___x_1655_ = lean_box(v___x_1652_);
v___x_1656_ = lean_array_uset(v_bs_x27_1651_, v_i_1645_, v___x_1655_);
v___x_1657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1643_, v_sz_1644_, v___x_1654_, v___x_1656_);
return v___x_1657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object* v_a_1658_, lean_object* v_sz_1659_, lean_object* v_i_1660_, lean_object* v_bs_1661_){
_start:
{
size_t v_sz_boxed_1662_; size_t v_i_boxed_1663_; lean_object* v_res_1664_; 
v_sz_boxed_1662_ = lean_unbox_usize(v_sz_1659_);
lean_dec(v_sz_1659_);
v_i_boxed_1663_ = lean_unbox_usize(v_i_1660_);
lean_dec(v_i_1660_);
v_res_1664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1658_, v_sz_boxed_1662_, v_i_boxed_1663_, v_bs_1661_);
lean_dec_ref(v_a_1658_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object* v_a_1665_, lean_object* v_as_1666_, size_t v_i_1667_, size_t v_stop_1668_, lean_object* v_b_1669_){
_start:
{
lean_object* v___y_1671_; uint8_t v___x_1675_; 
v___x_1675_ = lean_usize_dec_eq(v_i_1667_, v_stop_1668_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v_fvarId_1677_; uint8_t v___x_1678_; 
v___x_1676_ = lean_array_uget_borrowed(v_as_1666_, v_i_1667_);
v_fvarId_1677_ = lean_ctor_get(v___x_1676_, 0);
v___x_1678_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1665_, v_fvarId_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_inc(v___x_1676_);
v___x_1679_ = lean_array_push(v_b_1669_, v___x_1676_);
v___y_1671_ = v___x_1679_;
goto v___jp_1670_;
}
else
{
v___y_1671_ = v_b_1669_;
goto v___jp_1670_;
}
}
else
{
return v_b_1669_;
}
v___jp_1670_:
{
size_t v___x_1672_; size_t v___x_1673_; 
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_add(v_i_1667_, v___x_1672_);
v_i_1667_ = v___x_1673_;
v_b_1669_ = v___y_1671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object* v_a_1680_, lean_object* v_as_1681_, lean_object* v_i_1682_, lean_object* v_stop_1683_, lean_object* v_b_1684_){
_start:
{
size_t v_i_boxed_1685_; size_t v_stop_boxed_1686_; lean_object* v_res_1687_; 
v_i_boxed_1685_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v_stop_boxed_1686_ = lean_unbox_usize(v_stop_1683_);
lean_dec(v_stop_1683_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1680_, v_as_1681_, v_i_boxed_1685_, v_stop_boxed_1686_, v_b_1684_);
lean_dec_ref(v_as_1681_);
lean_dec_ref(v_a_1680_);
return v_res_1687_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_box(0);
v___x_1689_ = lean_unsigned_to_nat(16u);
v___x_1690_ = lean_mk_array(v___x_1689_, v___x_1688_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* v_decl_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_value_1717_; 
v_value_1717_ = lean_ctor_get(v_decl_1711_, 1);
lean_inc_ref(v_value_1717_);
if (lean_obj_tag(v_value_1717_) == 0)
{
lean_object* v_toSignature_1718_; uint8_t v_recursive_1719_; lean_object* v_inlineAttr_x3f_1720_; lean_object* v_code_1721_; lean_object* v___x_1722_; 
v_toSignature_1718_ = lean_ctor_get(v_decl_1711_, 0);
lean_inc_ref(v_toSignature_1718_);
v_recursive_1719_ = lean_ctor_get_uint8(v_decl_1711_, sizeof(void*)*3);
v_inlineAttr_x3f_1720_ = lean_ctor_get(v_decl_1711_, 2);
v_code_1721_ = lean_ctor_get(v_value_1717_, 0);
lean_inc_ref(v_code_1721_);
lean_inc(v_a_1715_);
lean_inc_ref(v_a_1714_);
lean_inc(v_a_1713_);
lean_inc_ref(v_a_1712_);
lean_inc_ref(v_decl_1711_);
v___x_1722_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1970_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1970_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1970_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_size_1727_; lean_object* v_buckets_1728_; lean_object* v_name_1729_; lean_object* v_levelParams_1730_; lean_object* v_type_1731_; lean_object* v_params_1732_; uint8_t v_safe_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1969_; 
v_size_1727_ = lean_ctor_get(v_a_1723_, 0);
v_buckets_1728_ = lean_ctor_get(v_a_1723_, 1);
v_name_1729_ = lean_ctor_get(v_toSignature_1718_, 0);
v_levelParams_1730_ = lean_ctor_get(v_toSignature_1718_, 1);
v_type_1731_ = lean_ctor_get(v_toSignature_1718_, 2);
v_params_1732_ = lean_ctor_get(v_toSignature_1718_, 3);
v_safe_1733_ = lean_ctor_get_uint8(v_toSignature_1718_, sizeof(void*)*4);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_toSignature_1718_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1735_ = v_toSignature_1718_;
v_isShared_1736_ = v_isSharedCheck_1969_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_params_1732_);
lean_inc(v_type_1731_);
lean_inc(v_levelParams_1730_);
lean_inc(v_name_1729_);
lean_dec(v_toSignature_1718_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1969_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; uint8_t v___y_1741_; lean_object* v___y_1742_; size_t v___y_1743_; size_t v___y_1744_; uint8_t v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___x_1883_; uint8_t v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; size_t v___y_1890_; size_t v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; uint8_t v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; uint8_t v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; uint8_t v___y_1945_; uint8_t v___x_1966_; 
v___x_1883_ = lean_array_get_size(v_params_1732_);
v___x_1966_ = lean_nat_dec_eq(v_size_1727_, v___x_1883_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = lean_nat_dec_eq(v_size_1727_, v___x_1967_);
v___y_1945_ = v___x_1968_;
goto v___jp_1944_;
}
else
{
v___y_1945_ = v___x_1966_;
goto v___jp_1944_;
}
v___jp_1737_:
{
lean_object* v___x_1753_; 
lean_inc(v___y_1746_);
lean_inc_ref(v___y_1738_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1739_);
v___x_1753_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v___y_1747_, v_value_1717_, v___y_1749_, v___y_1739_, v___y_1750_, v___y_1738_, v___y_1746_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1755_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
lean_inc(v___y_1746_);
lean_inc_ref(v___y_1738_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1739_);
v___x_1755_ = l_Lean_Compiler_LCNF_Code_inferType(v___y_1741_, v_code_1721_, v___y_1739_, v___y_1750_, v___y_1738_, v___y_1746_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
lean_inc(v___y_1746_);
lean_inc_ref(v___y_1738_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1739_);
lean_inc_ref(v___y_1740_);
v___x_1757_ = l_Lean_Compiler_LCNF_mkForallParams(v___y_1741_, v___y_1740_, v_a_1756_, v___y_1739_, v___y_1750_, v___y_1738_, v___y_1746_);
lean_dec(v_a_1756_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = lean_box(0);
lean_inc(v___y_1748_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 3, v___y_1740_);
lean_ctor_set(v___x_1735_, 2, v_a_1758_);
lean_ctor_set(v___x_1735_, 1, v___x_1759_);
lean_ctor_set(v___x_1735_, 0, v___y_1748_);
v___x_1761_ = v___x_1735_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___y_1748_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_a_1758_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v___y_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*4, v_safe_1733_);
v___x_1761_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
lean_ctor_set(v___x_1762_, 1, v_a_1754_);
lean_ctor_set(v___x_1762_, 2, v_inlineAttr_x3f_1720_);
lean_ctor_set_uint8(v___x_1762_, sizeof(void*)*3, v_recursive_1719_);
lean_inc_ref(v___x_1762_);
v___x_1763_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1762_, v___y_1746_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec_ref(v___x_1763_);
v___x_1764_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0);
lean_inc(v___y_1751_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___y_1751_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_st_mk_ref(v___x_1765_);
lean_inc(v___y_1746_);
lean_inc_ref(v___y_1738_);
lean_inc(v___y_1750_);
lean_inc_ref(v___y_1739_);
lean_inc(v___x_1766_);
v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v___y_1743_, v___y_1744_, v_params_1732_, v___y_1745_, v___x_1766_, v___y_1739_, v___y_1750_, v___y_1738_, v___y_1746_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; size_t v_sz_1773_; lean_object* v___x_1774_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1767_);
v___x_1769_ = lean_mk_empty_array_with_capacity(v___y_1751_);
v___x_1770_ = lean_array_get_size(v_a_1768_);
lean_inc(v_a_1768_);
v___x_1771_ = l_Array_toSubarray___redArg(v_a_1768_, v___y_1751_, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1769_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v_sz_1773_ = lean_array_size(v___y_1742_);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v___y_1742_, v_sz_1773_, v___y_1744_, v___x_1772_);
lean_dec_ref(v___y_1742_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v_fst_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1832_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
v_fst_1776_ = lean_ctor_get(v_a_1775_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; 
v_unused_1833_ = lean_ctor_get(v_a_1775_, 1);
lean_dec(v_unused_1833_);
v___x_1778_ = v_a_1775_;
v_isShared_1779_ = v_isSharedCheck_1832_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_fst_1776_);
lean_dec(v_a_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1832_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1780_, 0, v___y_1748_);
lean_ctor_set(v___x_1780_, 1, v___x_1759_);
lean_ctor_set(v___x_1780_, 2, v_fst_1776_);
v___x_1781_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
lean_inc(v___y_1746_);
lean_inc(v___y_1750_);
v___x_1782_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___y_1741_, v___x_1780_, v___x_1781_, v___y_1739_, v___y_1750_, v___y_1738_, v___y_1746_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v_fvarId_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
v_fvarId_1784_ = lean_ctor_get(v_a_1783_, 0);
lean_inc(v_fvarId_1784_);
v___x_1785_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_fvarId_1784_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 1, v___x_1785_);
lean_ctor_set(v___x_1778_, 0, v_a_1783_);
v___x_1787_ = v___x_1778_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1783_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1789_, 0, v_name_1729_);
lean_ctor_set(v___x_1789_, 1, v_levelParams_1730_);
lean_ctor_set(v___x_1789_, 2, v_type_1731_);
lean_ctor_set(v___x_1789_, 3, v_a_1768_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*4, v_safe_1733_);
v___x_1790_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3));
v___x_1791_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1788_);
lean_ctor_set(v___x_1791_, 2, v___x_1790_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3, v___y_1745_);
lean_inc_ref(v___x_1791_);
v___x_1792_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1791_, v___y_1746_);
lean_dec(v___y_1746_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_dec_ref(v___x_1792_);
v___x_1793_ = lean_st_ref_get(v___x_1766_);
lean_dec(v___x_1766_);
lean_dec(v___x_1793_);
v___x_1794_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___y_1741_, v___y_1752_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1752_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1805_; 
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; 
v_unused_1806_ = lean_ctor_get(v___x_1794_, 0);
lean_dec(v_unused_1806_);
v___x_1796_ = v___x_1794_;
v_isShared_1797_ = v_isSharedCheck_1805_;
goto v_resetjp_1795_;
}
else
{
lean_dec(v___x_1794_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1805_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1798_ = lean_unsigned_to_nat(2u);
v___x_1799_ = lean_mk_empty_array_with_capacity(v___x_1798_);
v___x_1800_ = lean_array_push(v___x_1799_, v___x_1762_);
v___x_1801_ = lean_array_push(v___x_1800_, v___x_1791_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1801_);
v___x_1803_ = v___x_1796_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec_ref(v___x_1791_);
lean_dec_ref(v___x_1762_);
v_a_1807_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1794_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1794_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec_ref(v___x_1791_);
lean_dec(v___x_1766_);
lean_dec_ref(v___x_1762_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1750_);
v_a_1815_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1792_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1792_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_del_object(v___x_1778_);
lean_dec(v_a_1768_);
lean_dec(v___x_1766_);
lean_dec_ref(v___x_1762_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1750_);
lean_dec(v___y_1746_);
lean_dec_ref(v_type_1731_);
lean_dec(v_levelParams_1730_);
lean_dec(v_name_1729_);
v_a_1824_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1782_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1782_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec(v_a_1768_);
lean_dec(v___x_1766_);
lean_dec_ref(v___x_1762_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1750_);
lean_dec(v___y_1748_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v_type_1731_);
lean_dec(v_levelParams_1730_);
lean_dec(v_name_1729_);
v_a_1834_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1774_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1774_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec(v___x_1766_);
lean_dec_ref(v___x_1762_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec(v___y_1748_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v_type_1731_);
lean_dec(v_levelParams_1730_);
lean_dec(v_name_1729_);
v_a_1842_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1767_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1767_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v___x_1762_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec(v___y_1748_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v_params_1732_);
lean_dec_ref(v_type_1731_);
lean_dec(v_levelParams_1730_);
lean_dec(v_name_1729_);
v_a_1850_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1763_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1763_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1754_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec(v___y_1748_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_del_object(v___x_1735_);
lean_dec_ref(v_params_1732_);
lean_dec_ref(v_type_1731_);
lean_dec(v_levelParams_1730_);
lean_dec(v_name_1729_);
lean_dec(v_inlineAttr_x3f_1720_);
v_a_1859_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1757_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1757_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_a_1754_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec(v___y_1748_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_del_object(v___x_1735_);
lean_dec_ref(v_params_1732_);
lean_dec_ref(v_type_1731_);
lean_dec(v_levelParams_1730_);
lean_dec(v_name_1729_);
lean_dec(v_inlineAttr_x3f_1720_);
v_a_1867_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1755_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1755_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec(v___y_1748_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_del_object(v___x_1735_);
lean_dec_ref(v_params_1732_);
lean_dec_ref(v_type_1731_);
lean_dec(v_levelParams_1730_);
lean_dec(v_name_1729_);
lean_dec_ref(v_code_1721_);
lean_dec(v_inlineAttr_x3f_1720_);
v_a_1875_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1753_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1753_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
v___jp_1884_:
{
uint8_t v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1896_ = 0;
v___x_1897_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4));
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1889_);
lean_inc(v_name_1729_);
v___x_1898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1898_, 0, v_name_1729_);
lean_ctor_set(v___x_1898_, 1, v___y_1889_);
lean_ctor_set(v___x_1898_, 2, v___y_1892_);
v___x_1899_ = lean_mk_empty_array_with_capacity(v___y_1894_);
v___x_1900_ = lean_nat_dec_lt(v___y_1894_, v___x_1883_);
if (v___x_1900_ == 0)
{
lean_dec(v_a_1723_);
v___y_1738_ = v___y_1886_;
v___y_1739_ = v___y_1887_;
v___y_1740_ = v___y_1895_;
v___y_1741_ = v___x_1896_;
v___y_1742_ = v___y_1892_;
v___y_1743_ = v___y_1891_;
v___y_1744_ = v___y_1890_;
v___y_1745_ = v___y_1885_;
v___y_1746_ = v___y_1888_;
v___y_1747_ = v___x_1897_;
v___y_1748_ = v___y_1889_;
v___y_1749_ = v___x_1898_;
v___y_1750_ = v___y_1893_;
v___y_1751_ = v___y_1894_;
v___y_1752_ = v___x_1899_;
goto v___jp_1737_;
}
else
{
uint8_t v___x_1901_; 
v___x_1901_ = lean_nat_dec_le(v___x_1883_, v___x_1883_);
if (v___x_1901_ == 0)
{
if (v___x_1900_ == 0)
{
lean_dec(v_a_1723_);
v___y_1738_ = v___y_1886_;
v___y_1739_ = v___y_1887_;
v___y_1740_ = v___y_1895_;
v___y_1741_ = v___x_1896_;
v___y_1742_ = v___y_1892_;
v___y_1743_ = v___y_1891_;
v___y_1744_ = v___y_1890_;
v___y_1745_ = v___y_1885_;
v___y_1746_ = v___y_1888_;
v___y_1747_ = v___x_1897_;
v___y_1748_ = v___y_1889_;
v___y_1749_ = v___x_1898_;
v___y_1750_ = v___y_1893_;
v___y_1751_ = v___y_1894_;
v___y_1752_ = v___x_1899_;
goto v___jp_1737_;
}
else
{
size_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_usize_of_nat(v___x_1883_);
v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1723_, v_params_1732_, v___y_1890_, v___x_1902_, v___x_1899_);
lean_dec(v_a_1723_);
v___y_1738_ = v___y_1886_;
v___y_1739_ = v___y_1887_;
v___y_1740_ = v___y_1895_;
v___y_1741_ = v___x_1896_;
v___y_1742_ = v___y_1892_;
v___y_1743_ = v___y_1891_;
v___y_1744_ = v___y_1890_;
v___y_1745_ = v___y_1885_;
v___y_1746_ = v___y_1888_;
v___y_1747_ = v___x_1897_;
v___y_1748_ = v___y_1889_;
v___y_1749_ = v___x_1898_;
v___y_1750_ = v___y_1893_;
v___y_1751_ = v___y_1894_;
v___y_1752_ = v___x_1903_;
goto v___jp_1737_;
}
}
else
{
size_t v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_usize_of_nat(v___x_1883_);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1723_, v_params_1732_, v___y_1890_, v___x_1904_, v___x_1899_);
lean_dec(v_a_1723_);
v___y_1738_ = v___y_1886_;
v___y_1739_ = v___y_1887_;
v___y_1740_ = v___y_1895_;
v___y_1741_ = v___x_1896_;
v___y_1742_ = v___y_1892_;
v___y_1743_ = v___y_1891_;
v___y_1744_ = v___y_1890_;
v___y_1745_ = v___y_1885_;
v___y_1746_ = v___y_1888_;
v___y_1747_ = v___x_1897_;
v___y_1748_ = v___y_1889_;
v___y_1749_ = v___x_1898_;
v___y_1750_ = v___y_1893_;
v___y_1751_ = v___y_1894_;
v___y_1752_ = v___x_1905_;
goto v___jp_1737_;
}
}
}
v___jp_1906_:
{
size_t v_sz_1912_; size_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v_sz_1912_ = lean_array_size(v_params_1732_);
v___x_1913_ = ((size_t)0ULL);
lean_inc_ref(v_params_1732_);
v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1723_, v_sz_1912_, v___x_1913_, v_params_1732_);
v___x_1915_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6));
lean_inc(v_name_1729_);
v___x_1916_ = l_Lean_Name_append(v_name_1729_, v___x_1915_);
v___x_1917_ = lean_unsigned_to_nat(0u);
v___x_1918_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7));
v___x_1919_ = lean_nat_dec_lt(v___x_1917_, v___x_1883_);
if (v___x_1919_ == 0)
{
v___y_1885_ = v___y_1907_;
v___y_1886_ = v___y_1910_;
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1911_;
v___y_1889_ = v___x_1916_;
v___y_1890_ = v___x_1913_;
v___y_1891_ = v_sz_1912_;
v___y_1892_ = v___x_1914_;
v___y_1893_ = v___y_1909_;
v___y_1894_ = v___x_1917_;
v___y_1895_ = v___x_1918_;
goto v___jp_1884_;
}
else
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_nat_dec_le(v___x_1883_, v___x_1883_);
if (v___x_1920_ == 0)
{
if (v___x_1919_ == 0)
{
v___y_1885_ = v___y_1907_;
v___y_1886_ = v___y_1910_;
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1911_;
v___y_1889_ = v___x_1916_;
v___y_1890_ = v___x_1913_;
v___y_1891_ = v_sz_1912_;
v___y_1892_ = v___x_1914_;
v___y_1893_ = v___y_1909_;
v___y_1894_ = v___x_1917_;
v___y_1895_ = v___x_1918_;
goto v___jp_1884_;
}
else
{
size_t v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_usize_of_nat(v___x_1883_);
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1723_, v_params_1732_, v___x_1913_, v___x_1921_, v___x_1918_);
v___y_1885_ = v___y_1907_;
v___y_1886_ = v___y_1910_;
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1911_;
v___y_1889_ = v___x_1916_;
v___y_1890_ = v___x_1913_;
v___y_1891_ = v_sz_1912_;
v___y_1892_ = v___x_1914_;
v___y_1893_ = v___y_1909_;
v___y_1894_ = v___x_1917_;
v___y_1895_ = v___x_1922_;
goto v___jp_1884_;
}
}
else
{
size_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_usize_of_nat(v___x_1883_);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1723_, v_params_1732_, v___x_1913_, v___x_1923_, v___x_1918_);
v___y_1885_ = v___y_1907_;
v___y_1886_ = v___y_1910_;
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1911_;
v___y_1889_ = v___x_1916_;
v___y_1890_ = v___x_1913_;
v___y_1891_ = v_sz_1912_;
v___y_1892_ = v___x_1914_;
v___y_1893_ = v___y_1909_;
v___y_1894_ = v___x_1917_;
v___y_1895_ = v___x_1924_;
goto v___jp_1884_;
}
}
}
v___jp_1925_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1930_ = lean_box(0);
v___x_1931_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(v___y_1929_, v___x_1930_);
v___x_1932_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v___x_1931_, v___x_1930_);
v___x_1933_ = l_Lean_MessageData_ofList(v___x_1932_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___y_1928_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v___y_1927_, v___x_1934_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_dec_ref(v___x_1935_);
v___y_1907_ = v___y_1926_;
v___y_1908_ = v_a_1712_;
v___y_1909_ = v_a_1713_;
v___y_1910_ = v_a_1714_;
v___y_1911_ = v_a_1715_;
goto v___jp_1906_;
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_del_object(v___x_1735_);
lean_dec_ref(v_params_1732_);
lean_dec_ref(v_type_1731_);
lean_dec(v_levelParams_1730_);
lean_dec(v_name_1729_);
lean_dec(v_a_1723_);
lean_dec_ref(v_code_1721_);
lean_dec(v_inlineAttr_x3f_1720_);
lean_dec_ref(v_value_1717_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
v___jp_1944_:
{
if (v___y_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_a_1948_; uint8_t v___x_1949_; 
lean_inc(v_inlineAttr_x3f_1720_);
lean_del_object(v___x_1725_);
lean_dec_ref(v_decl_1711_);
v___x_1946_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10));
v___x_1947_ = l_Lean_isTracingEnabledFor___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7___redArg(v___x_1946_, v_a_1714_);
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v___x_1949_ = lean_unbox(v_a_1948_);
lean_dec(v_a_1948_);
if (v___x_1949_ == 0)
{
v___y_1907_ = v___y_1945_;
v___y_1908_ = v_a_1712_;
v___y_1909_ = v_a_1713_;
v___y_1910_ = v_a_1714_;
v___y_1911_ = v_a_1715_;
goto v___jp_1906_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
lean_inc(v_name_1729_);
v___x_1950_ = l_Lean_MessageData_ofName(v_name_1729_);
v___x_1951_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12);
v___x_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_box(0);
v___x_1954_ = lean_array_get_size(v_buckets_1728_);
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = lean_nat_dec_lt(v___x_1955_, v___x_1954_);
if (v___x_1956_ == 0)
{
v___y_1926_ = v___y_1945_;
v___y_1927_ = v___x_1946_;
v___y_1928_ = v___x_1952_;
v___y_1929_ = v___x_1953_;
goto v___jp_1925_;
}
else
{
size_t v___x_1957_; size_t v___x_1958_; lean_object* v___x_1959_; 
v___x_1957_ = lean_usize_of_nat(v___x_1954_);
v___x_1958_ = ((size_t)0ULL);
v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__12(v_buckets_1728_, v___x_1957_, v___x_1958_, v___x_1953_);
v___y_1926_ = v___y_1945_;
v___y_1927_ = v___x_1946_;
v___y_1928_ = v___x_1952_;
v___y_1929_ = v___x_1959_;
goto v___jp_1925_;
}
}
}
else
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_del_object(v___x_1735_);
lean_dec_ref(v_params_1732_);
lean_dec_ref(v_type_1731_);
lean_dec(v_levelParams_1730_);
lean_dec(v_name_1729_);
lean_dec(v_a_1723_);
lean_dec_ref(v_code_1721_);
lean_dec_ref(v_value_1717_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
v___x_1960_ = lean_unsigned_to_nat(1u);
v___x_1961_ = lean_mk_empty_array_with_capacity(v___x_1960_);
v___x_1962_ = lean_array_push(v___x_1961_, v_decl_1711_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1962_);
v___x_1964_ = v___x_1725_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec_ref(v_code_1721_);
lean_dec_ref(v_toSignature_1718_);
lean_dec_ref(v_value_1717_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec_ref(v_decl_1711_);
v_a_1971_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1722_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1722_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_value_1717_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v_value_1717_, 0);
lean_dec(v_unused_1989_);
v___x_1980_ = v_value_1717_;
v_isShared_1981_ = v_isSharedCheck_1988_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v_value_1717_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1988_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_mk_empty_array_with_capacity(v___x_1982_);
v___x_1984_ = lean_array_push(v___x_1983_, v_decl_1711_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set_tag(v___x_1980_, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1984_);
v___x_1986_ = v___x_1980_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object* v_decl_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v_decl_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* v_00_u03b2_1997_, lean_object* v_m_1998_, lean_object* v_a_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1998_, v_a_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* v_00_u03b2_2001_, lean_object* v_m_2002_, lean_object* v_a_2003_){
_start:
{
uint8_t v_res_2004_; lean_object* v_r_2005_; 
v_res_2004_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(v_00_u03b2_2001_, v_m_2002_, v_a_2003_);
lean_dec(v_a_2003_);
lean_dec_ref(v_m_2002_);
v_r_2005_ = lean_box(v_res_2004_);
return v_r_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* v_as_2006_, size_t v_sz_2007_, size_t v_i_2008_, lean_object* v_b_2009_, uint8_t v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_2006_, v_sz_2007_, v_i_2008_, v_b_2009_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* v_as_2018_, lean_object* v_sz_2019_, lean_object* v_i_2020_, lean_object* v_b_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
size_t v_sz_boxed_2029_; size_t v_i_boxed_2030_; uint8_t v___y_13091__boxed_2031_; lean_object* v_res_2032_; 
v_sz_boxed_2029_ = lean_unbox_usize(v_sz_2019_);
lean_dec(v_sz_2019_);
v_i_boxed_2030_ = lean_unbox_usize(v_i_2020_);
lean_dec(v_i_2020_);
v___y_13091__boxed_2031_ = lean_unbox(v___y_2022_);
v_res_2032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_2018_, v_sz_boxed_2029_, v_i_boxed_2030_, v_b_2021_, v___y_13091__boxed_2031_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v_as_2018_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* v_as_2033_, size_t v_i_2034_, size_t v_stop_2035_, lean_object* v_b_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_a_2043_; uint8_t v___x_2047_; 
v___x_2047_ = lean_usize_dec_eq(v_i_2034_, v_stop_2035_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_array_uget_borrowed(v_as_2033_, v_i_2034_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v___y_2038_);
lean_inc_ref(v___y_2037_);
lean_inc(v___x_2048_);
v___x_2049_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v___x_2048_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = l_Array_append___redArg(v_b_2036_, v_a_2050_);
lean_dec(v_a_2050_);
v_a_2043_ = v___x_2051_;
goto v___jp_2042_;
}
else
{
lean_dec_ref(v_b_2036_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2052_; 
v_a_2052_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2049_);
v_a_2043_ = v_a_2052_;
goto v___jp_2042_;
}
else
{
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
return v___x_2049_;
}
}
}
else
{
lean_object* v___x_2053_; 
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v_b_2036_);
return v___x_2053_;
}
v___jp_2042_:
{
size_t v___x_2044_; size_t v___x_2045_; 
v___x_2044_ = ((size_t)1ULL);
v___x_2045_ = lean_usize_add(v_i_2034_, v___x_2044_);
v_i_2034_ = v___x_2045_;
v_b_2036_ = v_a_2043_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* v_as_2054_, lean_object* v_i_2055_, lean_object* v_stop_2056_, lean_object* v_b_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
size_t v_i_boxed_2063_; size_t v_stop_boxed_2064_; lean_object* v_res_2065_; 
v_i_boxed_2063_ = lean_unbox_usize(v_i_2055_);
lean_dec(v_i_2055_);
v_stop_boxed_2064_ = lean_unbox_usize(v_stop_2056_);
lean_dec(v_stop_2056_);
v_res_2065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_2054_, v_i_boxed_2063_, v_stop_boxed_2064_, v_b_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec_ref(v_as_2054_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* v___x_2066_, lean_object* v_decls_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2073_ = lean_mk_empty_array_with_capacity(v___x_2066_);
v___x_2074_ = lean_array_get_size(v_decls_2067_);
v___x_2075_ = lean_nat_dec_lt(v___x_2066_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; 
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2073_);
return v___x_2076_;
}
else
{
uint8_t v___x_2077_; 
v___x_2077_ = lean_nat_dec_le(v___x_2074_, v___x_2074_);
if (v___x_2077_ == 0)
{
if (v___x_2075_ == 0)
{
lean_object* v___x_2078_; 
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2073_);
return v___x_2078_;
}
else
{
size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = ((size_t)0ULL);
v___x_2080_ = lean_usize_of_nat(v___x_2074_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2067_, v___x_2079_, v___x_2080_, v___x_2073_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
return v___x_2081_;
}
}
else
{
size_t v___x_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = lean_usize_of_nat(v___x_2074_);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2067_, v___x_2082_, v___x_2083_, v___x_2073_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
return v___x_2084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* v___x_2085_, lean_object* v_decls_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(v___x_2085_, v_decls_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec_ref(v_decls_2086_);
lean_dec(v___x_2085_);
return v_res_2092_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_unsigned_to_nat(2803462840u);
v___x_2156_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2157_ = l_Lean_Name_num___override(v___x_2156_, v___x_2155_);
return v___x_2157_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2160_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2161_ = l_Lean_Name_str___override(v___x_2160_, v___x_2159_);
return v___x_2161_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2164_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2165_ = l_Lean_Name_str___override(v___x_2164_, v___x_2163_);
return v___x_2165_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_unsigned_to_nat(2u);
v___x_2167_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2168_ = l_Lean_Name_num___override(v___x_2167_, v___x_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10));
v___x_2171_ = 1;
v___x_2172_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2173_ = l_Lean_registerTraceClass(v___x_2170_, v___x_2171_, v___x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object* v_a_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
return v_res_2175_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
