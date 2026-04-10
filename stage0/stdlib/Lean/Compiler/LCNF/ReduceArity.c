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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
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
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2;
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3;
static const lean_string_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ", used params: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15;
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
return v___x_424_;
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_args_382_);
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
lean_dec_ref(v_a_463_);
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
return v___x_641_;
}
case 6:
{
lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_649_; 
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
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_b_656_);
return v___x_676_;
}
v___jp_664_:
{
lean_object* v___x_666_; 
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
lean_dec_ref(v___y_681_);
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
lean_dec_ref(v_a_692_);
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
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc(v___y_705_);
lean_inc_ref(v___y_704_);
lean_inc(v___y_703_);
lean_inc_ref(v___y_702_);
v___x_710_ = lean_apply_8(v_f_700_, v_code_709_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, lean_box(0));
return v___x_710_;
}
else
{
lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_718_; 
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
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
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
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
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
v___x_788_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v___x_786_, v_value_779_, v___x_787_, v___x_785_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec_ref(v___x_787_);
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
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
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
v___x_827_ = lean_panic_fn_borrowed(v___x_826_, v_msg_825_);
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
v___x_860_ = lean_unsigned_to_nat(640u);
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
lean_ctor_set(v___x_877_, 0, v___y_874_);
lean_ctor_set(v___x_877_, 1, v___y_875_);
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
lean_ctor_set(v___x_884_, 0, v___y_881_);
lean_ctor_set(v___x_884_, 1, v___y_882_);
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
v___y_874_ = v_a_902_;
v___y_875_ = v_a_904_;
v___y_876_ = v___x_909_;
goto v___jp_873_;
}
else
{
size_t v___x_910_; size_t v___x_911_; uint8_t v___x_912_; 
v___x_910_ = lean_ptr_addr(v_decl_905_);
v___x_911_ = lean_ptr_addr(v_a_902_);
v___x_912_ = lean_usize_dec_eq(v___x_910_, v___x_911_);
v___y_874_ = v_a_902_;
v___y_875_ = v_a_904_;
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
v___y_881_ = v_a_902_;
v___y_882_ = v_a_913_;
v___y_883_ = v___x_918_;
goto v___jp_880_;
}
else
{
size_t v___x_919_; size_t v___x_920_; uint8_t v___x_921_; 
v___x_919_ = lean_ptr_addr(v_decl_914_);
v___x_920_ = lean_ptr_addr(v_a_902_);
v___x_921_ = lean_usize_dec_eq(v___x_919_, v___x_920_);
v___y_881_ = v_a_902_;
v___y_882_ = v_a_913_;
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
lean_inc(v___y_1208_);
lean_inc_ref(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1205_);
lean_inc_ref(v___y_1204_);
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
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec_ref(v___y_1238_);
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
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1265_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1266_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
lean_ctor_set(v___x_1271_, 2, v___x_1270_);
lean_ctor_set(v___x_1271_, 3, v___x_1270_);
lean_ctor_set(v___x_1271_, 4, v___x_1269_);
lean_ctor_set(v___x_1271_, 5, v___x_1269_);
lean_ctor_set(v___x_1271_, 6, v___x_1269_);
lean_ctor_set(v___x_1271_, 7, v___x_1269_);
lean_ctor_set(v___x_1271_, 8, v___x_1269_);
lean_ctor_set(v___x_1271_, 9, v___x_1269_);
return v___x_1271_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3(void){
_start:
{
lean_object* v___x_1272_; double v___x_1273_; 
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = lean_float_of_nat(v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* v_cls_1277_, lean_object* v_msg_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_options_1284_; lean_object* v_ref_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_options_1284_ = lean_ctor_get(v___y_1281_, 2);
v_ref_1285_ = lean_ctor_get(v___y_1281_, 5);
v___x_1286_ = lean_st_ref_get(v___y_1282_);
v___x_1287_ = lean_st_ref_get(v___y_1280_);
v___x_1288_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1279_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1347_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1347_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1347_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_env_1293_; lean_object* v_lctx_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1345_; 
v_env_1293_ = lean_ctor_get(v___x_1286_, 0);
lean_inc_ref(v_env_1293_);
lean_dec(v___x_1286_);
v_lctx_1294_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v___x_1287_, 1);
lean_dec(v_unused_1346_);
v___x_1296_ = v___x_1287_;
v_isShared_1297_ = v_isSharedCheck_1345_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_lctx_1294_);
lean_dec(v___x_1287_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1345_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_traceState_1300_; lean_object* v_env_1301_; lean_object* v_nextMacroScope_1302_; lean_object* v_ngen_1303_; lean_object* v_auxDeclNGen_1304_; lean_object* v_cache_1305_; lean_object* v_messages_1306_; lean_object* v_infoState_1307_; lean_object* v_snapshotTasks_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1344_; 
v___x_1298_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2);
v___x_1299_ = lean_st_ref_take(v___y_1282_);
v_traceState_1300_ = lean_ctor_get(v___x_1299_, 4);
v_env_1301_ = lean_ctor_get(v___x_1299_, 0);
v_nextMacroScope_1302_ = lean_ctor_get(v___x_1299_, 1);
v_ngen_1303_ = lean_ctor_get(v___x_1299_, 2);
v_auxDeclNGen_1304_ = lean_ctor_get(v___x_1299_, 3);
v_cache_1305_ = lean_ctor_get(v___x_1299_, 5);
v_messages_1306_ = lean_ctor_get(v___x_1299_, 6);
v_infoState_1307_ = lean_ctor_get(v___x_1299_, 7);
v_snapshotTasks_1308_ = lean_ctor_get(v___x_1299_, 8);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1310_ = v___x_1299_;
v_isShared_1311_ = v_isSharedCheck_1344_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_snapshotTasks_1308_);
lean_inc(v_infoState_1307_);
lean_inc(v_messages_1306_);
lean_inc(v_cache_1305_);
lean_inc(v_traceState_1300_);
lean_inc(v_auxDeclNGen_1304_);
lean_inc(v_ngen_1303_);
lean_inc(v_nextMacroScope_1302_);
lean_inc(v_env_1301_);
lean_dec(v___x_1299_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1344_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
uint64_t v_tid_1312_; lean_object* v_traces_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1343_; 
v_tid_1312_ = lean_ctor_get_uint64(v_traceState_1300_, sizeof(void*)*1);
v_traces_1313_ = lean_ctor_get(v_traceState_1300_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_traceState_1300_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1315_ = v_traceState_1300_;
v_isShared_1316_ = v_isSharedCheck_1343_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_traces_1313_);
lean_dec(v_traceState_1300_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1343_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1317_ = lean_unbox(v_a_1289_);
lean_dec(v_a_1289_);
v___x_1318_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1294_, v___x_1317_);
lean_dec_ref(v_lctx_1294_);
lean_inc_ref(v_options_1284_);
v___x_1319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1319_, 0, v_env_1293_);
lean_ctor_set(v___x_1319_, 1, v___x_1298_);
lean_ctor_set(v___x_1319_, 2, v___x_1318_);
lean_ctor_set(v___x_1319_, 3, v_options_1284_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 3);
lean_ctor_set(v___x_1296_, 1, v_msg_1278_);
lean_ctor_set(v___x_1296_, 0, v___x_1319_);
v___x_1321_ = v___x_1296_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_msg_1278_);
v___x_1321_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; double v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3);
v___x_1324_ = 0;
v___x_1325_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4));
v___x_1326_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1326_, 0, v_cls_1277_);
lean_ctor_set(v___x_1326_, 1, v___x_1322_);
lean_ctor_set(v___x_1326_, 2, v___x_1325_);
lean_ctor_set_float(v___x_1326_, sizeof(void*)*3, v___x_1323_);
lean_ctor_set_float(v___x_1326_, sizeof(void*)*3 + 8, v___x_1323_);
lean_ctor_set_uint8(v___x_1326_, sizeof(void*)*3 + 16, v___x_1324_);
v___x_1327_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5));
v___x_1328_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1321_);
lean_ctor_set(v___x_1328_, 2, v___x_1327_);
lean_inc(v_ref_1285_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_ref_1285_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = l_Lean_PersistentArray_push___redArg(v_traces_1313_, v___x_1329_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1330_);
v___x_1332_ = v___x_1315_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1330_);
lean_ctor_set_uint64(v_reuseFailAlloc_1341_, sizeof(void*)*1, v_tid_1312_);
v___x_1332_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1334_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 4, v___x_1332_);
v___x_1334_ = v___x_1310_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_env_1301_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_nextMacroScope_1302_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_ngen_1303_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_auxDeclNGen_1304_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1340_, 5, v_cache_1305_);
lean_ctor_set(v_reuseFailAlloc_1340_, 6, v_messages_1306_);
lean_ctor_set(v_reuseFailAlloc_1340_, 7, v_infoState_1307_);
lean_ctor_set(v_reuseFailAlloc_1340_, 8, v_snapshotTasks_1308_);
v___x_1334_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1335_ = lean_st_ref_set(v___y_1282_, v___x_1334_);
v___x_1336_ = lean_box(0);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1336_);
v___x_1338_ = v___x_1291_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
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
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v___x_1287_);
lean_dec(v___x_1286_);
lean_dec_ref(v_msg_1278_);
lean_dec(v_cls_1277_);
v_a_1348_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1288_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1288_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___boxed(lean_object* v_cls_1356_, lean_object* v_msg_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v_cls_1356_, v_msg_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
if (lean_obj_tag(v_x_1365_) == 0)
{
lean_inc(v_x_1364_);
return v_x_1364_;
}
else
{
lean_object* v_key_1366_; lean_object* v_tail_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_key_1366_ = lean_ctor_get(v_x_1365_, 0);
v_tail_1367_ = lean_ctor_get(v_x_1365_, 2);
v___x_1368_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1364_, v_tail_1367_);
lean_inc(v_key_1366_);
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_key_1366_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object* v_x_1370_, lean_object* v_x_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1370_, v_x_1371_);
lean_dec(v_x_1371_);
lean_dec(v_x_1370_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object* v_as_1373_, size_t v_i_1374_, size_t v_stop_1375_, lean_object* v_b_1376_){
_start:
{
uint8_t v___x_1377_; 
v___x_1377_ = lean_usize_dec_eq(v_i_1374_, v_stop_1375_);
if (v___x_1377_ == 0)
{
size_t v___x_1378_; size_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1378_ = ((size_t)1ULL);
v___x_1379_ = lean_usize_sub(v_i_1374_, v___x_1378_);
v___x_1380_ = lean_array_uget_borrowed(v_as_1373_, v___x_1379_);
v___x_1381_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_b_1376_, v___x_1380_);
lean_dec(v_b_1376_);
v_i_1374_ = v___x_1379_;
v_b_1376_ = v___x_1381_;
goto _start;
}
else
{
return v_b_1376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object* v_as_1383_, lean_object* v_i_1384_, lean_object* v_stop_1385_, lean_object* v_b_1386_){
_start:
{
size_t v_i_boxed_1387_; size_t v_stop_boxed_1388_; lean_object* v_res_1389_; 
v_i_boxed_1387_ = lean_unbox_usize(v_i_1384_);
lean_dec(v_i_1384_);
v_stop_boxed_1388_ = lean_unbox_usize(v_stop_1385_);
lean_dec(v_stop_1385_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_as_1383_, v_i_boxed_1387_, v_stop_boxed_1388_, v_b_1386_);
lean_dec_ref(v_as_1383_);
return v_res_1389_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object* v_m_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_buckets_1392_; lean_object* v___x_1393_; uint64_t v___x_1394_; uint64_t v___x_1395_; uint64_t v___x_1396_; uint64_t v_fold_1397_; uint64_t v___x_1398_; uint64_t v___x_1399_; uint64_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v_buckets_1392_ = lean_ctor_get(v_m_1390_, 1);
v___x_1393_ = lean_array_get_size(v_buckets_1392_);
v___x_1394_ = l_Lean_instHashableFVarId_hash(v_a_1391_);
v___x_1395_ = 32ULL;
v___x_1396_ = lean_uint64_shift_right(v___x_1394_, v___x_1395_);
v_fold_1397_ = lean_uint64_xor(v___x_1394_, v___x_1396_);
v___x_1398_ = 16ULL;
v___x_1399_ = lean_uint64_shift_right(v_fold_1397_, v___x_1398_);
v___x_1400_ = lean_uint64_xor(v_fold_1397_, v___x_1399_);
v___x_1401_ = lean_uint64_to_usize(v___x_1400_);
v___x_1402_ = lean_usize_of_nat(v___x_1393_);
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_sub(v___x_1402_, v___x_1403_);
v___x_1405_ = lean_usize_land(v___x_1401_, v___x_1404_);
v___x_1406_ = lean_array_uget_borrowed(v_buckets_1392_, v___x_1405_);
v___x_1407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_1391_, v___x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object* v_m_1408_, lean_object* v_a_1409_){
_start:
{
uint8_t v_res_1410_; lean_object* v_r_1411_; 
v_res_1410_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec_ref(v_m_1408_);
v_r_1411_ = lean_box(v_res_1410_);
return v_r_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(lean_object* v_a_1412_, lean_object* v_as_1413_, size_t v_i_1414_, size_t v_stop_1415_, lean_object* v_b_1416_){
_start:
{
lean_object* v___y_1418_; uint8_t v___x_1422_; 
v___x_1422_ = lean_usize_dec_eq(v_i_1414_, v_stop_1415_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v_fvarId_1424_; uint8_t v___x_1425_; 
v___x_1423_ = lean_array_uget_borrowed(v_as_1413_, v_i_1414_);
v_fvarId_1424_ = lean_ctor_get(v___x_1423_, 0);
v___x_1425_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1412_, v_fvarId_1424_);
if (v___x_1425_ == 0)
{
v___y_1418_ = v_b_1416_;
goto v___jp_1417_;
}
else
{
lean_object* v___x_1426_; 
lean_inc(v___x_1423_);
v___x_1426_ = lean_array_push(v_b_1416_, v___x_1423_);
v___y_1418_ = v___x_1426_;
goto v___jp_1417_;
}
}
else
{
return v_b_1416_;
}
v___jp_1417_:
{
size_t v___x_1419_; size_t v___x_1420_; 
v___x_1419_ = ((size_t)1ULL);
v___x_1420_ = lean_usize_add(v_i_1414_, v___x_1419_);
v_i_1414_ = v___x_1420_;
v_b_1416_ = v___y_1418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7___boxed(lean_object* v_a_1427_, lean_object* v_as_1428_, lean_object* v_i_1429_, lean_object* v_stop_1430_, lean_object* v_b_1431_){
_start:
{
size_t v_i_boxed_1432_; size_t v_stop_boxed_1433_; lean_object* v_res_1434_; 
v_i_boxed_1432_ = lean_unbox_usize(v_i_1429_);
lean_dec(v_i_1429_);
v_stop_boxed_1433_ = lean_unbox_usize(v_stop_1430_);
lean_dec(v_stop_1430_);
v_res_1434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(v_a_1427_, v_as_1428_, v_i_boxed_1432_, v_stop_boxed_1433_, v_b_1431_);
lean_dec_ref(v_as_1428_);
lean_dec_ref(v_a_1427_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* v_a_1435_, lean_object* v_as_1436_, size_t v_i_1437_, size_t v_stop_1438_, lean_object* v_b_1439_){
_start:
{
lean_object* v___y_1441_; uint8_t v___x_1445_; 
v___x_1445_ = lean_usize_dec_eq(v_i_1437_, v_stop_1438_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v_fvarId_1447_; uint8_t v___x_1448_; 
v___x_1446_ = lean_array_uget_borrowed(v_as_1436_, v_i_1437_);
v_fvarId_1447_ = lean_ctor_get(v___x_1446_, 0);
v___x_1448_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1435_, v_fvarId_1447_);
if (v___x_1448_ == 0)
{
v___y_1441_ = v_b_1439_;
goto v___jp_1440_;
}
else
{
lean_object* v___x_1449_; 
lean_inc(v___x_1446_);
v___x_1449_ = lean_array_push(v_b_1439_, v___x_1446_);
v___y_1441_ = v___x_1449_;
goto v___jp_1440_;
}
}
else
{
return v_b_1439_;
}
v___jp_1440_:
{
size_t v___x_1442_; size_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = ((size_t)1ULL);
v___x_1443_ = lean_usize_add(v_i_1437_, v___x_1442_);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(v_a_1435_, v_as_1436_, v___x_1443_, v_stop_1438_, v___y_1441_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* v_a_1450_, lean_object* v_as_1451_, lean_object* v_i_1452_, lean_object* v_stop_1453_, lean_object* v_b_1454_){
_start:
{
size_t v_i_boxed_1455_; size_t v_stop_boxed_1456_; lean_object* v_res_1457_; 
v_i_boxed_1455_ = lean_unbox_usize(v_i_1452_);
lean_dec(v_i_1452_);
v_stop_boxed_1456_ = lean_unbox_usize(v_stop_1453_);
lean_dec(v_stop_1453_);
v_res_1457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1450_, v_as_1451_, v_i_boxed_1455_, v_stop_boxed_1456_, v_b_1454_);
lean_dec_ref(v_as_1451_);
lean_dec_ref(v_a_1450_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
if (lean_obj_tag(v_a_1458_) == 0)
{
lean_object* v___x_1460_; 
v___x_1460_ = l_List_reverse___redArg(v_a_1459_);
return v___x_1460_;
}
else
{
lean_object* v_head_1461_; lean_object* v_tail_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1471_; 
v_head_1461_ = lean_ctor_get(v_a_1458_, 0);
v_tail_1462_ = lean_ctor_get(v_a_1458_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_a_1458_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1464_ = v_a_1458_;
v_isShared_1465_ = v_isSharedCheck_1471_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_tail_1462_);
lean_inc(v_head_1461_);
lean_dec(v_a_1458_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1471_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = l_Lean_MessageData_ofExpr(v_head_1461_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 1, v_a_1459_);
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_a_1459_);
v___x_1468_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
v_a_1458_ = v_tail_1462_;
v_a_1459_ = v___x_1468_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object* v_as_1472_, size_t v_sz_1473_, size_t v_i_1474_, lean_object* v_b_1475_){
_start:
{
lean_object* v_a_1478_; uint8_t v___x_1482_; 
v___x_1482_ = lean_usize_dec_lt(v_i_1474_, v_sz_1473_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v_b_1475_);
return v___x_1483_;
}
else
{
lean_object* v_snd_1484_; lean_object* v_fst_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1520_; 
v_snd_1484_ = lean_ctor_get(v_b_1475_, 1);
v_fst_1485_ = lean_ctor_get(v_b_1475_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_b_1475_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1487_ = v_b_1475_;
v_isShared_1488_ = v_isSharedCheck_1520_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_snd_1484_);
lean_inc(v_fst_1485_);
lean_dec(v_b_1475_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1520_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_array_1489_; lean_object* v_start_1490_; lean_object* v_stop_1491_; uint8_t v___x_1492_; 
v_array_1489_ = lean_ctor_get(v_snd_1484_, 0);
v_start_1490_ = lean_ctor_get(v_snd_1484_, 1);
v_stop_1491_ = lean_ctor_get(v_snd_1484_, 2);
v___x_1492_ = lean_nat_dec_lt(v_start_1490_, v_stop_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1494_; 
if (v_isShared_1488_ == 0)
{
v___x_1494_ = v___x_1487_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_fst_1485_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_snd_1484_);
v___x_1494_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
return v___x_1495_;
}
}
else
{
lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1516_; 
lean_inc(v_stop_1491_);
lean_inc(v_start_1490_);
lean_inc_ref(v_array_1489_);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_snd_1484_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; 
v_unused_1517_ = lean_ctor_get(v_snd_1484_, 2);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_snd_1484_, 1);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_snd_1484_, 0);
lean_dec(v_unused_1519_);
v___x_1498_ = v_snd_1484_;
v_isShared_1499_ = v_isSharedCheck_1516_;
goto v_resetjp_1497_;
}
else
{
lean_dec(v_snd_1484_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1516_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_a_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v_a_1500_ = lean_array_uget_borrowed(v_as_1472_, v_i_1474_);
v___x_1501_ = lean_array_fget(v_array_1489_, v_start_1490_);
v___x_1502_ = lean_unsigned_to_nat(1u);
v___x_1503_ = lean_nat_add(v_start_1490_, v___x_1502_);
lean_dec(v_start_1490_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v___x_1503_);
v___x_1505_ = v___x_1498_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_array_1489_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_stop_1491_);
v___x_1505_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_unbox(v_a_1500_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1508_; 
lean_dec(v___x_1501_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1505_);
v___x_1508_ = v___x_1487_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_fst_1485_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1505_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
v_a_1478_ = v___x_1508_;
goto v___jp_1477_;
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1510_ = l_Lean_Compiler_LCNF_Param_toArg___redArg(v___x_1501_);
lean_dec(v___x_1501_);
v___x_1511_ = lean_array_push(v_fst_1485_, v___x_1510_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1505_);
lean_ctor_set(v___x_1487_, 0, v___x_1511_);
v___x_1513_ = v___x_1487_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1505_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
v_a_1478_ = v___x_1513_;
goto v___jp_1477_;
}
}
}
}
}
}
}
v___jp_1477_:
{
size_t v___x_1479_; size_t v___x_1480_; 
v___x_1479_ = ((size_t)1ULL);
v___x_1480_ = lean_usize_add(v_i_1474_, v___x_1479_);
v_i_1474_ = v___x_1480_;
v_b_1475_ = v_a_1478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object* v_as_1521_, lean_object* v_sz_1522_, lean_object* v_i_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_){
_start:
{
size_t v_sz_boxed_1526_; size_t v_i_boxed_1527_; lean_object* v_res_1528_; 
v_sz_boxed_1526_ = lean_unbox_usize(v_sz_1522_);
lean_dec(v_sz_1522_);
v_i_boxed_1527_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_res_1528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_1521_, v_sz_boxed_1526_, v_i_boxed_1527_, v_b_1524_);
lean_dec_ref(v_as_1521_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t v_sz_1529_, size_t v_i_1530_, lean_object* v_bs_1531_, uint8_t v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v___x_1539_; 
v___x_1539_ = lean_usize_dec_lt(v_i_1530_, v_sz_1529_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_bs_1531_);
return v___x_1540_;
}
else
{
uint8_t v___x_1541_; lean_object* v_v_1542_; lean_object* v___x_1543_; 
v___x_1541_ = 0;
v_v_1542_ = lean_array_uget_borrowed(v_bs_1531_, v_i_1530_);
lean_inc(v_v_1542_);
v___x_1543_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_1541_, v_v_1542_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; lean_object* v_bs_x27_1546_; size_t v___x_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1543_);
v___x_1545_ = lean_unsigned_to_nat(0u);
v_bs_x27_1546_ = lean_array_uset(v_bs_1531_, v_i_1530_, v___x_1545_);
v___x_1547_ = ((size_t)1ULL);
v___x_1548_ = lean_usize_add(v_i_1530_, v___x_1547_);
v___x_1549_ = lean_array_uset(v_bs_x27_1546_, v_i_1530_, v_a_1544_);
v_i_1530_ = v___x_1548_;
v_bs_1531_ = v___x_1549_;
goto _start;
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v_bs_1531_);
v_a_1551_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1543_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1543_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* v_sz_1559_, lean_object* v_i_1560_, lean_object* v_bs_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
size_t v_sz_boxed_1569_; size_t v_i_boxed_1570_; uint8_t v___y_12531__boxed_1571_; lean_object* v_res_1572_; 
v_sz_boxed_1569_ = lean_unbox_usize(v_sz_1559_);
lean_dec(v_sz_1559_);
v_i_boxed_1570_ = lean_unbox_usize(v_i_1560_);
lean_dec(v_i_1560_);
v___y_12531__boxed_1571_ = lean_unbox(v___y_1562_);
v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_boxed_1569_, v_i_boxed_1570_, v_bs_1561_, v___y_12531__boxed_1571_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
if (lean_obj_tag(v_a_1573_) == 0)
{
lean_object* v___x_1575_; 
v___x_1575_ = l_List_reverse___redArg(v_a_1574_);
return v___x_1575_;
}
else
{
lean_object* v_head_1576_; lean_object* v_tail_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1586_; 
v_head_1576_ = lean_ctor_get(v_a_1573_, 0);
v_tail_1577_ = lean_ctor_get(v_a_1573_, 1);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_a_1573_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1579_ = v_a_1573_;
v_isShared_1580_ = v_isSharedCheck_1586_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_tail_1577_);
lean_inc(v_head_1576_);
lean_dec(v_a_1573_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1586_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = l_Lean_mkFVar(v_head_1576_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v_a_1574_);
lean_ctor_set(v___x_1579_, 0, v___x_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_a_1574_);
v___x_1583_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
v_a_1573_ = v_tail_1577_;
v_a_1574_ = v___x_1583_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object* v_a_1587_, size_t v_sz_1588_, size_t v_i_1589_, lean_object* v_bs_1590_){
_start:
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_usize_dec_lt(v_i_1589_, v_sz_1588_);
if (v___x_1591_ == 0)
{
return v_bs_1590_;
}
else
{
lean_object* v_v_1592_; lean_object* v_fvarId_1593_; lean_object* v___x_1594_; lean_object* v_bs_x27_1595_; uint8_t v___x_1596_; size_t v___x_1597_; size_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_v_1592_ = lean_array_uget_borrowed(v_bs_1590_, v_i_1589_);
v_fvarId_1593_ = lean_ctor_get(v_v_1592_, 0);
lean_inc(v_fvarId_1593_);
v___x_1594_ = lean_unsigned_to_nat(0u);
v_bs_x27_1595_ = lean_array_uset(v_bs_1590_, v_i_1589_, v___x_1594_);
v___x_1596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1587_, v_fvarId_1593_);
lean_dec(v_fvarId_1593_);
v___x_1597_ = ((size_t)1ULL);
v___x_1598_ = lean_usize_add(v_i_1589_, v___x_1597_);
v___x_1599_ = lean_box(v___x_1596_);
v___x_1600_ = lean_array_uset(v_bs_x27_1595_, v_i_1589_, v___x_1599_);
v_i_1589_ = v___x_1598_;
v_bs_1590_ = v___x_1600_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object* v_a_1602_, lean_object* v_sz_1603_, lean_object* v_i_1604_, lean_object* v_bs_1605_){
_start:
{
size_t v_sz_boxed_1606_; size_t v_i_boxed_1607_; lean_object* v_res_1608_; 
v_sz_boxed_1606_ = lean_unbox_usize(v_sz_1603_);
lean_dec(v_sz_1603_);
v_i_boxed_1607_ = lean_unbox_usize(v_i_1604_);
lean_dec(v_i_1604_);
v_res_1608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1602_, v_sz_boxed_1606_, v_i_boxed_1607_, v_bs_1605_);
lean_dec_ref(v_a_1602_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* v_a_1609_, size_t v_sz_1610_, size_t v_i_1611_, lean_object* v_bs_1612_){
_start:
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_usize_dec_lt(v_i_1611_, v_sz_1610_);
if (v___x_1613_ == 0)
{
return v_bs_1612_;
}
else
{
lean_object* v_v_1614_; lean_object* v_fvarId_1615_; lean_object* v___x_1616_; lean_object* v_bs_x27_1617_; uint8_t v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_v_1614_ = lean_array_uget_borrowed(v_bs_1612_, v_i_1611_);
v_fvarId_1615_ = lean_ctor_get(v_v_1614_, 0);
lean_inc(v_fvarId_1615_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v_bs_x27_1617_ = lean_array_uset(v_bs_1612_, v_i_1611_, v___x_1616_);
v___x_1618_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1609_, v_fvarId_1615_);
lean_dec(v_fvarId_1615_);
v___x_1619_ = ((size_t)1ULL);
v___x_1620_ = lean_usize_add(v_i_1611_, v___x_1619_);
v___x_1621_ = lean_box(v___x_1618_);
v___x_1622_ = lean_array_uset(v_bs_x27_1617_, v_i_1611_, v___x_1621_);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1609_, v_sz_1610_, v___x_1620_, v___x_1622_);
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object* v_a_1624_, lean_object* v_sz_1625_, lean_object* v_i_1626_, lean_object* v_bs_1627_){
_start:
{
size_t v_sz_boxed_1628_; size_t v_i_boxed_1629_; lean_object* v_res_1630_; 
v_sz_boxed_1628_ = lean_unbox_usize(v_sz_1625_);
lean_dec(v_sz_1625_);
v_i_boxed_1629_ = lean_unbox_usize(v_i_1626_);
lean_dec(v_i_1626_);
v_res_1630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1624_, v_sz_boxed_1628_, v_i_boxed_1629_, v_bs_1627_);
lean_dec_ref(v_a_1624_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object* v_a_1631_, lean_object* v_as_1632_, size_t v_i_1633_, size_t v_stop_1634_, lean_object* v_b_1635_){
_start:
{
lean_object* v___y_1637_; uint8_t v___x_1641_; 
v___x_1641_ = lean_usize_dec_eq(v_i_1633_, v_stop_1634_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v_fvarId_1643_; uint8_t v___x_1644_; 
v___x_1642_ = lean_array_uget_borrowed(v_as_1632_, v_i_1633_);
v_fvarId_1643_ = lean_ctor_get(v___x_1642_, 0);
v___x_1644_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1631_, v_fvarId_1643_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; 
lean_inc(v___x_1642_);
v___x_1645_ = lean_array_push(v_b_1635_, v___x_1642_);
v___y_1637_ = v___x_1645_;
goto v___jp_1636_;
}
else
{
v___y_1637_ = v_b_1635_;
goto v___jp_1636_;
}
}
else
{
return v_b_1635_;
}
v___jp_1636_:
{
size_t v___x_1638_; size_t v___x_1639_; 
v___x_1638_ = ((size_t)1ULL);
v___x_1639_ = lean_usize_add(v_i_1633_, v___x_1638_);
v_i_1633_ = v___x_1639_;
v_b_1635_ = v___y_1637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object* v_a_1646_, lean_object* v_as_1647_, lean_object* v_i_1648_, lean_object* v_stop_1649_, lean_object* v_b_1650_){
_start:
{
size_t v_i_boxed_1651_; size_t v_stop_boxed_1652_; lean_object* v_res_1653_; 
v_i_boxed_1651_ = lean_unbox_usize(v_i_1648_);
lean_dec(v_i_1648_);
v_stop_boxed_1652_ = lean_unbox_usize(v_stop_1649_);
lean_dec(v_stop_1649_);
v_res_1653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1646_, v_as_1647_, v_i_boxed_1651_, v_stop_boxed_1652_, v_b_1650_);
lean_dec_ref(v_as_1647_);
lean_dec_ref(v_a_1646_);
return v_res_1653_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_box(0);
v___x_1655_ = lean_unsigned_to_nat(16u);
v___x_1656_ = lean_mk_array(v___x_1655_, v___x_1654_);
return v___x_1656_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10));
v___x_1678_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_1679_ = l_Lean_Name_append(v___x_1678_, v___x_1677_);
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14));
v___x_1682_ = l_Lean_stringToMessageData(v___x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* v_decl_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_value_1689_; 
v_value_1689_ = lean_ctor_get(v_decl_1683_, 1);
lean_inc_ref(v_value_1689_);
if (lean_obj_tag(v_value_1689_) == 0)
{
lean_object* v_toSignature_1690_; uint8_t v_recursive_1691_; lean_object* v_inlineAttr_x3f_1692_; lean_object* v_code_1693_; lean_object* v___x_1694_; 
v_toSignature_1690_ = lean_ctor_get(v_decl_1683_, 0);
lean_inc_ref(v_toSignature_1690_);
v_recursive_1691_ = lean_ctor_get_uint8(v_decl_1683_, sizeof(void*)*3);
v_inlineAttr_x3f_1692_ = lean_ctor_get(v_decl_1683_, 2);
v_code_1693_ = lean_ctor_get(v_value_1689_, 0);
lean_inc_ref(v_code_1693_);
lean_inc_ref(v_decl_1683_);
v___x_1694_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1944_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1944_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1944_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v_size_1699_; lean_object* v_buckets_1700_; lean_object* v_name_1701_; lean_object* v_levelParams_1702_; lean_object* v_type_1703_; lean_object* v_params_1704_; uint8_t v_safe_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1943_; 
v_size_1699_ = lean_ctor_get(v_a_1695_, 0);
v_buckets_1700_ = lean_ctor_get(v_a_1695_, 1);
v_name_1701_ = lean_ctor_get(v_toSignature_1690_, 0);
v_levelParams_1702_ = lean_ctor_get(v_toSignature_1690_, 1);
v_type_1703_ = lean_ctor_get(v_toSignature_1690_, 2);
v_params_1704_ = lean_ctor_get(v_toSignature_1690_, 3);
v_safe_1705_ = lean_ctor_get_uint8(v_toSignature_1690_, sizeof(void*)*4);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_toSignature_1690_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1707_ = v_toSignature_1690_;
v_isShared_1708_ = v_isSharedCheck_1943_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_params_1704_);
lean_inc(v_type_1703_);
lean_inc(v_levelParams_1702_);
lean_inc(v_name_1701_);
lean_dec(v_toSignature_1690_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1943_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; size_t v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; size_t v___y_1720_; uint8_t v___y_1721_; uint8_t v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___x_1855_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; size_t v___y_1862_; lean_object* v___y_1863_; size_t v___y_1864_; lean_object* v___y_1865_; uint8_t v___y_1866_; lean_object* v___y_1867_; uint8_t v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1898_; uint8_t v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; uint8_t v___y_1917_; uint8_t v___x_1940_; 
v___x_1855_ = lean_array_get_size(v_params_1704_);
v___x_1940_ = lean_nat_dec_eq(v_size_1699_, v___x_1855_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_nat_dec_eq(v_size_1699_, v___x_1941_);
v___y_1917_ = v___x_1942_;
goto v___jp_1916_;
}
else
{
v___y_1917_ = v___x_1940_;
goto v___jp_1916_;
}
v___jp_1709_:
{
lean_object* v___x_1725_; 
lean_inc_ref(v___y_1723_);
v___x_1725_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v___y_1723_, v_value_1689_, v___y_1715_, v___y_1713_, v___y_1717_, v___y_1718_, v___y_1710_);
lean_dec_ref(v___y_1715_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = l_Lean_Compiler_LCNF_Code_inferType(v___y_1721_, v_code_1693_, v___y_1713_, v___y_1717_, v___y_1718_, v___y_1710_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v___x_1727_);
lean_inc_ref(v___y_1714_);
v___x_1729_ = l_Lean_Compiler_LCNF_mkForallParams(v___y_1721_, v___y_1714_, v_a_1728_, v___y_1713_, v___y_1717_, v___y_1718_, v___y_1710_);
lean_dec(v_a_1728_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = lean_box(0);
lean_inc(v___y_1719_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 3, v___y_1714_);
lean_ctor_set(v___x_1707_, 2, v_a_1730_);
lean_ctor_set(v___x_1707_, 1, v___x_1731_);
lean_ctor_set(v___x_1707_, 0, v___y_1719_);
v___x_1733_ = v___x_1707_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___y_1719_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_a_1730_);
lean_ctor_set(v_reuseFailAlloc_1830_, 3, v___y_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*4, v_safe_1705_);
v___x_1733_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
lean_ctor_set(v___x_1734_, 1, v_a_1726_);
lean_ctor_set(v___x_1734_, 2, v_inlineAttr_x3f_1692_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*3, v_recursive_1691_);
lean_inc_ref(v___x_1734_);
v___x_1735_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1734_, v___y_1710_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec_ref(v___x_1735_);
v___x_1736_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0);
lean_inc(v___y_1711_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___y_1711_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = lean_st_mk_ref(v___x_1737_);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v___y_1720_, v___y_1716_, v_params_1704_, v___y_1722_, v___x_1738_, v___y_1713_, v___y_1717_, v___y_1718_, v___y_1710_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; size_t v_sz_1745_; lean_object* v___x_1746_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc_n(v_a_1740_, 2);
lean_dec_ref(v___x_1739_);
v___x_1741_ = lean_mk_empty_array_with_capacity(v___y_1711_);
v___x_1742_ = lean_array_get_size(v_a_1740_);
v___x_1743_ = l_Array_toSubarray___redArg(v_a_1740_, v___y_1711_, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1741_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v_sz_1745_ = lean_array_size(v___y_1712_);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v___y_1712_, v_sz_1745_, v___y_1716_, v___x_1744_);
lean_dec_ref(v___y_1712_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v_fst_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1804_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v_fst_1748_ = lean_ctor_get(v_a_1747_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_a_1747_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; 
v_unused_1805_ = lean_ctor_get(v_a_1747_, 1);
lean_dec(v_unused_1805_);
v___x_1750_ = v_a_1747_;
v_isShared_1751_ = v_isSharedCheck_1804_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_fst_1748_);
lean_dec(v_a_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1804_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1752_, 0, v___y_1719_);
lean_ctor_set(v___x_1752_, 1, v___x_1731_);
lean_ctor_set(v___x_1752_, 2, v_fst_1748_);
v___x_1753_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_1754_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___y_1721_, v___x_1752_, v___x_1753_, v___y_1713_, v___y_1717_, v___y_1718_, v___y_1710_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v_fvarId_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1754_);
v_fvarId_1756_ = lean_ctor_get(v_a_1755_, 0);
lean_inc(v_fvarId_1756_);
v___x_1757_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_fvarId_1756_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1757_);
lean_ctor_set(v___x_1750_, 0, v_a_1755_);
v___x_1759_ = v___x_1750_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1755_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
v___x_1761_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1761_, 0, v_name_1701_);
lean_ctor_set(v___x_1761_, 1, v_levelParams_1702_);
lean_ctor_set(v___x_1761_, 2, v_type_1703_);
lean_ctor_set(v___x_1761_, 3, v_a_1740_);
lean_ctor_set_uint8(v___x_1761_, sizeof(void*)*4, v_safe_1705_);
v___x_1762_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3));
v___x_1763_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1760_);
lean_ctor_set(v___x_1763_, 2, v___x_1762_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*3, v___y_1722_);
lean_inc_ref(v___x_1763_);
v___x_1764_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1763_, v___y_1710_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_dec_ref(v___x_1764_);
v___x_1765_ = lean_st_ref_get(v___x_1738_);
lean_dec(v___x_1738_);
lean_dec(v___x_1765_);
v___x_1766_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___y_1721_, v___y_1724_, v___y_1717_);
lean_dec_ref(v___y_1724_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1777_; 
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v___x_1766_, 0);
lean_dec(v_unused_1778_);
v___x_1768_ = v___x_1766_;
v_isShared_1769_ = v_isSharedCheck_1777_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v___x_1766_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1777_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1770_ = lean_unsigned_to_nat(2u);
v___x_1771_ = lean_mk_empty_array_with_capacity(v___x_1770_);
v___x_1772_ = lean_array_push(v___x_1771_, v___x_1734_);
v___x_1773_ = lean_array_push(v___x_1772_, v___x_1763_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1773_);
v___x_1775_ = v___x_1768_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v___x_1763_);
lean_dec_ref(v___x_1734_);
v_a_1779_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1766_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1766_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v___x_1763_);
lean_dec(v___x_1738_);
lean_dec_ref(v___x_1734_);
lean_dec_ref(v___y_1724_);
v_a_1787_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1764_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1764_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_del_object(v___x_1750_);
lean_dec(v_a_1740_);
lean_dec(v___x_1738_);
lean_dec_ref(v___x_1734_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v_type_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_name_1701_);
v_a_1796_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1754_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1754_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_a_1740_);
lean_dec(v___x_1738_);
lean_dec_ref(v___x_1734_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1719_);
lean_dec_ref(v_type_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_name_1701_);
v_a_1806_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1746_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1746_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec(v___x_1738_);
lean_dec_ref(v___x_1734_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v_type_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_name_1701_);
v_a_1814_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1739_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1739_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec_ref(v___x_1734_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v_params_1704_);
lean_dec_ref(v_type_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_name_1701_);
v_a_1822_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1735_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1735_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v_a_1726_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1714_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_del_object(v___x_1707_);
lean_dec_ref(v_params_1704_);
lean_dec_ref(v_type_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_name_1701_);
lean_dec(v_inlineAttr_x3f_1692_);
v_a_1831_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1729_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1729_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec(v_a_1726_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1714_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_del_object(v___x_1707_);
lean_dec_ref(v_params_1704_);
lean_dec_ref(v_type_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_name_1701_);
lean_dec(v_inlineAttr_x3f_1692_);
v_a_1839_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1727_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1727_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1714_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_del_object(v___x_1707_);
lean_dec_ref(v_params_1704_);
lean_dec_ref(v_type_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_name_1701_);
lean_dec_ref(v_code_1693_);
lean_dec(v_inlineAttr_x3f_1692_);
v_a_1847_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1725_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1725_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
v___jp_1856_:
{
uint8_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1868_ = 0;
v___x_1869_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4));
lean_inc_ref(v___y_1860_);
lean_inc(v___y_1861_);
lean_inc(v_name_1701_);
v___x_1870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1870_, 0, v_name_1701_);
lean_ctor_set(v___x_1870_, 1, v___y_1861_);
lean_ctor_set(v___x_1870_, 2, v___y_1860_);
v___x_1871_ = lean_mk_empty_array_with_capacity(v___y_1858_);
v___x_1872_ = lean_nat_dec_lt(v___y_1858_, v___x_1855_);
if (v___x_1872_ == 0)
{
lean_dec(v_a_1695_);
v___y_1710_ = v___y_1859_;
v___y_1711_ = v___y_1858_;
v___y_1712_ = v___y_1860_;
v___y_1713_ = v___y_1863_;
v___y_1714_ = v___y_1867_;
v___y_1715_ = v___x_1870_;
v___y_1716_ = v___y_1864_;
v___y_1717_ = v___y_1865_;
v___y_1718_ = v___y_1857_;
v___y_1719_ = v___y_1861_;
v___y_1720_ = v___y_1862_;
v___y_1721_ = v___x_1868_;
v___y_1722_ = v___y_1866_;
v___y_1723_ = v___x_1869_;
v___y_1724_ = v___x_1871_;
goto v___jp_1709_;
}
else
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_nat_dec_le(v___x_1855_, v___x_1855_);
if (v___x_1873_ == 0)
{
if (v___x_1872_ == 0)
{
lean_dec(v_a_1695_);
v___y_1710_ = v___y_1859_;
v___y_1711_ = v___y_1858_;
v___y_1712_ = v___y_1860_;
v___y_1713_ = v___y_1863_;
v___y_1714_ = v___y_1867_;
v___y_1715_ = v___x_1870_;
v___y_1716_ = v___y_1864_;
v___y_1717_ = v___y_1865_;
v___y_1718_ = v___y_1857_;
v___y_1719_ = v___y_1861_;
v___y_1720_ = v___y_1862_;
v___y_1721_ = v___x_1868_;
v___y_1722_ = v___y_1866_;
v___y_1723_ = v___x_1869_;
v___y_1724_ = v___x_1871_;
goto v___jp_1709_;
}
else
{
size_t v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_usize_of_nat(v___x_1855_);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1695_, v_params_1704_, v___y_1864_, v___x_1874_, v___x_1871_);
lean_dec(v_a_1695_);
v___y_1710_ = v___y_1859_;
v___y_1711_ = v___y_1858_;
v___y_1712_ = v___y_1860_;
v___y_1713_ = v___y_1863_;
v___y_1714_ = v___y_1867_;
v___y_1715_ = v___x_1870_;
v___y_1716_ = v___y_1864_;
v___y_1717_ = v___y_1865_;
v___y_1718_ = v___y_1857_;
v___y_1719_ = v___y_1861_;
v___y_1720_ = v___y_1862_;
v___y_1721_ = v___x_1868_;
v___y_1722_ = v___y_1866_;
v___y_1723_ = v___x_1869_;
v___y_1724_ = v___x_1875_;
goto v___jp_1709_;
}
}
else
{
size_t v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_usize_of_nat(v___x_1855_);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1695_, v_params_1704_, v___y_1864_, v___x_1876_, v___x_1871_);
lean_dec(v_a_1695_);
v___y_1710_ = v___y_1859_;
v___y_1711_ = v___y_1858_;
v___y_1712_ = v___y_1860_;
v___y_1713_ = v___y_1863_;
v___y_1714_ = v___y_1867_;
v___y_1715_ = v___x_1870_;
v___y_1716_ = v___y_1864_;
v___y_1717_ = v___y_1865_;
v___y_1718_ = v___y_1857_;
v___y_1719_ = v___y_1861_;
v___y_1720_ = v___y_1862_;
v___y_1721_ = v___x_1868_;
v___y_1722_ = v___y_1866_;
v___y_1723_ = v___x_1869_;
v___y_1724_ = v___x_1877_;
goto v___jp_1709_;
}
}
}
v___jp_1878_:
{
size_t v_sz_1884_; size_t v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_sz_1884_ = lean_array_size(v_params_1704_);
v___x_1885_ = ((size_t)0ULL);
lean_inc_ref(v_params_1704_);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1695_, v_sz_1884_, v___x_1885_, v_params_1704_);
v___x_1887_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6));
lean_inc(v_name_1701_);
v___x_1888_ = l_Lean_Name_append(v_name_1701_, v___x_1887_);
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7));
v___x_1891_ = lean_nat_dec_lt(v___x_1889_, v___x_1855_);
if (v___x_1891_ == 0)
{
v___y_1857_ = v___y_1882_;
v___y_1858_ = v___x_1889_;
v___y_1859_ = v___y_1883_;
v___y_1860_ = v___x_1886_;
v___y_1861_ = v___x_1888_;
v___y_1862_ = v_sz_1884_;
v___y_1863_ = v___y_1880_;
v___y_1864_ = v___x_1885_;
v___y_1865_ = v___y_1881_;
v___y_1866_ = v___y_1879_;
v___y_1867_ = v___x_1890_;
goto v___jp_1856_;
}
else
{
uint8_t v___x_1892_; 
v___x_1892_ = lean_nat_dec_le(v___x_1855_, v___x_1855_);
if (v___x_1892_ == 0)
{
if (v___x_1891_ == 0)
{
v___y_1857_ = v___y_1882_;
v___y_1858_ = v___x_1889_;
v___y_1859_ = v___y_1883_;
v___y_1860_ = v___x_1886_;
v___y_1861_ = v___x_1888_;
v___y_1862_ = v_sz_1884_;
v___y_1863_ = v___y_1880_;
v___y_1864_ = v___x_1885_;
v___y_1865_ = v___y_1881_;
v___y_1866_ = v___y_1879_;
v___y_1867_ = v___x_1890_;
goto v___jp_1856_;
}
else
{
size_t v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_usize_of_nat(v___x_1855_);
v___x_1894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1695_, v_params_1704_, v___x_1885_, v___x_1893_, v___x_1890_);
v___y_1857_ = v___y_1882_;
v___y_1858_ = v___x_1889_;
v___y_1859_ = v___y_1883_;
v___y_1860_ = v___x_1886_;
v___y_1861_ = v___x_1888_;
v___y_1862_ = v_sz_1884_;
v___y_1863_ = v___y_1880_;
v___y_1864_ = v___x_1885_;
v___y_1865_ = v___y_1881_;
v___y_1866_ = v___y_1879_;
v___y_1867_ = v___x_1894_;
goto v___jp_1856_;
}
}
else
{
size_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_usize_of_nat(v___x_1855_);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1695_, v_params_1704_, v___x_1885_, v___x_1895_, v___x_1890_);
v___y_1857_ = v___y_1882_;
v___y_1858_ = v___x_1889_;
v___y_1859_ = v___y_1883_;
v___y_1860_ = v___x_1886_;
v___y_1861_ = v___x_1888_;
v___y_1862_ = v_sz_1884_;
v___y_1863_ = v___y_1880_;
v___y_1864_ = v___x_1885_;
v___y_1865_ = v___y_1881_;
v___y_1866_ = v___y_1879_;
v___y_1867_ = v___x_1896_;
goto v___jp_1856_;
}
}
}
v___jp_1897_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1902_ = lean_box(0);
v___x_1903_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(v___y_1901_, v___x_1902_);
v___x_1904_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(v___x_1903_, v___x_1902_);
v___x_1905_ = l_Lean_MessageData_ofList(v___x_1904_);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___y_1900_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
lean_inc(v___y_1898_);
v___x_1907_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v___y_1898_, v___x_1906_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_dec_ref(v___x_1907_);
v___y_1879_ = v___y_1899_;
v___y_1880_ = v_a_1684_;
v___y_1881_ = v_a_1685_;
v___y_1882_ = v_a_1686_;
v___y_1883_ = v_a_1687_;
goto v___jp_1878_;
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_del_object(v___x_1707_);
lean_dec_ref(v_params_1704_);
lean_dec_ref(v_type_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_name_1701_);
lean_dec(v_a_1695_);
lean_dec_ref(v_code_1693_);
lean_dec(v_inlineAttr_x3f_1692_);
lean_dec_ref(v_value_1689_);
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
v___jp_1916_:
{
if (v___y_1917_ == 0)
{
lean_object* v_options_1918_; uint8_t v_hasTrace_1919_; 
lean_inc(v_inlineAttr_x3f_1692_);
lean_del_object(v___x_1697_);
lean_dec_ref(v_decl_1683_);
v_options_1918_ = lean_ctor_get(v_a_1686_, 2);
v_hasTrace_1919_ = lean_ctor_get_uint8(v_options_1918_, sizeof(void*)*1);
if (v_hasTrace_1919_ == 0)
{
v___y_1879_ = v___y_1917_;
v___y_1880_ = v_a_1684_;
v___y_1881_ = v_a_1685_;
v___y_1882_ = v_a_1686_;
v___y_1883_ = v_a_1687_;
goto v___jp_1878_;
}
else
{
lean_object* v_inheritedTraceOptions_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v_inheritedTraceOptions_1920_ = lean_ctor_get(v_a_1686_, 13);
v___x_1921_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10));
v___x_1922_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13);
v___x_1923_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1920_, v_options_1918_, v___x_1922_);
if (v___x_1923_ == 0)
{
v___y_1879_ = v___y_1917_;
v___y_1880_ = v_a_1684_;
v___y_1881_ = v_a_1685_;
v___y_1882_ = v_a_1686_;
v___y_1883_ = v_a_1687_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
lean_inc(v_name_1701_);
v___x_1924_ = l_Lean_MessageData_ofName(v_name_1701_);
v___x_1925_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_array_get_size(v_buckets_1700_);
v___x_1929_ = lean_unsigned_to_nat(0u);
v___x_1930_ = lean_nat_dec_lt(v___x_1929_, v___x_1928_);
if (v___x_1930_ == 0)
{
v___y_1898_ = v___x_1921_;
v___y_1899_ = v___y_1917_;
v___y_1900_ = v___x_1926_;
v___y_1901_ = v___x_1927_;
goto v___jp_1897_;
}
else
{
size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_usize_of_nat(v___x_1928_);
v___x_1932_ = ((size_t)0ULL);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_buckets_1700_, v___x_1931_, v___x_1932_, v___x_1927_);
v___y_1898_ = v___x_1921_;
v___y_1899_ = v___y_1917_;
v___y_1900_ = v___x_1926_;
v___y_1901_ = v___x_1933_;
goto v___jp_1897_;
}
}
}
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
lean_del_object(v___x_1707_);
lean_dec_ref(v_params_1704_);
lean_dec_ref(v_type_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_name_1701_);
lean_dec(v_a_1695_);
lean_dec_ref(v_code_1693_);
lean_dec_ref(v_value_1689_);
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = lean_mk_empty_array_with_capacity(v___x_1934_);
v___x_1936_ = lean_array_push(v___x_1935_, v_decl_1683_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v___x_1936_);
v___x_1938_ = v___x_1697_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_code_1693_);
lean_dec_ref(v_toSignature_1690_);
lean_dec_ref(v_value_1689_);
lean_dec_ref(v_decl_1683_);
v_a_1945_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1694_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1694_);
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
else
{
lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1962_; 
v_isSharedCheck_1962_ = !lean_is_exclusive(v_value_1689_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v_value_1689_, 0);
lean_dec(v_unused_1963_);
v___x_1954_ = v_value_1689_;
v_isShared_1955_ = v_isSharedCheck_1962_;
goto v_resetjp_1953_;
}
else
{
lean_dec(v_value_1689_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1962_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1956_ = lean_unsigned_to_nat(1u);
v___x_1957_ = lean_mk_empty_array_with_capacity(v___x_1956_);
v___x_1958_ = lean_array_push(v___x_1957_, v_decl_1683_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1958_);
v___x_1960_ = v___x_1954_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object* v_decl_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v_decl_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
return v_res_1970_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* v_00_u03b2_1971_, lean_object* v_m_1972_, lean_object* v_a_1973_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1972_, v_a_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* v_00_u03b2_1975_, lean_object* v_m_1976_, lean_object* v_a_1977_){
_start:
{
uint8_t v_res_1978_; lean_object* v_r_1979_; 
v_res_1978_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(v_00_u03b2_1975_, v_m_1976_, v_a_1977_);
lean_dec(v_a_1977_);
lean_dec_ref(v_m_1976_);
v_r_1979_ = lean_box(v_res_1978_);
return v_r_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* v_as_1980_, size_t v_sz_1981_, size_t v_i_1982_, lean_object* v_b_1983_, uint8_t v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_1980_, v_sz_1981_, v_i_1982_, v_b_1983_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* v_as_1992_, lean_object* v_sz_1993_, lean_object* v_i_1994_, lean_object* v_b_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
size_t v_sz_boxed_2003_; size_t v_i_boxed_2004_; uint8_t v___y_13285__boxed_2005_; lean_object* v_res_2006_; 
v_sz_boxed_2003_ = lean_unbox_usize(v_sz_1993_);
lean_dec(v_sz_1993_);
v_i_boxed_2004_ = lean_unbox_usize(v_i_1994_);
lean_dec(v_i_1994_);
v___y_13285__boxed_2005_ = lean_unbox(v___y_1996_);
v_res_2006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_1992_, v_sz_boxed_2003_, v_i_boxed_2004_, v_b_1995_, v___y_13285__boxed_2005_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v_as_1992_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* v_as_2007_, size_t v_i_2008_, size_t v_stop_2009_, lean_object* v_b_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_a_2017_; uint8_t v___x_2021_; 
v___x_2021_ = lean_usize_dec_eq(v_i_2008_, v_stop_2009_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_array_uget_borrowed(v_as_2007_, v_i_2008_);
lean_inc(v___x_2022_);
v___x_2023_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v___x_2022_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref(v___x_2023_);
v___x_2025_ = l_Array_append___redArg(v_b_2010_, v_a_2024_);
lean_dec(v_a_2024_);
v_a_2017_ = v___x_2025_;
goto v___jp_2016_;
}
else
{
lean_dec_ref(v_b_2010_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2026_; 
v_a_2026_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2026_);
lean_dec_ref(v___x_2023_);
v_a_2017_ = v_a_2026_;
goto v___jp_2016_;
}
else
{
return v___x_2023_;
}
}
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v_b_2010_);
return v___x_2027_;
}
v___jp_2016_:
{
size_t v___x_2018_; size_t v___x_2019_; 
v___x_2018_ = ((size_t)1ULL);
v___x_2019_ = lean_usize_add(v_i_2008_, v___x_2018_);
v_i_2008_ = v___x_2019_;
v_b_2010_ = v_a_2017_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* v_as_2028_, lean_object* v_i_2029_, lean_object* v_stop_2030_, lean_object* v_b_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
size_t v_i_boxed_2037_; size_t v_stop_boxed_2038_; lean_object* v_res_2039_; 
v_i_boxed_2037_ = lean_unbox_usize(v_i_2029_);
lean_dec(v_i_2029_);
v_stop_boxed_2038_ = lean_unbox_usize(v_stop_2030_);
lean_dec(v_stop_2030_);
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_2028_, v_i_boxed_2037_, v_stop_boxed_2038_, v_b_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec_ref(v_as_2028_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* v___x_2040_, lean_object* v_decls_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2047_ = lean_mk_empty_array_with_capacity(v___x_2040_);
v___x_2048_ = lean_array_get_size(v_decls_2041_);
v___x_2049_ = lean_nat_dec_lt(v___x_2040_, v___x_2048_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2047_);
return v___x_2050_;
}
else
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_nat_dec_le(v___x_2048_, v___x_2048_);
if (v___x_2051_ == 0)
{
if (v___x_2049_ == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2047_);
return v___x_2052_;
}
else
{
size_t v___x_2053_; size_t v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = ((size_t)0ULL);
v___x_2054_ = lean_usize_of_nat(v___x_2048_);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2041_, v___x_2053_, v___x_2054_, v___x_2047_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
return v___x_2055_;
}
}
else
{
size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = ((size_t)0ULL);
v___x_2057_ = lean_usize_of_nat(v___x_2048_);
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2041_, v___x_2056_, v___x_2057_, v___x_2047_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* v___x_2059_, lean_object* v_decls_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(v___x_2059_, v_decls_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec_ref(v_decls_2060_);
lean_dec(v___x_2059_);
return v_res_2066_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_unsigned_to_nat(2803462840u);
v___x_2130_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2131_ = l_Lean_Name_num___override(v___x_2130_, v___x_2129_);
return v___x_2131_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2134_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2135_ = l_Lean_Name_str___override(v___x_2134_, v___x_2133_);
return v___x_2135_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2138_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2139_ = l_Lean_Name_str___override(v___x_2138_, v___x_2137_);
return v___x_2139_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = lean_unsigned_to_nat(2u);
v___x_2141_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2142_ = l_Lean_Name_num___override(v___x_2141_, v___x_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2144_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10));
v___x_2145_ = 1;
v___x_2146_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2147_ = l_Lean_registerTraceClass(v___x_2144_, v___x_2145_, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
return v_res_2149_;
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
