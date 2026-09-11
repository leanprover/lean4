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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Param_toArg___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5_value;
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
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1;
static const lean_array_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_dummy"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 145, 231, 197, 9, 240, 100, 81)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lcVoid"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value),LEAN_SCALAR_PTR_LITERAL(68, 180, 59, 167, 252, 217, 37, 174)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_redArg"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value),LEAN_SCALAR_PTR_LITERAL(174, 35, 1, 83, 6, 52, 87, 186)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "reduceArity"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value),LEAN_SCALAR_PTR_LITERAL(89, 83, 236, 44, 104, 94, 232, 236)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15;
static const lean_string_object l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ", used params: "};
static const lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17;
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
static const lean_ctor_object l_Lean_Compiler_LCNF_reduceArity___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value),LEAN_SCALAR_PTR_LITERAL(111, 96, 179, 183, 204, 167, 118, 86)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value),LEAN_SCALAR_PTR_LITERAL(14, 5, 205, 56, 180, 134, 217, 66)}};
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value),LEAN_SCALAR_PTR_LITERAL(88, 65, 191, 26, 52, 74, 82, 47)}};
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
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_nbuckets_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_53_ = lean_array_get_size(v_data_52_);
v___x_54_ = lean_unsigned_to_nat(2u);
v_nbuckets_55_ = lean_nat_mul(v___x_53_, v___x_54_);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_box(0);
v___x_58_ = lean_mk_array(v_nbuckets_55_, v___x_57_);
v___x_59_ = lean_array_propagate_mark(v_data_52_, v___x_58_);
v___x_60_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(v___x_56_, v_data_52_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(lean_object* v_m_61_, lean_object* v_a_62_, lean_object* v_b_63_){
_start:
{
lean_object* v_size_64_; lean_object* v_buckets_65_; lean_object* v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v_fold_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; lean_object* v_bkt_79_; uint8_t v___x_80_; 
v_size_64_ = lean_ctor_get(v_m_61_, 0);
v_buckets_65_ = lean_ctor_get(v_m_61_, 1);
v___x_66_ = lean_array_get_size(v_buckets_65_);
v___x_67_ = l_Lean_instHashableFVarId_hash(v_a_62_);
v___x_68_ = 32ULL;
v___x_69_ = lean_uint64_shift_right(v___x_67_, v___x_68_);
v_fold_70_ = lean_uint64_xor(v___x_67_, v___x_69_);
v___x_71_ = 16ULL;
v___x_72_ = lean_uint64_shift_right(v_fold_70_, v___x_71_);
v___x_73_ = lean_uint64_xor(v_fold_70_, v___x_72_);
v___x_74_ = lean_uint64_to_usize(v___x_73_);
v___x_75_ = lean_usize_of_nat(v___x_66_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_sub(v___x_75_, v___x_76_);
v___x_78_ = lean_usize_land(v___x_74_, v___x_77_);
v_bkt_79_ = lean_array_uget_borrowed(v_buckets_65_, v___x_78_);
v___x_80_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_62_, v_bkt_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_101_; 
lean_inc_ref(v_buckets_65_);
lean_inc(v_size_64_);
v_isSharedCheck_101_ = !lean_is_exclusive(v_m_61_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; lean_object* v_unused_103_; 
v_unused_102_ = lean_ctor_get(v_m_61_, 1);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_m_61_, 0);
lean_dec(v_unused_103_);
v___x_82_ = v_m_61_;
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
else
{
lean_dec(v_m_61_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v_size_x27_85_; lean_object* v___x_86_; lean_object* v_buckets_x27_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v_size_x27_85_ = lean_nat_add(v_size_64_, v___x_84_);
lean_dec(v_size_64_);
lean_inc(v_bkt_79_);
v___x_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_86_, 0, v_a_62_);
lean_ctor_set(v___x_86_, 1, v_b_63_);
lean_ctor_set(v___x_86_, 2, v_bkt_79_);
v_buckets_x27_87_ = lean_array_uset(v_buckets_65_, v___x_78_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(4u);
v___x_89_ = lean_nat_mul(v_size_x27_85_, v___x_88_);
v___x_90_ = lean_unsigned_to_nat(3u);
v___x_91_ = lean_nat_div(v___x_89_, v___x_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_array_get_size(v_buckets_x27_87_);
v___x_93_ = lean_nat_dec_le(v___x_91_, v___x_92_);
lean_dec(v___x_91_);
if (v___x_93_ == 0)
{
lean_object* v_val_94_; lean_object* v___x_96_; 
v_val_94_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(v_buckets_x27_87_);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_val_94_);
lean_ctor_set(v___x_82_, 0, v_size_x27_85_);
v___x_96_ = v___x_82_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_size_x27_85_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_val_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
else
{
lean_object* v___x_99_; 
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 1, v_buckets_x27_87_);
lean_ctor_set(v___x_82_, 0, v_size_x27_85_);
v___x_99_ = v___x_82_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_size_x27_85_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_buckets_x27_87_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_dec(v_b_63_);
lean_dec(v_a_62_);
return v_m_61_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(lean_object* v_k_104_, lean_object* v_t_105_){
_start:
{
if (lean_obj_tag(v_t_105_) == 0)
{
lean_object* v_k_106_; lean_object* v_l_107_; lean_object* v_r_108_; uint8_t v___x_109_; 
v_k_106_ = lean_ctor_get(v_t_105_, 1);
v_l_107_ = lean_ctor_get(v_t_105_, 3);
v_r_108_ = lean_ctor_get(v_t_105_, 4);
v___x_109_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_104_, v_k_106_);
switch(v___x_109_)
{
case 0:
{
v_t_105_ = v_l_107_;
goto _start;
}
case 1:
{
uint8_t v___x_111_; 
v___x_111_ = 1;
return v___x_111_;
}
default: 
{
v_t_105_ = v_r_108_;
goto _start;
}
}
}
else
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg___boxed(lean_object* v_k_114_, lean_object* v_t_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_114_, v_t_115_);
lean_dec(v_t_115_);
lean_dec(v_k_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object* v_fvarId_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_params_122_; uint8_t v___x_123_; 
v_params_122_ = lean_ctor_get(v_a_119_, 1);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_fvarId_118_, v_params_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v_fvarId_118_);
v___x_124_ = lean_box(0);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = lean_st_ref_take(v_a_120_);
v___x_127_ = lean_box(0);
v___x_128_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v___x_126_, v_fvarId_118_, v___x_127_);
v___x_129_ = lean_st_ref_put(v_a_120_, v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_127_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object* v_fvarId_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object* v_fvarId_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_136_, v_a_137_, v_a_138_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object* v_fvarId_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar(v_fvarId_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
return v_res_153_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(lean_object* v_00_u03b2_154_, lean_object* v_k_155_, lean_object* v_t_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_155_, v_t_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___boxed(lean_object* v_00_u03b2_158_, lean_object* v_k_159_, lean_object* v_t_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(v_00_u03b2_158_, v_k_159_, v_t_160_);
lean_dec(v_t_160_);
lean_dec(v_k_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1(lean_object* v_00_u03b2_163_, lean_object* v_m_164_, lean_object* v_a_165_, lean_object* v_b_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v_m_164_, v_a_165_, v_b_166_);
return v___x_167_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(lean_object* v_00_u03b2_168_, lean_object* v_a_169_, lean_object* v_x_170_){
_start:
{
uint8_t v___x_171_; 
v___x_171_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_169_, v_x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___boxed(lean_object* v_00_u03b2_172_, lean_object* v_a_173_, lean_object* v_x_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(v_00_u03b2_172_, v_a_173_, v_x_174_);
lean_dec(v_x_174_);
lean_dec(v_a_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2(lean_object* v_00_u03b2_177_, lean_object* v_data_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(v_data_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_180_, lean_object* v_i_181_, lean_object* v_source_182_, lean_object* v_target_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(v_i_181_, v_source_182_, v_target_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(v_x_186_, v_x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object* v_arg_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
if (lean_obj_tag(v_arg_189_) == 1)
{
lean_object* v_fvarId_193_; lean_object* v___x_194_; 
v_fvarId_193_ = lean_ctor_get(v_arg_189_, 0);
lean_inc(v_fvarId_193_);
lean_dec_ref_known(v_arg_189_, 1);
v___x_194_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_193_, v_a_190_, v_a_191_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_arg_189_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object* v_arg_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object* v_arg_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_202_, v_a_203_, v_a_204_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object* v_arg_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Compiler_LCNF_FindUsed_visitArg(v_arg_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object* v_as_220_, size_t v_sz_221_, size_t v_i_222_, lean_object* v_b_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_a_228_; uint8_t v___x_232_; 
v___x_232_ = lean_usize_dec_lt(v_i_222_, v_sz_221_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_b_223_);
return v___x_233_;
}
else
{
lean_object* v_array_234_; lean_object* v_start_235_; lean_object* v_stop_236_; uint8_t v___x_237_; 
v_array_234_ = lean_ctor_get(v_b_223_, 0);
v_start_235_ = lean_ctor_get(v_b_223_, 1);
v_stop_236_ = lean_ctor_get(v_b_223_, 2);
v___x_237_ = lean_nat_dec_lt(v_start_235_, v_stop_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v_b_223_);
return v___x_238_;
}
else
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_261_; 
lean_inc(v_stop_236_);
lean_inc(v_start_235_);
lean_inc_ref(v_array_234_);
v_isSharedCheck_261_ = !lean_is_exclusive(v_b_223_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; lean_object* v_unused_263_; lean_object* v_unused_264_; 
v_unused_262_ = lean_ctor_get(v_b_223_, 2);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_b_223_, 1);
lean_dec(v_unused_263_);
v_unused_264_ = lean_ctor_get(v_b_223_, 0);
lean_dec(v_unused_264_);
v___x_240_ = v_b_223_;
v_isShared_241_ = v_isSharedCheck_261_;
goto v_resetjp_239_;
}
else
{
lean_dec(v_b_223_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_261_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_242_ = lean_array_fget(v_array_234_, v_start_235_);
v___x_243_ = lean_unsigned_to_nat(1u);
v___x_244_ = lean_nat_add(v_start_235_, v___x_243_);
lean_dec(v_start_235_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_244_);
v___x_246_ = v___x_240_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_array_234_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_stop_236_);
v___x_246_ = v_reuseFailAlloc_260_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
if (lean_obj_tag(v___x_242_) == 1)
{
lean_object* v_fvarId_247_; lean_object* v_a_248_; lean_object* v_fvarId_249_; uint8_t v___x_250_; 
v_fvarId_247_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_fvarId_247_);
lean_dec_ref_known(v___x_242_, 1);
v_a_248_ = lean_array_uget_borrowed(v_as_220_, v_i_222_);
v_fvarId_249_ = lean_ctor_get(v_a_248_, 0);
v___x_250_ = l_Lean_instBEqFVarId_beq(v_fvarId_247_, v_fvarId_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_247_, v___y_224_, v___y_225_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_dec_ref_known(v___x_251_, 1);
v_a_228_ = v___x_246_;
goto v___jp_227_;
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec_ref(v___x_246_);
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_dec(v_fvarId_247_);
v_a_228_ = v___x_246_;
goto v___jp_227_;
}
}
else
{
lean_dec(v___x_242_);
v_a_228_ = v___x_246_;
goto v___jp_227_;
}
}
}
}
}
v___jp_227_:
{
size_t v___x_229_; size_t v___x_230_; 
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_i_222_, v___x_229_);
v_i_222_ = v___x_230_;
v_b_223_ = v_a_228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object* v_as_265_, lean_object* v_sz_266_, lean_object* v_i_267_, lean_object* v_b_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
size_t v_sz_boxed_272_; size_t v_i_boxed_273_; lean_object* v_res_274_; 
v_sz_boxed_272_ = lean_unbox_usize(v_sz_266_);
lean_dec(v_sz_266_);
v_i_boxed_273_ = lean_unbox_usize(v_i_267_);
lean_dec(v_i_267_);
v_res_274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_265_, v_sz_boxed_272_, v_i_boxed_273_, v_b_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec_ref(v_as_265_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object* v_a_275_, lean_object* v_b_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_array_280_; lean_object* v_start_281_; lean_object* v_stop_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_298_; 
v_array_280_ = lean_ctor_get(v_a_275_, 0);
v_start_281_ = lean_ctor_get(v_a_275_, 1);
v_stop_282_ = lean_ctor_get(v_a_275_, 2);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_275_);
if (v_isSharedCheck_298_ == 0)
{
v___x_284_ = v_a_275_;
v_isShared_285_ = v_isSharedCheck_298_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_stop_282_);
lean_inc(v_start_281_);
lean_inc(v_array_280_);
lean_dec(v_a_275_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_298_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
uint8_t v___x_286_; 
v___x_286_ = lean_nat_dec_lt(v_start_281_, v_stop_282_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
lean_del_object(v___x_284_);
lean_dec(v_stop_282_);
lean_dec(v_start_281_);
lean_dec_ref(v_array_280_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v_b_276_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v_fvarId_289_; lean_object* v___x_290_; 
v___x_288_ = lean_array_fget_borrowed(v_array_280_, v_start_281_);
v_fvarId_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_fvarId_289_);
v___x_290_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_289_, v___y_277_, v___y_278_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
lean_dec_ref_known(v___x_290_, 1);
v___x_291_ = lean_box(0);
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_add(v_start_281_, v___x_292_);
lean_dec(v_start_281_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_293_);
v___x_295_ = v___x_284_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_array_280_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_stop_282_);
v___x_295_ = v_reuseFailAlloc_297_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
v_a_275_ = v___x_295_;
v_b_276_ = v___x_291_;
goto _start;
}
}
else
{
lean_del_object(v___x_284_);
lean_dec(v_stop_282_);
lean_dec(v_start_281_);
lean_dec_ref(v_array_280_);
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object* v_a_299_, lean_object* v_b_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_299_, v_b_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object* v_as_305_, size_t v_i_306_, size_t v_stop_307_, lean_object* v_b_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
uint8_t v___x_312_; 
v___x_312_ = lean_usize_dec_eq(v_i_306_, v_stop_307_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_array_uget_borrowed(v_as_305_, v_i_306_);
lean_inc(v___x_313_);
v___x_314_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v___x_313_, v___y_309_, v___y_310_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; size_t v___x_316_; size_t v___x_317_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_314_, 1);
v___x_316_ = ((size_t)1ULL);
v___x_317_ = lean_usize_add(v_i_306_, v___x_316_);
v_i_306_ = v___x_317_;
v_b_308_ = v_a_315_;
goto _start;
}
else
{
return v___x_314_;
}
}
else
{
lean_object* v___x_319_; 
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v_b_308_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object* v_as_320_, lean_object* v_i_321_, lean_object* v_stop_322_, lean_object* v_b_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
size_t v_i_boxed_327_; size_t v_stop_boxed_328_; lean_object* v_res_329_; 
v_i_boxed_327_ = lean_unbox_usize(v_i_321_);
lean_dec(v_i_321_);
v_stop_boxed_328_ = lean_unbox_usize(v_stop_322_);
lean_dec(v_stop_322_);
v_res_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_320_, v_i_boxed_327_, v_stop_boxed_328_, v_b_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec_ref(v_as_320_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object* v_a_330_, lean_object* v_b_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_array_335_; lean_object* v_start_336_; lean_object* v_stop_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_352_; 
v_array_335_ = lean_ctor_get(v_a_330_, 0);
v_start_336_ = lean_ctor_get(v_a_330_, 1);
v_stop_337_ = lean_ctor_get(v_a_330_, 2);
v_isSharedCheck_352_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_352_ == 0)
{
v___x_339_ = v_a_330_;
v_isShared_340_ = v_isSharedCheck_352_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_stop_337_);
lean_inc(v_start_336_);
lean_inc(v_array_335_);
lean_dec(v_a_330_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_352_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
uint8_t v___x_341_; 
v___x_341_ = lean_nat_dec_lt(v_start_336_, v_stop_337_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
lean_del_object(v___x_339_);
lean_dec(v_stop_337_);
lean_dec(v_start_336_);
lean_dec_ref(v_array_335_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v_b_331_);
return v___x_342_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_array_fget_borrowed(v_array_335_, v_start_336_);
lean_inc(v___x_343_);
v___x_344_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v___x_343_, v___y_332_, v___y_333_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
lean_dec_ref_known(v___x_344_, 1);
v___x_345_ = lean_box(0);
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_start_336_, v___x_346_);
lean_dec(v_start_336_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_347_);
v___x_349_ = v___x_339_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_array_335_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_347_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_stop_337_);
v___x_349_ = v_reuseFailAlloc_351_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
v_a_330_ = v___x_349_;
v_b_331_ = v___x_345_;
goto _start;
}
}
else
{
lean_del_object(v___x_339_);
lean_dec(v_stop_337_);
lean_dec(v_start_336_);
lean_dec_ref(v_array_335_);
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object* v_a_353_, lean_object* v_b_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_353_, v_b_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object* v_e_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
switch(lean_obj_tag(v_e_359_))
{
case 0:
{
lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_374_; 
v_isSharedCheck_374_ = !lean_is_exclusive(v_e_359_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; 
v_unused_375_ = lean_ctor_get(v_e_359_, 0);
lean_dec(v_unused_375_);
v___x_368_ = v_e_359_;
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
else
{
lean_dec(v_e_359_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_370_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
case 1:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_box(0);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
case 2:
{
lean_object* v_struct_378_; lean_object* v___x_379_; 
v_struct_378_ = lean_ctor_get(v_e_359_, 2);
lean_inc(v_struct_378_);
lean_dec_ref_known(v_e_359_, 3);
v___x_379_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_struct_378_, v_a_360_, v_a_361_);
return v___x_379_;
}
case 3:
{
lean_object* v_decl_380_; lean_object* v_toSignature_381_; lean_object* v_declName_382_; lean_object* v_args_383_; lean_object* v_name_384_; lean_object* v_params_385_; lean_object* v___y_387_; lean_object* v_lower_388_; lean_object* v_upper_389_; uint8_t v___x_400_; 
v_decl_380_ = lean_ctor_get(v_a_360_, 0);
v_toSignature_381_ = lean_ctor_get(v_decl_380_, 0);
v_declName_382_ = lean_ctor_get(v_e_359_, 0);
lean_inc(v_declName_382_);
v_args_383_ = lean_ctor_get(v_e_359_, 2);
lean_inc_ref(v_args_383_);
lean_dec_ref_known(v_e_359_, 3);
v_name_384_ = lean_ctor_get(v_toSignature_381_, 0);
v_params_385_ = lean_ctor_get(v_toSignature_381_, 3);
v___x_400_ = lean_name_eq(v_declName_382_, v_name_384_);
lean_dec(v_declName_382_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = lean_array_get_size(v_args_383_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_nat_dec_lt(v___x_401_, v___x_402_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_dec_ref(v_args_383_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
return v___x_405_;
}
else
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_le(v___x_402_, v___x_402_);
if (v___x_406_ == 0)
{
if (v___x_404_ == 0)
{
lean_object* v___x_407_; 
lean_dec_ref(v_args_383_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_403_);
return v___x_407_;
}
else
{
size_t v___x_408_; size_t v___x_409_; lean_object* v___x_410_; 
v___x_408_ = ((size_t)0ULL);
v___x_409_ = lean_usize_of_nat(v___x_402_);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_383_, v___x_408_, v___x_409_, v___x_403_, v_a_360_, v_a_361_);
lean_dec_ref(v_args_383_);
return v___x_410_;
}
}
else
{
size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((size_t)0ULL);
v___x_412_ = lean_usize_of_nat(v___x_402_);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_383_, v___x_411_, v___x_412_, v___x_403_, v_a_360_, v_a_361_);
lean_dec_ref(v_args_383_);
return v___x_413_;
}
}
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; size_t v_sz_417_; size_t v___x_418_; lean_object* v___x_419_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_array_get_size(v_args_383_);
lean_inc_ref(v_args_383_);
v___x_416_ = l_Array_toSubarray___redArg(v_args_383_, v___x_414_, v___x_415_);
v_sz_417_ = lean_array_size(v_params_385_);
v___x_418_ = ((size_t)0ULL);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_params_385_, v_sz_417_, v___x_418_, v___x_416_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_lower_421_; lean_object* v_upper_422_; lean_object* v___x_428_; uint8_t v___x_429_; 
lean_dec_ref_known(v___x_419_, 1);
v___x_428_ = lean_array_get_size(v_params_385_);
v___x_429_ = lean_nat_dec_le(v___x_428_, v___x_414_);
if (v___x_429_ == 0)
{
v_lower_421_ = v___x_428_;
v_upper_422_ = v___x_415_;
goto v___jp_420_;
}
else
{
v_lower_421_ = v___x_414_;
v_upper_422_ = v___x_415_;
goto v___jp_420_;
}
v___jp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = l_Array_toSubarray___redArg(v_args_383_, v_lower_421_, v_upper_422_);
v___x_424_ = lean_box(0);
v___x_425_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v___x_423_, v___x_424_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
lean_dec_ref_known(v___x_425_, 1);
v___x_426_ = lean_array_get_size(v_params_385_);
v___x_427_ = lean_nat_dec_le(v___x_415_, v___x_414_);
if (v___x_427_ == 0)
{
v___y_387_ = v___x_424_;
v_lower_388_ = v___x_415_;
v_upper_389_ = v___x_426_;
goto v___jp_386_;
}
else
{
v___y_387_ = v___x_424_;
v_lower_388_ = v___x_414_;
v_upper_389_ = v___x_426_;
goto v___jp_386_;
}
}
else
{
return v___x_425_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_args_383_);
v_a_430_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_419_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_419_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
v___jp_386_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_inc_ref(v_params_385_);
v___x_390_ = l_Array_toSubarray___redArg(v_params_385_, v_lower_388_, v_upper_389_);
v___x_391_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v___x_390_, v___y_387_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; 
v_unused_399_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_399_);
v___x_393_ = v___x_391_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_dec(v___x_391_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___y_387_);
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___y_387_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
return v___x_391_;
}
}
}
default: 
{
lean_object* v_fvarId_438_; lean_object* v_args_439_; lean_object* v___x_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_461_; 
v_fvarId_438_ = lean_ctor_get(v_e_359_, 0);
lean_inc(v_fvarId_438_);
v_args_439_ = lean_ctor_get(v_e_359_, 1);
lean_inc_ref(v_args_439_);
lean_dec_ref_known(v_e_359_, 2);
v___x_440_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_438_, v_a_360_, v_a_361_);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v___x_440_, 0);
lean_dec(v_unused_462_);
v___x_442_ = v___x_440_;
v_isShared_443_ = v_isSharedCheck_461_;
goto v_resetjp_441_;
}
else
{
lean_dec(v___x_440_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_461_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_array_get_size(v_args_439_);
v___x_446_ = lean_box(0);
v___x_447_ = lean_nat_dec_lt(v___x_444_, v___x_445_);
if (v___x_447_ == 0)
{
lean_object* v___x_449_; 
lean_dec_ref(v_args_439_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_446_);
v___x_449_ = v___x_442_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_446_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
else
{
uint8_t v___x_451_; 
v___x_451_ = lean_nat_dec_le(v___x_445_, v___x_445_);
if (v___x_451_ == 0)
{
if (v___x_447_ == 0)
{
lean_object* v___x_453_; 
lean_dec_ref(v_args_439_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_446_);
v___x_453_ = v___x_442_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_446_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
else
{
size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; 
lean_del_object(v___x_442_);
v___x_455_ = ((size_t)0ULL);
v___x_456_ = lean_usize_of_nat(v___x_445_);
v___x_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_439_, v___x_455_, v___x_456_, v___x_446_, v_a_360_, v_a_361_);
lean_dec_ref(v_args_439_);
return v___x_457_;
}
}
else
{
size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; 
lean_del_object(v___x_442_);
v___x_458_ = ((size_t)0ULL);
v___x_459_ = lean_usize_of_nat(v___x_445_);
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_439_, v___x_458_, v___x_459_, v___x_446_, v_a_360_, v_a_361_);
lean_dec_ref(v_args_439_);
return v___x_460_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object* v_e_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_e_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object* v_as_472_, size_t v_i_473_, size_t v_stop_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_472_, v_i_473_, v_stop_474_, v_b_475_, v___y_476_, v___y_477_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object* v_as_484_, lean_object* v_i_485_, lean_object* v_stop_486_, lean_object* v_b_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
size_t v_i_boxed_495_; size_t v_stop_boxed_496_; lean_object* v_res_497_; 
v_i_boxed_495_ = lean_unbox_usize(v_i_485_);
lean_dec(v_i_485_);
v_stop_boxed_496_ = lean_unbox_usize(v_stop_486_);
lean_dec(v_stop_486_);
v_res_497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(v_as_484_, v_i_boxed_495_, v_stop_boxed_496_, v_b_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec_ref(v_as_484_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object* v_as_498_, size_t v_sz_499_, size_t v_i_500_, lean_object* v_b_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_498_, v_sz_499_, v_i_500_, v_b_501_, v___y_502_, v___y_503_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object* v_as_510_, lean_object* v_sz_511_, lean_object* v_i_512_, lean_object* v_b_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
size_t v_sz_boxed_521_; size_t v_i_boxed_522_; lean_object* v_res_523_; 
v_sz_boxed_521_ = lean_unbox_usize(v_sz_511_);
lean_dec(v_sz_511_);
v_i_boxed_522_ = lean_unbox_usize(v_i_512_);
lean_dec(v_i_512_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(v_as_510_, v_sz_boxed_521_, v_i_boxed_522_, v_b_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec_ref(v_as_510_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object* v_inst_524_, lean_object* v_R_525_, lean_object* v_a_526_, lean_object* v_b_527_, lean_object* v_c_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_526_, v_b_527_, v___y_529_, v___y_530_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object* v_inst_537_, lean_object* v_R_538_, lean_object* v_a_539_, lean_object* v_b_540_, lean_object* v_c_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(v_inst_537_, v_R_538_, v_a_539_, v_b_540_, v_c_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object* v_inst_550_, lean_object* v_R_551_, lean_object* v_a_552_, lean_object* v_b_553_, lean_object* v_c_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_552_, v_b_553_, v___y_555_, v___y_556_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object* v_inst_563_, lean_object* v_R_564_, lean_object* v_a_565_, lean_object* v_b_566_, lean_object* v_c_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(v_inst_563_, v_R_564_, v_a_565_, v_b_566_, v_c_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object* v_code_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_decl_585_; lean_object* v_k_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; 
switch(lean_obj_tag(v_code_576_))
{
case 0:
{
lean_object* v_decl_596_; lean_object* v_k_597_; lean_object* v_value_598_; lean_object* v___x_599_; 
v_decl_596_ = lean_ctor_get(v_code_576_, 0);
lean_inc_ref(v_decl_596_);
v_k_597_ = lean_ctor_get(v_code_576_, 1);
lean_inc_ref(v_k_597_);
lean_dec_ref_known(v_code_576_, 2);
v_value_598_ = lean_ctor_get(v_decl_596_, 3);
lean_inc(v_value_598_);
lean_dec_ref(v_decl_596_);
v___x_599_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_value_598_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_dec_ref_known(v___x_599_, 1);
v_code_576_ = v_k_597_;
goto _start;
}
else
{
lean_dec_ref(v_k_597_);
return v___x_599_;
}
}
case 3:
{
lean_object* v_args_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_args_601_ = lean_ctor_get(v_code_576_, 1);
lean_inc_ref(v_args_601_);
lean_dec_ref_known(v_code_576_, 2);
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_array_get_size(v_args_601_);
v___x_604_ = lean_box(0);
v___x_605_ = lean_nat_dec_lt(v___x_602_, v___x_603_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
lean_dec_ref(v_args_601_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
return v___x_606_;
}
else
{
uint8_t v___x_607_; 
v___x_607_ = lean_nat_dec_le(v___x_603_, v___x_603_);
if (v___x_607_ == 0)
{
if (v___x_605_ == 0)
{
lean_object* v___x_608_; 
lean_dec_ref(v_args_601_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_604_);
return v___x_608_;
}
else
{
size_t v___x_609_; size_t v___x_610_; lean_object* v___x_611_; 
v___x_609_ = ((size_t)0ULL);
v___x_610_ = lean_usize_of_nat(v___x_603_);
v___x_611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_601_, v___x_609_, v___x_610_, v___x_604_, v_a_577_, v_a_578_);
lean_dec_ref(v_args_601_);
return v___x_611_;
}
}
else
{
size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; 
v___x_612_ = ((size_t)0ULL);
v___x_613_ = lean_usize_of_nat(v___x_603_);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_601_, v___x_612_, v___x_613_, v___x_604_, v_a_577_, v_a_578_);
lean_dec_ref(v_args_601_);
return v___x_614_;
}
}
}
case 4:
{
lean_object* v_cases_615_; lean_object* v_discr_616_; lean_object* v_alts_617_; lean_object* v___x_618_; 
v_cases_615_ = lean_ctor_get(v_code_576_, 0);
lean_inc_ref(v_cases_615_);
lean_dec_ref_known(v_code_576_, 1);
v_discr_616_ = lean_ctor_get(v_cases_615_, 2);
lean_inc(v_discr_616_);
v_alts_617_ = lean_ctor_get(v_cases_615_, 3);
lean_inc_ref(v_alts_617_);
lean_dec_ref(v_cases_615_);
v___x_618_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_discr_616_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_639_; 
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v___x_618_, 0);
lean_dec(v_unused_640_);
v___x_620_ = v___x_618_;
v_isShared_621_ = v_isSharedCheck_639_;
goto v_resetjp_619_;
}
else
{
lean_dec(v___x_618_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_639_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_array_get_size(v_alts_617_);
v___x_624_ = lean_box(0);
v___x_625_ = lean_nat_dec_lt(v___x_622_, v___x_623_);
if (v___x_625_ == 0)
{
lean_object* v___x_627_; 
lean_dec_ref(v_alts_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_624_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
else
{
uint8_t v___x_629_; 
v___x_629_ = lean_nat_dec_le(v___x_623_, v___x_623_);
if (v___x_629_ == 0)
{
if (v___x_625_ == 0)
{
lean_object* v___x_631_; 
lean_dec_ref(v_alts_617_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_624_);
v___x_631_ = v___x_620_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_624_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
size_t v___x_633_; size_t v___x_634_; lean_object* v___x_635_; 
lean_del_object(v___x_620_);
v___x_633_ = ((size_t)0ULL);
v___x_634_ = lean_usize_of_nat(v___x_623_);
v___x_635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_617_, v___x_633_, v___x_634_, v___x_624_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec_ref(v_alts_617_);
return v___x_635_;
}
}
else
{
size_t v___x_636_; size_t v___x_637_; lean_object* v___x_638_; 
lean_del_object(v___x_620_);
v___x_636_ = ((size_t)0ULL);
v___x_637_ = lean_usize_of_nat(v___x_623_);
v___x_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_617_, v___x_636_, v___x_637_, v___x_624_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec_ref(v_alts_617_);
return v___x_638_;
}
}
}
}
else
{
lean_dec_ref(v_alts_617_);
return v___x_618_;
}
}
case 5:
{
lean_object* v_fvarId_641_; lean_object* v___x_642_; 
v_fvarId_641_ = lean_ctor_get(v_code_576_, 0);
lean_inc(v_fvarId_641_);
lean_dec_ref_known(v_code_576_, 1);
v___x_642_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_641_, v_a_577_, v_a_578_);
return v___x_642_;
}
case 6:
{
lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_650_; 
v_isSharedCheck_650_ = !lean_is_exclusive(v_code_576_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_code_576_, 0);
lean_dec(v_unused_651_);
v___x_644_ = v_code_576_;
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
else
{
lean_dec(v_code_576_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_646_ = lean_box(0);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 0);
lean_ctor_set(v___x_644_, 0, v___x_646_);
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
default: 
{
lean_object* v_decl_652_; lean_object* v_k_653_; 
v_decl_652_ = lean_ctor_get(v_code_576_, 0);
lean_inc_ref(v_decl_652_);
v_k_653_ = lean_ctor_get(v_code_576_, 1);
lean_inc_ref(v_k_653_);
lean_dec_ref(v_code_576_);
v_decl_585_ = v_decl_652_;
v_k_586_ = v_k_653_;
v___y_587_ = v_a_577_;
v___y_588_ = v_a_578_;
v___y_589_ = v_a_579_;
v___y_590_ = v_a_580_;
v___y_591_ = v_a_581_;
v___y_592_ = v_a_582_;
goto v___jp_584_;
}
}
v___jp_584_:
{
lean_object* v_value_593_; lean_object* v___x_594_; 
v_value_593_ = lean_ctor_get(v_decl_585_, 4);
lean_inc_ref(v_value_593_);
lean_dec_ref(v_decl_585_);
v___x_594_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_value_593_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_dec_ref_known(v___x_594_, 1);
v_code_576_ = v_k_586_;
v_a_577_ = v___y_587_;
v_a_578_ = v___y_588_;
v_a_579_ = v___y_589_;
v_a_580_ = v___y_590_;
v_a_581_ = v___y_591_;
v_a_582_ = v___y_592_;
goto _start;
}
else
{
lean_dec_ref(v_k_586_);
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object* v_as_654_, size_t v_i_655_, size_t v_stop_656_, lean_object* v_b_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___y_666_; uint8_t v___x_672_; 
v___x_672_ = lean_usize_dec_eq(v_i_655_, v_stop_656_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
v___x_673_ = lean_array_uget_borrowed(v_as_654_, v_i_655_);
switch(lean_obj_tag(v___x_673_))
{
case 0:
{
lean_object* v_code_674_; 
v_code_674_ = lean_ctor_get(v___x_673_, 2);
lean_inc_ref(v_code_674_);
v___y_666_ = v_code_674_;
goto v___jp_665_;
}
case 1:
{
lean_object* v_code_675_; 
v_code_675_ = lean_ctor_get(v___x_673_, 1);
lean_inc_ref(v_code_675_);
v___y_666_ = v_code_675_;
goto v___jp_665_;
}
default: 
{
lean_object* v_code_676_; 
v_code_676_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_code_676_);
v___y_666_ = v_code_676_;
goto v___jp_665_;
}
}
}
else
{
lean_object* v___x_677_; 
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v_b_657_);
return v___x_677_;
}
v___jp_665_:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Compiler_LCNF_FindUsed_visit(v___y_666_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; size_t v___x_669_; size_t v___x_670_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_add(v_i_655_, v___x_669_);
v_i_655_ = v___x_670_;
v_b_657_ = v_a_668_;
goto _start;
}
else
{
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object* v_as_678_, lean_object* v_i_679_, lean_object* v_stop_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
size_t v_i_boxed_689_; size_t v_stop_boxed_690_; lean_object* v_res_691_; 
v_i_boxed_689_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_stop_boxed_690_ = lean_unbox_usize(v_stop_680_);
lean_dec(v_stop_680_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_as_678_, v_i_boxed_689_, v_stop_boxed_690_, v_b_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec_ref(v_as_678_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object* v_code_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_code_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(lean_object* v_f_701_, lean_object* v_v_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
if (lean_obj_tag(v_v_702_) == 0)
{
lean_object* v_code_710_; lean_object* v___x_711_; 
v_code_710_ = lean_ctor_get(v_v_702_, 0);
lean_inc_ref(v_code_710_);
lean_dec_ref_known(v_v_702_, 1);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
v___x_711_ = lean_apply_8(v_f_701_, v_code_710_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
return v___x_711_;
}
else
{
lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v_f_701_);
v_isSharedCheck_719_ = !lean_is_exclusive(v_v_702_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v_v_702_, 0);
lean_dec(v_unused_720_);
v___x_713_ = v_v_702_;
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
else
{
lean_dec(v_v_702_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_719_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_715_ = lean_box(0);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 0);
lean_ctor_set(v___x_713_, 0, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg___boxed(lean_object* v_f_721_, lean_object* v_v_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_721_, v_v_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(uint8_t v_pu_731_, lean_object* v_f_732_, lean_object* v_v_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_732_, v_v_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___boxed(lean_object* v_pu_742_, lean_object* v_f_743_, lean_object* v_v_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
uint8_t v_pu_boxed_752_; lean_object* v_res_753_; 
v_pu_boxed_752_ = lean_unbox(v_pu_742_);
v_res_753_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(v_pu_boxed_752_, v_f_743_, v_v_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object* v_as_754_, size_t v_i_755_, size_t v_stop_756_, lean_object* v_b_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = lean_usize_dec_eq(v_i_755_, v_stop_756_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v_fvarId_760_; lean_object* v___x_761_; size_t v___x_762_; size_t v___x_763_; 
v___x_759_ = lean_array_uget_borrowed(v_as_754_, v_i_755_);
v_fvarId_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_fvarId_760_);
v___x_761_ = l_Lean_FVarIdSet_insert(v_b_757_, v_fvarId_760_);
v___x_762_ = ((size_t)1ULL);
v___x_763_ = lean_usize_add(v_i_755_, v___x_762_);
v_i_755_ = v___x_763_;
v_b_757_ = v___x_761_;
goto _start;
}
else
{
return v_b_757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object* v_as_765_, lean_object* v_i_766_, lean_object* v_stop_767_, lean_object* v_b_768_){
_start:
{
size_t v_i_boxed_769_; size_t v_stop_boxed_770_; lean_object* v_res_771_; 
v_i_boxed_769_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_stop_boxed_770_ = lean_unbox_usize(v_stop_767_);
lean_dec(v_stop_767_);
v_res_771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_as_765_, v_i_boxed_769_, v_stop_boxed_770_, v_b_768_);
lean_dec_ref(v_as_765_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object* v_decl_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_toSignature_779_; lean_object* v_value_780_; lean_object* v_params_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___y_785_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_toSignature_779_ = lean_ctor_get(v_decl_773_, 0);
v_value_780_ = lean_ctor_get(v_decl_773_, 1);
lean_inc_ref(v_value_780_);
v_params_781_ = lean_ctor_get(v_toSignature_779_, 3);
v___x_782_ = lean_box(1);
v___x_783_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = lean_array_get_size(v_params_781_);
v___x_809_ = lean_nat_dec_lt(v___x_807_, v___x_808_);
if (v___x_809_ == 0)
{
v___y_785_ = v___x_782_;
goto v___jp_784_;
}
else
{
uint8_t v___x_810_; 
v___x_810_ = lean_nat_dec_le(v___x_808_, v___x_808_);
if (v___x_810_ == 0)
{
if (v___x_809_ == 0)
{
v___y_785_ = v___x_782_;
goto v___jp_784_;
}
else
{
size_t v___x_811_; size_t v___x_812_; lean_object* v___x_813_; 
v___x_811_ = ((size_t)0ULL);
v___x_812_ = lean_usize_of_nat(v___x_808_);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_781_, v___x_811_, v___x_812_, v___x_782_);
v___y_785_ = v___x_813_;
goto v___jp_784_;
}
}
else
{
size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; 
v___x_814_ = ((size_t)0ULL);
v___x_815_ = lean_usize_of_nat(v___x_808_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_781_, v___x_814_, v___x_815_, v___x_782_);
v___y_785_ = v___x_816_;
goto v___jp_784_;
}
}
v___jp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_786_ = lean_st_mk_ref(v___x_783_);
v___x_787_ = ((lean_object*)(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0));
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v_decl_773_);
lean_ctor_set(v___x_788_, 1, v___y_785_);
v___x_789_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v___x_787_, v_value_780_, v___x_788_, v___x_786_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec_ref_known(v___x_788_, 2);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; 
v_unused_798_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_798_);
v___x_791_ = v___x_789_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_dec(v___x_789_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_st_ref_get(v___x_786_);
lean_dec(v___x_786_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v___x_786_);
v_a_799_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_789_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_789_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(lean_object* v_decl_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
return v_res_823_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0(void){
_start:
{
uint8_t v___x_824_; lean_object* v___x_825_; 
v___x_824_ = 0;
v___x_825_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object* v_msg_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0);
v___x_828_ = lean_panic_fn_borrowed(v___x_827_, v_msg_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(lean_object* v_args_829_, lean_object* v_upperBound_830_, lean_object* v___x_831_, lean_object* v_a_832_, lean_object* v_b_833_){
_start:
{
lean_object* v_a_836_; uint8_t v___x_843_; 
v___x_843_ = lean_nat_dec_lt(v_a_832_, v_upperBound_830_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec(v_a_832_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_b_833_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = lean_array_get_size(v___x_831_);
v___x_846_ = lean_nat_dec_lt(v_a_832_, v___x_845_);
if (v___x_846_ == 0)
{
goto v___jp_840_;
}
else
{
lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_847_ = lean_array_fget_borrowed(v___x_831_, v_a_832_);
v___x_848_ = lean_unbox(v___x_847_);
if (v___x_848_ == 0)
{
v_a_836_ = v_b_833_;
goto v___jp_835_;
}
else
{
goto v___jp_840_;
}
}
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_add(v_a_832_, v___x_837_);
lean_dec(v_a_832_);
v_a_832_ = v___x_838_;
v_b_833_ = v_a_836_;
goto _start;
}
v___jp_840_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_array_fget_borrowed(v_args_829_, v_a_832_);
lean_inc(v___x_841_);
v___x_842_ = lean_array_push(v_b_833_, v___x_841_);
v_a_836_ = v___x_842_;
goto v___jp_835_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(lean_object* v_args_849_, lean_object* v_upperBound_850_, lean_object* v___x_851_, lean_object* v_a_852_, lean_object* v_b_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_849_, v_upperBound_850_, v___x_851_, v_a_852_, v_b_853_);
lean_dec_ref(v___x_851_);
lean_dec(v_upperBound_850_);
lean_dec_ref(v_args_849_);
return v_res_855_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_859_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2));
v___x_860_ = lean_unsigned_to_nat(9u);
v___x_861_ = lean_unsigned_to_nat(650u);
v___x_862_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1));
v___x_863_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0));
v___x_864_ = l_mkPanicMessageWithDecl(v___x_863_, v___x_862_, v___x_861_, v___x_860_, v___x_859_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* v_code_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_decl_879_; lean_object* v_k_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; 
switch(lean_obj_tag(v_code_871_))
{
case 0:
{
lean_object* v_decl_993_; lean_object* v_k_994_; lean_object* v_argsNew_996_; lean_object* v___y_997_; lean_object* v_auxDeclName_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v_value_1055_; 
v_decl_993_ = lean_ctor_get(v_code_871_, 0);
v_k_994_ = lean_ctor_get(v_code_871_, 1);
v_value_1055_ = lean_ctor_get(v_decl_993_, 3);
if (lean_obj_tag(v_value_1055_) == 3)
{
lean_object* v_declName_1056_; lean_object* v_args_1057_; lean_object* v_declName_1058_; lean_object* v_auxDeclName_1059_; lean_object* v_paramMask_1060_; uint8_t v_allUnused_1061_; uint8_t v___x_1062_; 
v_declName_1056_ = lean_ctor_get(v_value_1055_, 0);
v_args_1057_ = lean_ctor_get(v_value_1055_, 2);
v_declName_1058_ = lean_ctor_get(v_a_872_, 0);
v_auxDeclName_1059_ = lean_ctor_get(v_a_872_, 1);
v_paramMask_1060_ = lean_ctor_get(v_a_872_, 2);
v_allUnused_1061_ = lean_ctor_get_uint8(v_a_872_, sizeof(void*)*3);
v___x_1062_ = lean_name_eq(v_declName_1056_, v_declName_1058_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
lean_inc_ref(v_k_994_);
v___x_1063_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_994_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1100_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1100_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1100_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
size_t v___x_1068_; size_t v___x_1069_; uint8_t v___x_1070_; 
v___x_1068_ = lean_ptr_addr(v_k_994_);
v___x_1069_ = lean_ptr_addr(v_a_1064_);
v___x_1070_ = lean_usize_dec_eq(v___x_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1080_; 
lean_inc_ref(v_decl_993_);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; lean_object* v_unused_1082_; 
v_unused_1081_ = lean_ctor_get(v_code_871_, 1);
lean_dec(v_unused_1081_);
v_unused_1082_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_1082_);
v___x_1072_ = v_code_871_;
v_isShared_1073_ = v_isSharedCheck_1080_;
goto v_resetjp_1071_;
}
else
{
lean_dec(v_code_871_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1080_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v_a_1064_);
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_decl_993_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_a_1064_);
v___x_1075_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1077_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1075_);
v___x_1077_ = v___x_1066_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
size_t v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = lean_ptr_addr(v_decl_993_);
v___x_1084_ = lean_usize_dec_eq(v___x_1083_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1094_; 
lean_inc_ref(v_decl_993_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; 
v_unused_1095_ = lean_ctor_get(v_code_871_, 1);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_1096_);
v___x_1086_ = v_code_871_;
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
else
{
lean_dec(v_code_871_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 1, v_a_1064_);
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_decl_993_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_a_1064_);
v___x_1089_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1089_);
v___x_1091_ = v___x_1066_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v___x_1098_; 
lean_dec(v_a_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v_code_871_);
v___x_1098_ = v___x_1066_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_code_871_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_871_, 2);
return v___x_1063_;
}
}
else
{
if (v_allUnused_1061_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1101_ = lean_array_get_size(v_args_1057_);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_1104_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1057_, v___x_1101_, v_paramMask_1060_, v___x_1102_, v___x_1103_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v_argsNew_996_ = v_a_1105_;
v___y_997_ = v_a_872_;
v_auxDeclName_998_ = v_auxDeclName_1059_;
v___y_999_ = v_a_873_;
v___y_1000_ = v_a_874_;
v___y_1001_ = v_a_875_;
v___y_1002_ = v_a_876_;
goto v___jp_995_;
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref_known(v_code_871_, 2);
v_a_1106_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1104_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1114_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5));
v___x_1115_ = lean_array_get_size(v_paramMask_1060_);
v___x_1116_ = lean_array_get_size(v_args_1057_);
v___x_1117_ = l_Array_extract___redArg(v_args_1057_, v___x_1115_, v___x_1116_);
v___x_1118_ = l_Array_append___redArg(v___x_1114_, v___x_1117_);
lean_dec_ref(v___x_1117_);
v_argsNew_996_ = v___x_1118_;
v___y_997_ = v_a_872_;
v_auxDeclName_998_ = v_auxDeclName_1059_;
v___y_999_ = v_a_873_;
v___y_1000_ = v_a_874_;
v___y_1001_ = v_a_875_;
v___y_1002_ = v_a_876_;
goto v___jp_995_;
}
}
}
else
{
lean_object* v___x_1119_; 
lean_inc_ref(v_k_994_);
v___x_1119_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_994_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1156_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1156_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1156_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
size_t v___x_1124_; size_t v___x_1125_; uint8_t v___x_1126_; 
v___x_1124_ = lean_ptr_addr(v_k_994_);
v___x_1125_ = lean_ptr_addr(v_a_1120_);
v___x_1126_ = lean_usize_dec_eq(v___x_1124_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1136_; 
lean_inc_ref(v_decl_993_);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; lean_object* v_unused_1138_; 
v_unused_1137_ = lean_ctor_get(v_code_871_, 1);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_1138_);
v___x_1128_ = v_code_871_;
v_isShared_1129_ = v_isSharedCheck_1136_;
goto v_resetjp_1127_;
}
else
{
lean_dec(v_code_871_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1136_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 1, v_a_1120_);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_decl_993_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_a_1120_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1131_);
v___x_1133_ = v___x_1122_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
size_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_ptr_addr(v_decl_993_);
v___x_1140_ = lean_usize_dec_eq(v___x_1139_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1150_; 
lean_inc_ref(v_decl_993_);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1151_ = lean_ctor_get(v_code_871_, 1);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_1152_);
v___x_1142_ = v_code_871_;
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
else
{
lean_dec(v_code_871_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_a_1120_);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_decl_993_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_a_1120_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1145_);
v___x_1147_ = v___x_1122_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
else
{
lean_object* v___x_1154_; 
lean_dec(v_a_1120_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v_code_871_);
v___x_1154_ = v___x_1122_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_code_871_);
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
else
{
lean_dec_ref_known(v_code_871_, 2);
return v___x_1119_;
}
}
v___jp_995_:
{
uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1003_ = 0;
v___x_1004_ = lean_box(0);
lean_inc(v_auxDeclName_998_);
v___x_1005_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1005_, 0, v_auxDeclName_998_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
lean_ctor_set(v___x_1005_, 2, v_argsNew_996_);
lean_inc_ref(v_decl_993_);
v___x_1006_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1003_, v_decl_993_, v___x_1005_, v___y_1000_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
lean_inc_ref(v_k_994_);
v___x_1008_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_994_, v___y_997_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1046_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1046_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1046_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
size_t v___x_1013_; size_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1013_ = lean_ptr_addr(v_k_994_);
v___x_1014_ = lean_ptr_addr(v_a_1009_);
v___x_1015_ = lean_usize_dec_eq(v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1025_; 
v_isSharedCheck_1025_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; lean_object* v_unused_1027_; 
v_unused_1026_ = lean_ctor_get(v_code_871_, 1);
lean_dec(v_unused_1026_);
v_unused_1027_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_1027_);
v___x_1017_ = v_code_871_;
v_isShared_1018_ = v_isSharedCheck_1025_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v_code_871_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1025_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 1, v_a_1009_);
lean_ctor_set(v___x_1017_, 0, v_a_1007_);
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1007_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_a_1009_);
v___x_1020_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1022_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1020_);
v___x_1022_ = v___x_1011_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
size_t v___x_1028_; size_t v___x_1029_; uint8_t v___x_1030_; 
v___x_1028_ = lean_ptr_addr(v_decl_993_);
v___x_1029_ = lean_ptr_addr(v_a_1007_);
v___x_1030_ = lean_usize_dec_eq(v___x_1028_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1040_; 
v_isSharedCheck_1040_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; lean_object* v_unused_1042_; 
v_unused_1041_ = lean_ctor_get(v_code_871_, 1);
lean_dec(v_unused_1041_);
v_unused_1042_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_1042_);
v___x_1032_ = v_code_871_;
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
else
{
lean_dec(v_code_871_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1040_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v_a_1009_);
lean_ctor_set(v___x_1032_, 0, v_a_1007_);
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1007_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_a_1009_);
v___x_1035_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1035_);
v___x_1037_ = v___x_1011_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v___x_1044_; 
lean_dec(v_a_1009_);
lean_dec(v_a_1007_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_code_871_);
v___x_1044_ = v___x_1011_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_code_871_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
else
{
lean_dec(v_a_1007_);
lean_dec_ref_known(v_code_871_, 2);
return v___x_1008_;
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref_known(v_code_871_, 2);
v_a_1047_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1006_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1006_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1157_; lean_object* v_k_1158_; 
v_decl_1157_ = lean_ctor_get(v_code_871_, 0);
v_k_1158_ = lean_ctor_get(v_code_871_, 1);
lean_inc_ref(v_k_1158_);
lean_inc_ref(v_decl_1157_);
v_decl_879_ = v_decl_1157_;
v_k_880_ = v_k_1158_;
v___y_881_ = v_a_872_;
v___y_882_ = v_a_873_;
v___y_883_ = v_a_874_;
v___y_884_ = v_a_875_;
v___y_885_ = v_a_876_;
goto v___jp_878_;
}
case 2:
{
lean_object* v_decl_1159_; lean_object* v_k_1160_; 
v_decl_1159_ = lean_ctor_get(v_code_871_, 0);
v_k_1160_ = lean_ctor_get(v_code_871_, 1);
lean_inc_ref(v_k_1160_);
lean_inc_ref(v_decl_1159_);
v_decl_879_ = v_decl_1159_;
v_k_880_ = v_k_1160_;
v___y_881_ = v_a_872_;
v___y_882_ = v_a_873_;
v___y_883_ = v_a_874_;
v___y_884_ = v_a_875_;
v___y_885_ = v_a_876_;
goto v___jp_878_;
}
case 4:
{
lean_object* v_cases_1161_; lean_object* v_typeName_1162_; lean_object* v_resultType_1163_; lean_object* v_discr_1164_; lean_object* v_alts_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1204_; 
v_cases_1161_ = lean_ctor_get(v_code_871_, 0);
lean_inc_ref(v_cases_1161_);
v_typeName_1162_ = lean_ctor_get(v_cases_1161_, 0);
v_resultType_1163_ = lean_ctor_get(v_cases_1161_, 1);
v_discr_1164_ = lean_ctor_get(v_cases_1161_, 2);
v_alts_1165_ = lean_ctor_get(v_cases_1161_, 3);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_cases_1161_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1167_ = v_cases_1161_;
v_isShared_1168_ = v_isSharedCheck_1204_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_alts_1165_);
lean_inc(v_discr_1164_);
lean_inc(v_resultType_1163_);
lean_inc(v_typeName_1162_);
lean_dec(v_cases_1161_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1204_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1165_);
v___x_1170_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v___x_1169_, v_alts_1165_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1195_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1195_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1195_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
size_t v___x_1175_; size_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1175_ = lean_ptr_addr(v_alts_1165_);
lean_dec_ref(v_alts_1165_);
v___x_1176_ = lean_ptr_addr(v_a_1171_);
v___x_1177_ = lean_usize_dec_eq(v___x_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1190_; 
v_isSharedCheck_1190_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_1191_);
v___x_1179_ = v_code_871_;
v_isShared_1180_ = v_isSharedCheck_1190_;
goto v_resetjp_1178_;
}
else
{
lean_dec(v_code_871_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1190_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 3, v_a_1171_);
v___x_1182_ = v___x_1167_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_typeName_1162_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_resultType_1163_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_discr_1164_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_a_1171_);
v___x_1182_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1182_);
v___x_1184_ = v___x_1179_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1184_);
v___x_1186_ = v___x_1173_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
else
{
lean_object* v___x_1193_; 
lean_dec(v_a_1171_);
lean_del_object(v___x_1167_);
lean_dec(v_discr_1164_);
lean_dec_ref(v_resultType_1163_);
lean_dec(v_typeName_1162_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v_code_871_);
v___x_1193_ = v___x_1173_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_code_871_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_del_object(v___x_1167_);
lean_dec_ref(v_alts_1165_);
lean_dec(v_discr_1164_);
lean_dec_ref(v_resultType_1163_);
lean_dec(v_typeName_1162_);
lean_dec_ref_known(v_code_871_, 1);
v_a_1196_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1170_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1170_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
default: 
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_code_871_);
return v___x_1205_;
}
}
v___jp_878_:
{
lean_object* v_params_886_; lean_object* v_type_887_; lean_object* v_value_888_; lean_object* v___x_889_; 
v_params_886_ = lean_ctor_get(v_decl_879_, 2);
lean_inc_ref(v_params_886_);
v_type_887_ = lean_ctor_get(v_decl_879_, 3);
lean_inc_ref(v_type_887_);
v_value_888_ = lean_ctor_get(v_decl_879_, 4);
lean_inc_ref(v_value_888_);
v___x_889_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_value_888_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; uint8_t v___x_891_; lean_object* v___x_892_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_891_ = 0;
v___x_892_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_891_, v_decl_879_, v_type_887_, v_params_886_, v_a_890_, v___y_883_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
if (lean_obj_tag(v___x_894_) == 0)
{
switch(lean_obj_tag(v_code_871_))
{
case 1:
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_934_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_934_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_934_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_934_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_decl_899_; lean_object* v_k_900_; size_t v___x_901_; size_t v___x_902_; uint8_t v___x_903_; 
v_decl_899_ = lean_ctor_get(v_code_871_, 0);
v_k_900_ = lean_ctor_get(v_code_871_, 1);
v___x_901_ = lean_ptr_addr(v_k_900_);
v___x_902_ = lean_ptr_addr(v_a_895_);
v___x_903_ = lean_usize_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_913_; 
v_isSharedCheck_913_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; lean_object* v_unused_915_; 
v_unused_914_ = lean_ctor_get(v_code_871_, 1);
lean_dec(v_unused_914_);
v_unused_915_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_915_);
v___x_905_ = v_code_871_;
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
else
{
lean_dec(v_code_871_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_913_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v_a_895_);
lean_ctor_set(v___x_905_, 0, v_a_893_);
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_893_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_a_895_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_908_);
v___x_910_ = v___x_897_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
size_t v___x_916_; size_t v___x_917_; uint8_t v___x_918_; 
v___x_916_ = lean_ptr_addr(v_decl_899_);
v___x_917_ = lean_ptr_addr(v_a_893_);
v___x_918_ = lean_usize_dec_eq(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_928_; 
v_isSharedCheck_928_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; lean_object* v_unused_930_; 
v_unused_929_ = lean_ctor_get(v_code_871_, 1);
lean_dec(v_unused_929_);
v_unused_930_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_930_);
v___x_920_ = v_code_871_;
v_isShared_921_ = v_isSharedCheck_928_;
goto v_resetjp_919_;
}
else
{
lean_dec(v_code_871_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_928_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 1, v_a_895_);
lean_ctor_set(v___x_920_, 0, v_a_893_);
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_893_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_a_895_);
v___x_923_ = v_reuseFailAlloc_927_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_923_);
v___x_925_ = v___x_897_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v___x_932_; 
lean_dec(v_a_895_);
lean_dec(v_a_893_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_code_871_);
v___x_932_ = v___x_897_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_code_871_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
case 2:
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_974_; 
v_a_935_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_974_ == 0)
{
v___x_937_ = v___x_894_;
v_isShared_938_ = v_isSharedCheck_974_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_894_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_974_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_decl_939_; lean_object* v_k_940_; size_t v___x_941_; size_t v___x_942_; uint8_t v___x_943_; 
v_decl_939_ = lean_ctor_get(v_code_871_, 0);
v_k_940_ = lean_ctor_get(v_code_871_, 1);
v___x_941_ = lean_ptr_addr(v_k_940_);
v___x_942_ = lean_ptr_addr(v_a_935_);
v___x_943_ = lean_usize_dec_eq(v___x_941_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_953_; 
v_isSharedCheck_953_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; lean_object* v_unused_955_; 
v_unused_954_ = lean_ctor_get(v_code_871_, 1);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_955_);
v___x_945_ = v_code_871_;
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
else
{
lean_dec(v_code_871_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v_a_935_);
lean_ctor_set(v___x_945_, 0, v_a_893_);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_893_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_a_935_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_948_);
v___x_950_ = v___x_937_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
size_t v___x_956_; size_t v___x_957_; uint8_t v___x_958_; 
v___x_956_ = lean_ptr_addr(v_decl_939_);
v___x_957_ = lean_ptr_addr(v_a_893_);
v___x_958_ = lean_usize_dec_eq(v___x_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_968_; 
v_isSharedCheck_968_ = !lean_is_exclusive(v_code_871_);
if (v_isSharedCheck_968_ == 0)
{
lean_object* v_unused_969_; lean_object* v_unused_970_; 
v_unused_969_ = lean_ctor_get(v_code_871_, 1);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v_code_871_, 0);
lean_dec(v_unused_970_);
v___x_960_ = v_code_871_;
v_isShared_961_ = v_isSharedCheck_968_;
goto v_resetjp_959_;
}
else
{
lean_dec(v_code_871_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_968_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_a_935_);
lean_ctor_set(v___x_960_, 0, v_a_893_);
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_893_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_a_935_);
v___x_963_ = v_reuseFailAlloc_967_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_965_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_963_);
v___x_965_ = v___x_937_;
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
lean_dec(v_a_935_);
lean_dec(v_a_893_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_code_871_);
v___x_972_ = v___x_937_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_code_871_);
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
default: 
{
lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_a_893_);
lean_dec_ref(v_code_871_);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v___x_894_, 0);
lean_dec(v_unused_984_);
v___x_976_ = v___x_894_;
v_isShared_977_ = v_isSharedCheck_983_;
goto v_resetjp_975_;
}
else
{
lean_dec(v___x_894_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_983_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_978_ = lean_obj_once(&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3, &l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once, _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3);
v___x_979_ = l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(v___x_978_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_979_);
v___x_981_ = v___x_976_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
}
else
{
lean_dec(v_a_893_);
lean_dec_ref(v_code_871_);
return v___x_894_;
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v_k_880_);
lean_dec_ref(v_code_871_);
v_a_985_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_892_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_892_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_dec_ref(v_type_887_);
lean_dec_ref(v_params_886_);
lean_dec_ref(v_k_880_);
lean_dec_ref(v_decl_879_);
lean_dec_ref(v_code_871_);
return v___x_889_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(lean_object* v_i_1206_, lean_object* v_as_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = lean_array_get_size(v_as_1207_);
v___x_1215_ = lean_nat_dec_lt(v_i_1206_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_dec(v_i_1206_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v_as_1207_);
return v___x_1216_;
}
else
{
lean_object* v_a_1217_; lean_object* v___y_1219_; 
v_a_1217_ = lean_array_fget_borrowed(v_as_1207_, v_i_1206_);
switch(lean_obj_tag(v_a_1217_))
{
case 0:
{
lean_object* v_code_1241_; 
v_code_1241_ = lean_ctor_get(v_a_1217_, 2);
lean_inc_ref(v_code_1241_);
v___y_1219_ = v_code_1241_;
goto v___jp_1218_;
}
case 1:
{
lean_object* v_code_1242_; 
v_code_1242_ = lean_ctor_get(v_a_1217_, 1);
lean_inc_ref(v_code_1242_);
v___y_1219_ = v_code_1242_;
goto v___jp_1218_;
}
default: 
{
lean_object* v_code_1243_; 
v_code_1243_ = lean_ctor_get(v_a_1217_, 0);
lean_inc_ref(v_code_1243_);
v___y_1219_ = v_code_1243_;
goto v___jp_1218_;
}
}
v___jp_1218_:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v___y_1219_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1222_; size_t v___x_1223_; size_t v___x_1224_; uint8_t v___x_1225_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
lean_inc(v_a_1217_);
v___x_1222_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1217_, v_a_1221_);
v___x_1223_ = lean_ptr_addr(v_a_1217_);
v___x_1224_ = lean_ptr_addr(v___x_1222_);
v___x_1225_ = lean_usize_dec_eq(v___x_1223_, v___x_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_add(v_i_1206_, v___x_1226_);
v___x_1228_ = lean_array_fset(v_as_1207_, v_i_1206_, v___x_1222_);
lean_dec(v_i_1206_);
v_i_1206_ = v___x_1227_;
v_as_1207_ = v___x_1228_;
goto _start;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec_ref(v___x_1222_);
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = lean_nat_add(v_i_1206_, v___x_1230_);
lean_dec(v_i_1206_);
v_i_1206_ = v___x_1231_;
goto _start;
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v_as_1207_);
lean_dec(v_i_1206_);
v_a_1233_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1220_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1220_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(lean_object* v_i_1244_, lean_object* v_as_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v_i_1244_, v_as_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec_ref(v___y_1246_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object* v_code_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_code_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec_ref(v_a_1254_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object* v_args_1261_, lean_object* v_upperBound_1262_, lean_object* v___x_1263_, lean_object* v_inst_1264_, lean_object* v_R_1265_, lean_object* v_a_1266_, lean_object* v_b_1267_, lean_object* v_c_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1261_, v_upperBound_1262_, v___x_1263_, v_a_1266_, v_b_1267_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object* v_args_1276_, lean_object* v_upperBound_1277_, lean_object* v___x_1278_, lean_object* v_inst_1279_, lean_object* v_R_1280_, lean_object* v_a_1281_, lean_object* v_b_1282_, lean_object* v_c_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(v_args_1276_, v_upperBound_1277_, v___x_1278_, v_inst_1279_, v_R_1280_, v_a_1281_, v_b_1282_, v_c_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec_ref(v___x_1278_);
lean_dec(v_upperBound_1277_);
lean_dec_ref(v_args_1276_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object* v_f_1291_, lean_object* v_v_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
if (lean_obj_tag(v_v_1292_) == 0)
{
lean_object* v_code_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1323_; 
v_code_1299_ = lean_ctor_get(v_v_1292_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_v_1292_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1301_ = v_v_1292_;
v_isShared_1302_ = v_isSharedCheck_1323_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_code_1299_);
lean_dec(v_v_1292_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1323_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; 
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
lean_inc_ref(v___y_1293_);
v___x_1303_ = lean_apply_7(v_f_1291_, v_code_1299_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, lean_box(0));
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1314_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v_a_1304_);
v___x_1309_ = v___x_1301_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1311_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1309_);
v___x_1311_ = v___x_1306_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_del_object(v___x_1301_);
v_a_1315_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1303_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1303_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
else
{
lean_object* v___x_1324_; 
lean_dec_ref(v_f_1291_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_v_1292_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object* v_f_1325_, lean_object* v_v_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1325_, v_v_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(uint8_t v_pu_1334_, lean_object* v_f_1335_, lean_object* v_v_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1335_, v_v_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object* v_pu_1344_, lean_object* v_f_1345_, lean_object* v_v_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v_pu_boxed_1353_; lean_object* v_res_1354_; 
v_pu_boxed_1353_ = lean_unbox(v_pu_1344_);
v_res_1354_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(v_pu_boxed_1353_, v_f_1345_, v_v_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1354_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1355_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
lean_ctor_set(v___x_1360_, 2, v___x_1359_);
lean_ctor_set(v___x_1360_, 3, v___x_1359_);
lean_ctor_set(v___x_1360_, 4, v___x_1358_);
lean_ctor_set(v___x_1360_, 5, v___x_1358_);
lean_ctor_set(v___x_1360_, 6, v___x_1358_);
lean_ctor_set(v___x_1360_, 7, v___x_1358_);
lean_ctor_set(v___x_1360_, 8, v___x_1358_);
lean_ctor_set(v___x_1360_, 9, v___x_1358_);
lean_ctor_set(v___x_1360_, 10, v___x_1358_);
return v___x_1360_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3(void){
_start:
{
lean_object* v___x_1361_; double v___x_1362_; 
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_float_of_nat(v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* v_cls_1366_, lean_object* v_msg_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_toCold_1373_; lean_object* v_ref_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_toCold_1373_ = lean_ctor_get(v___y_1370_, 0);
v_ref_1374_ = lean_ctor_get(v___y_1370_, 2);
v___x_1375_ = lean_st_ref_get(v___y_1371_);
v___x_1376_ = lean_st_ref_get(v___y_1369_);
v___x_1377_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1368_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1437_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1437_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1437_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_env_1382_; lean_object* v_lctx_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1435_; 
v_env_1382_ = lean_ctor_get(v___x_1375_, 0);
lean_inc_ref(v_env_1382_);
lean_dec(v___x_1375_);
v_lctx_1383_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v___x_1376_, 1);
lean_dec(v_unused_1436_);
v___x_1385_ = v___x_1376_;
v_isShared_1386_ = v_isSharedCheck_1435_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_lctx_1383_);
lean_dec(v___x_1376_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1435_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v_options_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_traceState_1390_; lean_object* v_env_1391_; lean_object* v_nextMacroScope_1392_; lean_object* v_ngen_1393_; lean_object* v_auxDeclNGen_1394_; lean_object* v_cache_1395_; lean_object* v_messages_1396_; lean_object* v_infoState_1397_; lean_object* v_snapshotTasks_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1434_; 
v_options_1387_ = lean_ctor_get(v_toCold_1373_, 2);
v___x_1388_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2);
v___x_1389_ = lean_st_ref_take(v___y_1371_);
v_traceState_1390_ = lean_ctor_get(v___x_1389_, 4);
v_env_1391_ = lean_ctor_get(v___x_1389_, 0);
v_nextMacroScope_1392_ = lean_ctor_get(v___x_1389_, 1);
v_ngen_1393_ = lean_ctor_get(v___x_1389_, 2);
v_auxDeclNGen_1394_ = lean_ctor_get(v___x_1389_, 3);
v_cache_1395_ = lean_ctor_get(v___x_1389_, 5);
v_messages_1396_ = lean_ctor_get(v___x_1389_, 6);
v_infoState_1397_ = lean_ctor_get(v___x_1389_, 7);
v_snapshotTasks_1398_ = lean_ctor_get(v___x_1389_, 8);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1400_ = v___x_1389_;
v_isShared_1401_ = v_isSharedCheck_1434_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_snapshotTasks_1398_);
lean_inc(v_infoState_1397_);
lean_inc(v_messages_1396_);
lean_inc(v_cache_1395_);
lean_inc(v_traceState_1390_);
lean_inc(v_auxDeclNGen_1394_);
lean_inc(v_ngen_1393_);
lean_inc(v_nextMacroScope_1392_);
lean_inc(v_env_1391_);
lean_dec(v___x_1389_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1434_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
uint64_t v_tid_1402_; lean_object* v_traces_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1433_; 
v_tid_1402_ = lean_ctor_get_uint64(v_traceState_1390_, sizeof(void*)*1);
v_traces_1403_ = lean_ctor_get(v_traceState_1390_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_traceState_1390_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1405_ = v_traceState_1390_;
v_isShared_1406_ = v_isSharedCheck_1433_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_traces_1403_);
lean_dec(v_traceState_1390_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1433_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1407_ = lean_unbox(v_a_1378_);
lean_dec(v_a_1378_);
v___x_1408_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1383_, v___x_1407_);
lean_dec_ref(v_lctx_1383_);
lean_inc_ref(v_options_1387_);
v___x_1409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1409_, 0, v_env_1382_);
lean_ctor_set(v___x_1409_, 1, v___x_1388_);
lean_ctor_set(v___x_1409_, 2, v___x_1408_);
lean_ctor_set(v___x_1409_, 3, v_options_1387_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set_tag(v___x_1385_, 3);
lean_ctor_set(v___x_1385_, 1, v_msg_1367_);
lean_ctor_set(v___x_1385_, 0, v___x_1409_);
v___x_1411_ = v___x_1385_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_msg_1367_);
v___x_1411_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; double v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1412_ = lean_box(0);
v___x_1413_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3);
v___x_1414_ = 0;
v___x_1415_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4));
v___x_1416_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1416_, 0, v_cls_1366_);
lean_ctor_set(v___x_1416_, 1, v___x_1412_);
lean_ctor_set(v___x_1416_, 2, v___x_1415_);
lean_ctor_set_float(v___x_1416_, sizeof(void*)*3, v___x_1413_);
lean_ctor_set_float(v___x_1416_, sizeof(void*)*3 + 8, v___x_1413_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*3 + 16, v___x_1414_);
v___x_1417_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5));
v___x_1418_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1411_);
lean_ctor_set(v___x_1418_, 2, v___x_1417_);
lean_inc(v_ref_1374_);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v_ref_1374_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = l_Lean_PersistentArray_push___redArg(v_traces_1403_, v___x_1419_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1420_);
v___x_1422_ = v___x_1405_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1420_);
lean_ctor_set_uint64(v_reuseFailAlloc_1431_, sizeof(void*)*1, v_tid_1402_);
v___x_1422_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1424_; 
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 4, v___x_1422_);
v___x_1424_ = v___x_1400_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_env_1391_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_nextMacroScope_1392_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_ngen_1393_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_auxDeclNGen_1394_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1430_, 5, v_cache_1395_);
lean_ctor_set(v_reuseFailAlloc_1430_, 6, v_messages_1396_);
lean_ctor_set(v_reuseFailAlloc_1430_, 7, v_infoState_1397_);
lean_ctor_set(v_reuseFailAlloc_1430_, 8, v_snapshotTasks_1398_);
v___x_1424_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v___x_1425_ = lean_st_ref_put(v___y_1371_, v___x_1424_);
v___x_1426_ = lean_box(0);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1426_);
v___x_1428_ = v___x_1380_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
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
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v___x_1376_);
lean_dec(v___x_1375_);
lean_dec_ref(v_msg_1367_);
lean_dec(v_cls_1366_);
v_a_1438_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1377_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1377_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___boxed(lean_object* v_cls_1446_, lean_object* v_msg_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v_cls_1446_, v_msg_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(lean_object* v_name_1455_, lean_object* v___x_1456_, lean_object* v___x_1457_, uint8_t v___x_1458_, lean_object* v_value_1459_, lean_object* v_code_1460_, uint8_t v_safe_1461_, uint8_t v_recursive_1462_, lean_object* v_inlineAttr_x3f_1463_, lean_object* v_params_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_inc(v___x_1456_);
v___x_1470_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1470_, 0, v_name_1455_);
lean_ctor_set(v___x_1470_, 1, v___x_1456_);
lean_ctor_set(v___x_1470_, 2, v___x_1457_);
lean_ctor_set_uint8(v___x_1470_, sizeof(void*)*3, v___x_1458_);
v___x_1471_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___closed__0));
v___x_1472_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v___x_1471_, v_value_1459_, v___x_1470_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec_ref_known(v___x_1470_, 3);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = 0;
v___x_1475_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_1474_, v_code_1460_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
lean_inc_ref(v_params_1464_);
v___x_1477_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_1474_, v_params_1464_, v_a_1476_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v_a_1476_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1480_, 0, v___x_1456_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
lean_ctor_set(v___x_1480_, 2, v_a_1478_);
lean_ctor_set(v___x_1480_, 3, v_params_1464_);
lean_ctor_set_uint8(v___x_1480_, sizeof(void*)*4, v_safe_1461_);
v___x_1481_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v_a_1473_);
lean_ctor_set(v___x_1481_, 2, v_inlineAttr_x3f_1463_);
lean_ctor_set_uint8(v___x_1481_, sizeof(void*)*3, v_recursive_1462_);
lean_inc_ref(v___x_1481_);
v___x_1482_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1481_, v___y_1468_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v___x_1482_, 0);
lean_dec(v_unused_1490_);
v___x_1484_ = v___x_1482_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_dec(v___x_1482_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1481_);
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1481_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref_known(v___x_1481_, 3);
v_a_1491_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1482_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1482_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_a_1473_);
lean_dec_ref(v_params_1464_);
lean_dec(v_inlineAttr_x3f_1463_);
lean_dec(v___x_1456_);
v_a_1499_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1477_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1477_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_a_1473_);
lean_dec_ref(v_params_1464_);
lean_dec(v_inlineAttr_x3f_1463_);
lean_dec(v___x_1456_);
v_a_1507_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1475_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1475_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v_params_1464_);
lean_dec(v_inlineAttr_x3f_1463_);
lean_dec_ref(v_code_1460_);
lean_dec(v___x_1456_);
v_a_1515_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1472_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1472_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed(lean_object* v_name_1523_, lean_object* v___x_1524_, lean_object* v___x_1525_, lean_object* v___x_1526_, lean_object* v_value_1527_, lean_object* v_code_1528_, lean_object* v_safe_1529_, lean_object* v_recursive_1530_, lean_object* v_inlineAttr_x3f_1531_, lean_object* v_params_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v___x_11818__boxed_1538_; uint8_t v_safe_boxed_1539_; uint8_t v_recursive_boxed_1540_; lean_object* v_res_1541_; 
v___x_11818__boxed_1538_ = lean_unbox(v___x_1526_);
v_safe_boxed_1539_ = lean_unbox(v_safe_1529_);
v_recursive_boxed_1540_ = lean_unbox(v_recursive_1530_);
v_res_1541_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(v_name_1523_, v___x_1524_, v___x_1525_, v___x_11818__boxed_1538_, v_value_1527_, v_code_1528_, v_safe_boxed_1539_, v_recursive_boxed_1540_, v_inlineAttr_x3f_1531_, v_params_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(lean_object* v___x_1548_, uint8_t v___x_1549_, lean_object* v_name_1550_, lean_object* v_levelParams_1551_, lean_object* v_type_1552_, lean_object* v_a_1553_, uint8_t v_safe_1554_, uint8_t v___x_1555_, lean_object* v_____r_1556_, lean_object* v_args_1557_, uint8_t v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1548_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
lean_ctor_set(v___x_1566_, 2, v_args_1557_);
v___x_1567_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__1));
v___x_1568_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1549_, v___x_1566_, v___x_1567_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v_fvarId_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v_fvarId_1570_ = lean_ctor_get(v_a_1569_, 0);
lean_inc(v_fvarId_1570_);
v___x_1571_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_fvarId_1570_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_a_1569_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
v___x_1574_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1574_, 0, v_name_1550_);
lean_ctor_set(v___x_1574_, 1, v_levelParams_1551_);
lean_ctor_set(v___x_1574_, 2, v_type_1552_);
lean_ctor_set(v___x_1574_, 3, v_a_1553_);
lean_ctor_set_uint8(v___x_1574_, sizeof(void*)*4, v_safe_1554_);
v___x_1575_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__2));
v___x_1576_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1573_);
lean_ctor_set(v___x_1576_, 2, v___x_1575_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*3, v___x_1555_);
lean_inc_ref(v___x_1576_);
v___x_1577_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1576_, v___y_1563_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; 
v_unused_1585_ = lean_ctor_get(v___x_1577_, 0);
lean_dec(v_unused_1585_);
v___x_1579_ = v___x_1577_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_dec(v___x_1577_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1576_);
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1576_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref_known(v___x_1576_, 3);
v_a_1586_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1577_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1577_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v_a_1553_);
lean_dec_ref(v_type_1552_);
lean_dec(v_levelParams_1551_);
lean_dec(v_name_1550_);
v_a_1594_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1568_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1568_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___boxed(lean_object** _args){
lean_object* v___x_1602_ = _args[0];
lean_object* v___x_1603_ = _args[1];
lean_object* v_name_1604_ = _args[2];
lean_object* v_levelParams_1605_ = _args[3];
lean_object* v_type_1606_ = _args[4];
lean_object* v_a_1607_ = _args[5];
lean_object* v_safe_1608_ = _args[6];
lean_object* v___x_1609_ = _args[7];
lean_object* v_____r_1610_ = _args[8];
lean_object* v_args_1611_ = _args[9];
lean_object* v___y_1612_ = _args[10];
lean_object* v___y_1613_ = _args[11];
lean_object* v___y_1614_ = _args[12];
lean_object* v___y_1615_ = _args[13];
lean_object* v___y_1616_ = _args[14];
lean_object* v___y_1617_ = _args[15];
lean_object* v___y_1618_ = _args[16];
_start:
{
uint8_t v___x_11962__boxed_1619_; uint8_t v_safe_boxed_1620_; uint8_t v___x_11964__boxed_1621_; uint8_t v___y_11966__boxed_1622_; lean_object* v_res_1623_; 
v___x_11962__boxed_1619_ = lean_unbox(v___x_1603_);
v_safe_boxed_1620_ = lean_unbox(v_safe_1608_);
v___x_11964__boxed_1621_ = lean_unbox(v___x_1609_);
v___y_11966__boxed_1622_ = lean_unbox(v___y_1612_);
v_res_1623_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___x_1602_, v___x_11962__boxed_1619_, v_name_1604_, v_levelParams_1605_, v_type_1606_, v_a_1607_, v_safe_boxed_1620_, v___x_11964__boxed_1621_, v_____r_1610_, v_args_1611_, v___y_11966__boxed_1622_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
if (lean_obj_tag(v_x_1625_) == 0)
{
lean_inc(v_x_1624_);
return v_x_1624_;
}
else
{
lean_object* v_key_1626_; lean_object* v_tail_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_key_1626_ = lean_ctor_get(v_x_1625_, 0);
v_tail_1627_ = lean_ctor_get(v_x_1625_, 2);
v___x_1628_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1624_, v_tail_1627_);
lean_inc(v_key_1626_);
v___x_1629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1629_, 0, v_key_1626_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1630_, v_x_1631_);
lean_dec(v_x_1631_);
lean_dec(v_x_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object* v_as_1633_, size_t v_i_1634_, size_t v_stop_1635_, lean_object* v_b_1636_){
_start:
{
uint8_t v___x_1637_; 
v___x_1637_ = lean_usize_dec_eq(v_i_1634_, v_stop_1635_);
if (v___x_1637_ == 0)
{
size_t v___x_1638_; size_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1638_ = ((size_t)1ULL);
v___x_1639_ = lean_usize_sub(v_i_1634_, v___x_1638_);
v___x_1640_ = lean_array_uget_borrowed(v_as_1633_, v___x_1639_);
v___x_1641_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_b_1636_, v___x_1640_);
lean_dec(v_b_1636_);
v_i_1634_ = v___x_1639_;
v_b_1636_ = v___x_1641_;
goto _start;
}
else
{
return v_b_1636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object* v_as_1643_, lean_object* v_i_1644_, lean_object* v_stop_1645_, lean_object* v_b_1646_){
_start:
{
size_t v_i_boxed_1647_; size_t v_stop_boxed_1648_; lean_object* v_res_1649_; 
v_i_boxed_1647_ = lean_unbox_usize(v_i_1644_);
lean_dec(v_i_1644_);
v_stop_boxed_1648_ = lean_unbox_usize(v_stop_1645_);
lean_dec(v_stop_1645_);
v_res_1649_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_as_1643_, v_i_boxed_1647_, v_stop_boxed_1648_, v_b_1646_);
lean_dec_ref(v_as_1643_);
return v_res_1649_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object* v_m_1650_, lean_object* v_a_1651_){
_start:
{
lean_object* v_buckets_1652_; lean_object* v___x_1653_; uint64_t v___x_1654_; uint64_t v___x_1655_; uint64_t v___x_1656_; uint64_t v_fold_1657_; uint64_t v___x_1658_; uint64_t v___x_1659_; uint64_t v___x_1660_; size_t v___x_1661_; size_t v___x_1662_; size_t v___x_1663_; size_t v___x_1664_; size_t v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v_buckets_1652_ = lean_ctor_get(v_m_1650_, 1);
v___x_1653_ = lean_array_get_size(v_buckets_1652_);
v___x_1654_ = l_Lean_instHashableFVarId_hash(v_a_1651_);
v___x_1655_ = 32ULL;
v___x_1656_ = lean_uint64_shift_right(v___x_1654_, v___x_1655_);
v_fold_1657_ = lean_uint64_xor(v___x_1654_, v___x_1656_);
v___x_1658_ = 16ULL;
v___x_1659_ = lean_uint64_shift_right(v_fold_1657_, v___x_1658_);
v___x_1660_ = lean_uint64_xor(v_fold_1657_, v___x_1659_);
v___x_1661_ = lean_uint64_to_usize(v___x_1660_);
v___x_1662_ = lean_usize_of_nat(v___x_1653_);
v___x_1663_ = ((size_t)1ULL);
v___x_1664_ = lean_usize_sub(v___x_1662_, v___x_1663_);
v___x_1665_ = lean_usize_land(v___x_1661_, v___x_1664_);
v___x_1666_ = lean_array_uget_borrowed(v_buckets_1652_, v___x_1665_);
v___x_1667_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_1651_, v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object* v_m_1668_, lean_object* v_a_1669_){
_start:
{
uint8_t v_res_1670_; lean_object* v_r_1671_; 
v_res_1670_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1668_, v_a_1669_);
lean_dec(v_a_1669_);
lean_dec_ref(v_m_1668_);
v_r_1671_ = lean_box(v_res_1670_);
return v_r_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* v_a_1672_, lean_object* v_as_1673_, size_t v_i_1674_, size_t v_stop_1675_, lean_object* v_b_1676_){
_start:
{
lean_object* v___y_1678_; uint8_t v___x_1682_; 
v___x_1682_ = lean_usize_dec_eq(v_i_1674_, v_stop_1675_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v_fvarId_1684_; uint8_t v___x_1685_; 
v___x_1683_ = lean_array_uget_borrowed(v_as_1673_, v_i_1674_);
v_fvarId_1684_ = lean_ctor_get(v___x_1683_, 0);
v___x_1685_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1672_, v_fvarId_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
lean_inc(v___x_1683_);
v___x_1686_ = lean_array_push(v_b_1676_, v___x_1683_);
v___y_1678_ = v___x_1686_;
goto v___jp_1677_;
}
else
{
v___y_1678_ = v_b_1676_;
goto v___jp_1677_;
}
}
else
{
return v_b_1676_;
}
v___jp_1677_:
{
size_t v___x_1679_; size_t v___x_1680_; 
v___x_1679_ = ((size_t)1ULL);
v___x_1680_ = lean_usize_add(v_i_1674_, v___x_1679_);
v_i_1674_ = v___x_1680_;
v_b_1676_ = v___y_1678_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* v_a_1687_, lean_object* v_as_1688_, lean_object* v_i_1689_, lean_object* v_stop_1690_, lean_object* v_b_1691_){
_start:
{
size_t v_i_boxed_1692_; size_t v_stop_boxed_1693_; lean_object* v_res_1694_; 
v_i_boxed_1692_ = lean_unbox_usize(v_i_1689_);
lean_dec(v_i_1689_);
v_stop_boxed_1693_ = lean_unbox_usize(v_stop_1690_);
lean_dec(v_stop_1690_);
v_res_1694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1687_, v_as_1688_, v_i_boxed_1692_, v_stop_boxed_1693_, v_b_1691_);
lean_dec_ref(v_as_1688_);
lean_dec_ref(v_a_1687_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
if (lean_obj_tag(v_a_1695_) == 0)
{
lean_object* v___x_1697_; 
v___x_1697_ = l_List_reverse___redArg(v_a_1696_);
return v___x_1697_;
}
else
{
lean_object* v_head_1698_; lean_object* v_tail_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1708_; 
v_head_1698_ = lean_ctor_get(v_a_1695_, 0);
v_tail_1699_ = lean_ctor_get(v_a_1695_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_a_1695_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1701_ = v_a_1695_;
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_tail_1699_);
lean_inc(v_head_1698_);
lean_dec(v_a_1695_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1708_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = l_Lean_MessageData_ofExpr(v_head_1698_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v_a_1696_);
lean_ctor_set(v___x_1701_, 0, v___x_1703_);
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1696_);
v___x_1705_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
v_a_1695_ = v_tail_1699_;
v_a_1696_ = v___x_1705_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object* v_as_1709_, size_t v_sz_1710_, size_t v_i_1711_, lean_object* v_b_1712_){
_start:
{
lean_object* v_a_1715_; uint8_t v___x_1719_; 
v___x_1719_ = lean_usize_dec_lt(v_i_1711_, v_sz_1710_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_b_1712_);
return v___x_1720_;
}
else
{
lean_object* v_snd_1721_; lean_object* v_fst_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1757_; 
v_snd_1721_ = lean_ctor_get(v_b_1712_, 1);
v_fst_1722_ = lean_ctor_get(v_b_1712_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_b_1712_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1724_ = v_b_1712_;
v_isShared_1725_ = v_isSharedCheck_1757_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_snd_1721_);
lean_inc(v_fst_1722_);
lean_dec(v_b_1712_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1757_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_array_1726_; lean_object* v_start_1727_; lean_object* v_stop_1728_; uint8_t v___x_1729_; 
v_array_1726_ = lean_ctor_get(v_snd_1721_, 0);
v_start_1727_ = lean_ctor_get(v_snd_1721_, 1);
v_stop_1728_ = lean_ctor_get(v_snd_1721_, 2);
v___x_1729_ = lean_nat_dec_lt(v_start_1727_, v_stop_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1731_; 
if (v_isShared_1725_ == 0)
{
v___x_1731_ = v___x_1724_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_fst_1722_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_snd_1721_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
else
{
lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1753_; 
lean_inc(v_stop_1728_);
lean_inc(v_start_1727_);
lean_inc_ref(v_array_1726_);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_snd_1721_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; lean_object* v_unused_1755_; lean_object* v_unused_1756_; 
v_unused_1754_ = lean_ctor_get(v_snd_1721_, 2);
lean_dec(v_unused_1754_);
v_unused_1755_ = lean_ctor_get(v_snd_1721_, 1);
lean_dec(v_unused_1755_);
v_unused_1756_ = lean_ctor_get(v_snd_1721_, 0);
lean_dec(v_unused_1756_);
v___x_1735_ = v_snd_1721_;
v_isShared_1736_ = v_isSharedCheck_1753_;
goto v_resetjp_1734_;
}
else
{
lean_dec(v_snd_1721_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1753_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v_a_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1742_; 
v_a_1737_ = lean_array_uget_borrowed(v_as_1709_, v_i_1711_);
v___x_1738_ = lean_array_fget(v_array_1726_, v_start_1727_);
v___x_1739_ = lean_unsigned_to_nat(1u);
v___x_1740_ = lean_nat_add(v_start_1727_, v___x_1739_);
lean_dec(v_start_1727_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 1, v___x_1740_);
v___x_1742_ = v___x_1735_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_array_1726_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_stop_1728_);
v___x_1742_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_unbox(v_a_1737_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1745_; 
lean_dec(v___x_1738_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1742_);
v___x_1745_ = v___x_1724_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_fst_1722_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___x_1742_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
v_a_1715_ = v___x_1745_;
goto v___jp_1714_;
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1747_ = l_Lean_Compiler_LCNF_Param_toArg___redArg(v___x_1738_);
lean_dec(v___x_1738_);
v___x_1748_ = lean_array_push(v_fst_1722_, v___x_1747_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1742_);
lean_ctor_set(v___x_1724_, 0, v___x_1748_);
v___x_1750_ = v___x_1724_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v___x_1742_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
v_a_1715_ = v___x_1750_;
goto v___jp_1714_;
}
}
}
}
}
}
}
v___jp_1714_:
{
size_t v___x_1716_; size_t v___x_1717_; 
v___x_1716_ = ((size_t)1ULL);
v___x_1717_ = lean_usize_add(v_i_1711_, v___x_1716_);
v_i_1711_ = v___x_1717_;
v_b_1712_ = v_a_1715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object* v_as_1758_, lean_object* v_sz_1759_, lean_object* v_i_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_){
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1759_);
lean_dec(v_sz_1759_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1760_);
lean_dec(v_i_1760_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_1758_, v_sz_boxed_1763_, v_i_boxed_1764_, v_b_1761_);
lean_dec_ref(v_as_1758_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t v_sz_1766_, size_t v_i_1767_, lean_object* v_bs_1768_, uint8_t v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
uint8_t v___x_1776_; 
v___x_1776_ = lean_usize_dec_lt(v_i_1767_, v_sz_1766_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_bs_1768_);
return v___x_1777_;
}
else
{
uint8_t v___x_1778_; lean_object* v_v_1779_; lean_object* v___x_1780_; 
v___x_1778_ = 0;
v_v_1779_ = lean_array_uget_borrowed(v_bs_1768_, v_i_1767_);
lean_inc(v_v_1779_);
v___x_1780_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_1778_, v_v_1779_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1782_; lean_object* v_bs_x27_1783_; size_t v___x_1784_; size_t v___x_1785_; lean_object* v___x_1786_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___x_1782_ = lean_unsigned_to_nat(0u);
v_bs_x27_1783_ = lean_array_uset(v_bs_1768_, v_i_1767_, v___x_1782_);
v___x_1784_ = ((size_t)1ULL);
v___x_1785_ = lean_usize_add(v_i_1767_, v___x_1784_);
v___x_1786_ = lean_array_uset(v_bs_x27_1783_, v_i_1767_, v_a_1781_);
v_i_1767_ = v___x_1785_;
v_bs_1768_ = v___x_1786_;
goto _start;
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v_bs_1768_);
v_a_1788_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1780_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1780_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* v_sz_1796_, lean_object* v_i_1797_, lean_object* v_bs_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
size_t v_sz_boxed_1806_; size_t v_i_boxed_1807_; uint8_t v___y_12263__boxed_1808_; lean_object* v_res_1809_; 
v_sz_boxed_1806_ = lean_unbox_usize(v_sz_1796_);
lean_dec(v_sz_1796_);
v_i_boxed_1807_ = lean_unbox_usize(v_i_1797_);
lean_dec(v_i_1797_);
v___y_12263__boxed_1808_ = lean_unbox(v___y_1799_);
v_res_1809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_boxed_1806_, v_i_boxed_1807_, v_bs_1798_, v___y_12263__boxed_1808_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
if (lean_obj_tag(v_a_1810_) == 0)
{
lean_object* v___x_1812_; 
v___x_1812_ = l_List_reverse___redArg(v_a_1811_);
return v___x_1812_;
}
else
{
lean_object* v_head_1813_; lean_object* v_tail_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1823_; 
v_head_1813_ = lean_ctor_get(v_a_1810_, 0);
v_tail_1814_ = lean_ctor_get(v_a_1810_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_a_1810_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1816_ = v_a_1810_;
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_tail_1814_);
lean_inc(v_head_1813_);
lean_dec(v_a_1810_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1818_ = l_Lean_mkFVar(v_head_1813_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 1, v_a_1811_);
lean_ctor_set(v___x_1816_, 0, v___x_1818_);
v___x_1820_ = v___x_1816_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_a_1811_);
v___x_1820_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
v_a_1810_ = v_tail_1814_;
v_a_1811_ = v___x_1820_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(lean_object* v_a_1824_, lean_object* v_as_1825_, size_t v_i_1826_, size_t v_stop_1827_, lean_object* v_b_1828_){
_start:
{
lean_object* v___y_1830_; uint8_t v___x_1834_; 
v___x_1834_ = lean_usize_dec_eq(v_i_1826_, v_stop_1827_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v_fvarId_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_array_uget_borrowed(v_as_1825_, v_i_1826_);
v_fvarId_1836_ = lean_ctor_get(v___x_1835_, 0);
v___x_1837_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1824_, v_fvarId_1836_);
if (v___x_1837_ == 0)
{
v___y_1830_ = v_b_1828_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1838_; 
lean_inc(v___x_1835_);
v___x_1838_ = lean_array_push(v_b_1828_, v___x_1835_);
v___y_1830_ = v___x_1838_;
goto v___jp_1829_;
}
}
else
{
return v_b_1828_;
}
v___jp_1829_:
{
size_t v___x_1831_; size_t v___x_1832_; 
v___x_1831_ = ((size_t)1ULL);
v___x_1832_ = lean_usize_add(v_i_1826_, v___x_1831_);
v_i_1826_ = v___x_1832_;
v_b_1828_ = v___y_1830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6___boxed(lean_object* v_a_1839_, lean_object* v_as_1840_, lean_object* v_i_1841_, lean_object* v_stop_1842_, lean_object* v_b_1843_){
_start:
{
size_t v_i_boxed_1844_; size_t v_stop_boxed_1845_; lean_object* v_res_1846_; 
v_i_boxed_1844_ = lean_unbox_usize(v_i_1841_);
lean_dec(v_i_1841_);
v_stop_boxed_1845_ = lean_unbox_usize(v_stop_1842_);
lean_dec(v_stop_1842_);
v_res_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1839_, v_as_1840_, v_i_boxed_1844_, v_stop_boxed_1845_, v_b_1843_);
lean_dec_ref(v_as_1840_);
lean_dec_ref(v_a_1839_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object* v_a_1847_, lean_object* v_as_1848_, size_t v_i_1849_, size_t v_stop_1850_, lean_object* v_b_1851_){
_start:
{
lean_object* v___y_1853_; uint8_t v___x_1857_; 
v___x_1857_ = lean_usize_dec_eq(v_i_1849_, v_stop_1850_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; lean_object* v_fvarId_1859_; uint8_t v___x_1860_; 
v___x_1858_ = lean_array_uget_borrowed(v_as_1848_, v_i_1849_);
v_fvarId_1859_ = lean_ctor_get(v___x_1858_, 0);
v___x_1860_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1847_, v_fvarId_1859_);
if (v___x_1860_ == 0)
{
v___y_1853_ = v_b_1851_;
goto v___jp_1852_;
}
else
{
lean_object* v___x_1861_; 
lean_inc(v___x_1858_);
v___x_1861_ = lean_array_push(v_b_1851_, v___x_1858_);
v___y_1853_ = v___x_1861_;
goto v___jp_1852_;
}
}
else
{
return v_b_1851_;
}
v___jp_1852_:
{
size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_add(v_i_1849_, v___x_1854_);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1847_, v_as_1848_, v___x_1855_, v_stop_1850_, v___y_1853_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object* v_a_1862_, lean_object* v_as_1863_, lean_object* v_i_1864_, lean_object* v_stop_1865_, lean_object* v_b_1866_){
_start:
{
size_t v_i_boxed_1867_; size_t v_stop_boxed_1868_; lean_object* v_res_1869_; 
v_i_boxed_1867_ = lean_unbox_usize(v_i_1864_);
lean_dec(v_i_1864_);
v_stop_boxed_1868_ = lean_unbox_usize(v_stop_1865_);
lean_dec(v_stop_1865_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1862_, v_as_1863_, v_i_boxed_1867_, v_stop_boxed_1868_, v_b_1866_);
lean_dec_ref(v_as_1863_);
lean_dec_ref(v_a_1862_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object* v_a_1870_, size_t v_sz_1871_, size_t v_i_1872_, lean_object* v_bs_1873_){
_start:
{
uint8_t v___x_1874_; 
v___x_1874_ = lean_usize_dec_lt(v_i_1872_, v_sz_1871_);
if (v___x_1874_ == 0)
{
return v_bs_1873_;
}
else
{
lean_object* v_v_1875_; lean_object* v_fvarId_1876_; lean_object* v___x_1877_; lean_object* v_bs_x27_1878_; uint8_t v___x_1879_; size_t v___x_1880_; size_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_v_1875_ = lean_array_uget_borrowed(v_bs_1873_, v_i_1872_);
v_fvarId_1876_ = lean_ctor_get(v_v_1875_, 0);
lean_inc(v_fvarId_1876_);
v___x_1877_ = lean_unsigned_to_nat(0u);
v_bs_x27_1878_ = lean_array_uset(v_bs_1873_, v_i_1872_, v___x_1877_);
v___x_1879_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1870_, v_fvarId_1876_);
lean_dec(v_fvarId_1876_);
v___x_1880_ = ((size_t)1ULL);
v___x_1881_ = lean_usize_add(v_i_1872_, v___x_1880_);
v___x_1882_ = lean_box(v___x_1879_);
v___x_1883_ = lean_array_uset(v_bs_x27_1878_, v_i_1872_, v___x_1882_);
v_i_1872_ = v___x_1881_;
v_bs_1873_ = v___x_1883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object* v_a_1885_, lean_object* v_sz_1886_, lean_object* v_i_1887_, lean_object* v_bs_1888_){
_start:
{
size_t v_sz_boxed_1889_; size_t v_i_boxed_1890_; lean_object* v_res_1891_; 
v_sz_boxed_1889_ = lean_unbox_usize(v_sz_1886_);
lean_dec(v_sz_1886_);
v_i_boxed_1890_ = lean_unbox_usize(v_i_1887_);
lean_dec(v_i_1887_);
v_res_1891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1885_, v_sz_boxed_1889_, v_i_boxed_1890_, v_bs_1888_);
lean_dec_ref(v_a_1885_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* v_a_1892_, size_t v_sz_1893_, size_t v_i_1894_, lean_object* v_bs_1895_){
_start:
{
uint8_t v___x_1896_; 
v___x_1896_ = lean_usize_dec_lt(v_i_1894_, v_sz_1893_);
if (v___x_1896_ == 0)
{
return v_bs_1895_;
}
else
{
lean_object* v_v_1897_; lean_object* v_fvarId_1898_; lean_object* v___x_1899_; lean_object* v_bs_x27_1900_; uint8_t v___x_1901_; size_t v___x_1902_; size_t v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_v_1897_ = lean_array_uget_borrowed(v_bs_1895_, v_i_1894_);
v_fvarId_1898_ = lean_ctor_get(v_v_1897_, 0);
lean_inc(v_fvarId_1898_);
v___x_1899_ = lean_unsigned_to_nat(0u);
v_bs_x27_1900_ = lean_array_uset(v_bs_1895_, v_i_1894_, v___x_1899_);
v___x_1901_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1892_, v_fvarId_1898_);
lean_dec(v_fvarId_1898_);
v___x_1902_ = ((size_t)1ULL);
v___x_1903_ = lean_usize_add(v_i_1894_, v___x_1902_);
v___x_1904_ = lean_box(v___x_1901_);
v___x_1905_ = lean_array_uset(v_bs_x27_1900_, v_i_1894_, v___x_1904_);
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1892_, v_sz_1893_, v___x_1903_, v___x_1905_);
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object* v_a_1907_, lean_object* v_sz_1908_, lean_object* v_i_1909_, lean_object* v_bs_1910_){
_start:
{
size_t v_sz_boxed_1911_; size_t v_i_boxed_1912_; lean_object* v_res_1913_; 
v_sz_boxed_1911_ = lean_unbox_usize(v_sz_1908_);
lean_dec(v_sz_1908_);
v_i_boxed_1912_ = lean_unbox_usize(v_i_1909_);
lean_dec(v_i_1909_);
v_res_1913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1907_, v_sz_boxed_1911_, v_i_boxed_1912_, v_bs_1910_);
lean_dec_ref(v_a_1907_);
return v_res_1913_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_box(0);
v___x_1915_ = lean_unsigned_to_nat(16u);
v___x_1916_ = lean_mk_array(v___x_1915_, v___x_1914_);
return v___x_1916_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0);
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___x_1917_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = lean_box(0);
v___x_1929_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6));
v___x_1930_ = l_Lean_Expr_const___override(v___x_1929_, v___x_1928_);
return v___x_1930_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_1943_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14));
v___x_1944_ = l_Lean_Name_append(v___x_1943_, v___x_1942_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16));
v___x_1947_ = l_Lean_stringToMessageData(v___x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* v_decl_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v___y_1955_; lean_object* v___y_1956_; uint8_t v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v_value_1992_; 
v_value_1992_ = lean_ctor_get(v_decl_1948_, 1);
lean_inc_ref(v_value_1992_);
if (lean_obj_tag(v_value_1992_) == 0)
{
lean_object* v_toSignature_1993_; uint8_t v_recursive_1994_; lean_object* v_inlineAttr_x3f_1995_; lean_object* v_code_1996_; lean_object* v_name_1997_; lean_object* v_levelParams_1998_; lean_object* v_type_1999_; lean_object* v_params_2000_; uint8_t v_safe_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v_toSignature_1993_ = lean_ctor_get(v_decl_1948_, 0);
v_recursive_1994_ = lean_ctor_get_uint8(v_decl_1948_, sizeof(void*)*3);
v_inlineAttr_x3f_1995_ = lean_ctor_get(v_decl_1948_, 2);
v_code_1996_ = lean_ctor_get(v_value_1992_, 0);
v_name_1997_ = lean_ctor_get(v_toSignature_1993_, 0);
v_levelParams_1998_ = lean_ctor_get(v_toSignature_1993_, 1);
v_type_1999_ = lean_ctor_get(v_toSignature_1993_, 2);
v_params_2000_ = lean_ctor_get(v_toSignature_1993_, 3);
v_safe_2001_ = lean_ctor_get_uint8(v_toSignature_1993_, sizeof(void*)*4);
v___x_2002_ = lean_array_get_size(v_params_2000_);
v___x_2003_ = lean_unsigned_to_nat(0u);
v___x_2004_ = lean_nat_dec_eq(v___x_2002_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_inc_ref(v_code_1996_);
lean_inc_ref(v_decl_1948_);
v___x_2005_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2180_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2180_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2180_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v_size_2010_; lean_object* v_buckets_2011_; uint8_t v___x_2012_; 
v_size_2010_ = lean_ctor_get(v_a_2006_, 0);
v_buckets_2011_ = lean_ctor_get(v_a_2006_, 1);
v___x_2012_ = lean_nat_dec_eq(v_size_2010_, v___x_2002_);
if (v___x_2012_ == 0)
{
lean_object* v_toCold_2013_; lean_object* v_options_2014_; lean_object* v_inheritedTraceOptions_2015_; uint8_t v_hasTrace_2016_; uint8_t v___x_2017_; lean_object* v___y_2019_; uint8_t v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; size_t v___y_2024_; lean_object* v___y_2025_; uint8_t v___y_2026_; lean_object* v___y_2027_; size_t v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2075_; uint8_t v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; size_t v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; uint8_t v___y_2083_; size_t v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; size_t v___y_2095_; lean_object* v___y_2096_; uint8_t v___y_2097_; lean_object* v___y_2098_; size_t v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; 
lean_inc_ref(v_params_2000_);
lean_inc_ref(v_type_1999_);
lean_inc(v_levelParams_1998_);
lean_inc(v_name_1997_);
lean_inc(v_inlineAttr_x3f_1995_);
lean_del_object(v___x_2008_);
lean_dec_ref(v_decl_1948_);
v_toCold_2013_ = lean_ctor_get(v_a_1951_, 0);
v_options_2014_ = lean_ctor_get(v_toCold_2013_, 2);
v_inheritedTraceOptions_2015_ = lean_ctor_get(v_toCold_2013_, 11);
v_hasTrace_2016_ = lean_ctor_get_uint8(v_options_2014_, sizeof(void*)*1);
v___x_2017_ = lean_nat_dec_eq(v_size_2010_, v___x_2003_);
if (v_hasTrace_2016_ == 0)
{
v___y_2125_ = v_a_1949_;
v___y_2126_ = v_a_1950_;
v___y_2127_ = v_a_1951_;
v___y_2128_ = v_a_1952_;
goto v___jp_2124_;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2146_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_2147_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15);
v___x_2148_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2015_, v_options_2014_, v___x_2147_);
if (v___x_2148_ == 0)
{
v___y_2125_ = v_a_1949_;
v___y_2126_ = v_a_1950_;
v___y_2127_ = v_a_1951_;
v___y_2128_ = v_a_1952_;
goto v___jp_2124_;
}
else
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___y_2153_; lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
lean_inc(v_name_1997_);
v___x_2149_ = l_Lean_MessageData_ofName(v_name_1997_);
v___x_2150_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17);
v___x_2151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2168_ = lean_box(0);
v___x_2169_ = lean_array_get_size(v_buckets_2011_);
v___x_2170_ = lean_nat_dec_lt(v___x_2003_, v___x_2169_);
if (v___x_2170_ == 0)
{
v___y_2153_ = v___x_2168_;
goto v___jp_2152_;
}
else
{
size_t v___x_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = lean_usize_of_nat(v___x_2169_);
v___x_2172_ = ((size_t)0ULL);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_buckets_2011_, v___x_2171_, v___x_2172_, v___x_2168_);
v___y_2153_ = v___x_2173_;
goto v___jp_2152_;
}
v___jp_2152_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2154_ = lean_box(0);
v___x_2155_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(v___y_2153_, v___x_2154_);
v___x_2156_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(v___x_2155_, v___x_2154_);
v___x_2157_ = l_Lean_MessageData_ofList(v___x_2156_);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2151_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v___x_2146_, v___x_2158_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_dec_ref_known(v___x_2159_, 1);
v___y_2125_ = v_a_1949_;
v___y_2126_ = v_a_1950_;
v___y_2127_ = v_a_1951_;
v___y_2128_ = v_a_1952_;
goto v___jp_2124_;
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec(v_a_2006_);
lean_dec_ref(v_params_2000_);
lean_dec_ref(v_type_1999_);
lean_dec(v_levelParams_1998_);
lean_dec(v_name_1997_);
lean_dec_ref(v_code_1996_);
lean_dec(v_inlineAttr_x3f_1995_);
lean_dec_ref_known(v_value_1992_, 1);
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
v___jp_2018_:
{
if (lean_obj_tag(v___y_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_a_2031_ = lean_ctor_get(v___y_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___y_2030_, 1);
v___x_2032_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1);
v___x_2033_ = lean_st_mk_ref(v___x_2032_);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v___y_2024_, v___y_2028_, v_params_2000_, v___x_2012_, v___x_2033_, v___y_2027_, v___y_2025_, v___y_2023_, v___y_2022_);
if (lean_obj_tag(v___x_2034_) == 0)
{
if (v___x_2017_ == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; size_t v_sz_2040_; lean_object* v___x_2041_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc_n(v_a_2035_, 2);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_2037_ = lean_array_get_size(v_a_2035_);
v___x_2038_ = l_Array_toSubarray___redArg(v_a_2035_, v___x_2003_, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2036_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v_sz_2040_ = lean_array_size(v___y_2021_);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v___y_2021_, v_sz_2040_, v___y_2028_, v___x_2039_);
lean_dec_ref(v___y_2021_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v_fst_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v_fst_2043_ = lean_ctor_get(v_a_2042_, 0);
lean_inc(v_fst_2043_);
lean_dec(v_a_2042_);
v___x_2044_ = lean_box(0);
v___x_2045_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___y_2019_, v___y_2020_, v_name_1997_, v_levelParams_1998_, v_type_1999_, v_a_2035_, v_safe_2001_, v___x_2012_, v___x_2044_, v_fst_2043_, v___x_2012_, v___x_2033_, v___y_2027_, v___y_2025_, v___y_2023_, v___y_2022_);
v___y_1955_ = v_a_2031_;
v___y_1956_ = v___y_2025_;
v___y_1957_ = v___y_2026_;
v___y_1958_ = v___x_2033_;
v___y_1959_ = v___y_2029_;
v___y_1960_ = v___x_2045_;
goto v___jp_1954_;
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_a_2035_);
lean_dec(v___x_2033_);
lean_dec(v_a_2031_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2019_);
lean_dec_ref(v_type_1999_);
lean_dec(v_levelParams_1998_);
lean_dec(v_name_1997_);
v_a_2046_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2041_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2041_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
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
else
{
lean_object* v_a_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec_ref(v___y_2021_);
v_a_2054_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2055_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5));
v___x_2056_ = lean_box(0);
v___x_2057_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___y_2019_, v___y_2020_, v_name_1997_, v_levelParams_1998_, v_type_1999_, v_a_2054_, v_safe_2001_, v___x_2012_, v___x_2056_, v___x_2055_, v___x_2012_, v___x_2033_, v___y_2027_, v___y_2025_, v___y_2023_, v___y_2022_);
v___y_1955_ = v_a_2031_;
v___y_1956_ = v___y_2025_;
v___y_1957_ = v___y_2026_;
v___y_1958_ = v___x_2033_;
v___y_1959_ = v___y_2029_;
v___y_1960_ = v___x_2057_;
goto v___jp_1954_;
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v___x_2033_);
lean_dec(v_a_2031_);
lean_dec_ref(v___y_2029_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2019_);
lean_dec_ref(v_type_1999_);
lean_dec(v_levelParams_1998_);
lean_dec(v_name_1997_);
v_a_2058_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2034_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2034_);
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
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v___y_2029_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2019_);
lean_dec_ref(v_params_2000_);
lean_dec_ref(v_type_1999_);
lean_dec(v_levelParams_1998_);
lean_dec(v_name_1997_);
v_a_2066_ = lean_ctor_get(v___y_2030_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___y_2030_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___y_2030_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___y_2030_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
v___jp_2074_:
{
lean_object* v___x_2088_; 
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2085_);
v___x_2088_ = lean_apply_6(v___y_2078_, v___y_2087_, v___y_2085_, v___y_2082_, v___y_2081_, v___y_2080_, lean_box(0));
v___y_2019_ = v___y_2075_;
v___y_2020_ = v___y_2076_;
v___y_2021_ = v___y_2077_;
v___y_2022_ = v___y_2080_;
v___y_2023_ = v___y_2081_;
v___y_2024_ = v___y_2079_;
v___y_2025_ = v___y_2082_;
v___y_2026_ = v___y_2083_;
v___y_2027_ = v___y_2085_;
v___y_2028_ = v___y_2084_;
v___y_2029_ = v___y_2086_;
v___y_2030_ = v___x_2088_;
goto v___jp_2018_;
}
v___jp_2089_:
{
if (v___x_2017_ == 0)
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_2102_ = lean_nat_dec_lt(v___x_2003_, v___x_2002_);
if (v___x_2102_ == 0)
{
lean_dec(v_a_2006_);
v___y_2075_ = v___y_2090_;
v___y_2076_ = v___y_2097_;
v___y_2077_ = v___y_2091_;
v___y_2078_ = v___y_2092_;
v___y_2079_ = v___y_2095_;
v___y_2080_ = v___y_2094_;
v___y_2081_ = v___y_2093_;
v___y_2082_ = v___y_2096_;
v___y_2083_ = v___y_2097_;
v___y_2084_ = v___y_2099_;
v___y_2085_ = v___y_2098_;
v___y_2086_ = v___y_2100_;
v___y_2087_ = v___x_2101_;
goto v___jp_2074_;
}
else
{
uint8_t v___x_2103_; 
v___x_2103_ = lean_nat_dec_le(v___x_2002_, v___x_2002_);
if (v___x_2103_ == 0)
{
if (v___x_2102_ == 0)
{
lean_dec(v_a_2006_);
v___y_2075_ = v___y_2090_;
v___y_2076_ = v___y_2097_;
v___y_2077_ = v___y_2091_;
v___y_2078_ = v___y_2092_;
v___y_2079_ = v___y_2095_;
v___y_2080_ = v___y_2094_;
v___y_2081_ = v___y_2093_;
v___y_2082_ = v___y_2096_;
v___y_2083_ = v___y_2097_;
v___y_2084_ = v___y_2099_;
v___y_2085_ = v___y_2098_;
v___y_2086_ = v___y_2100_;
v___y_2087_ = v___x_2101_;
goto v___jp_2074_;
}
else
{
size_t v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_usize_of_nat(v___x_2002_);
v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_2006_, v_params_2000_, v___y_2099_, v___x_2104_, v___x_2101_);
lean_dec(v_a_2006_);
v___y_2075_ = v___y_2090_;
v___y_2076_ = v___y_2097_;
v___y_2077_ = v___y_2091_;
v___y_2078_ = v___y_2092_;
v___y_2079_ = v___y_2095_;
v___y_2080_ = v___y_2094_;
v___y_2081_ = v___y_2093_;
v___y_2082_ = v___y_2096_;
v___y_2083_ = v___y_2097_;
v___y_2084_ = v___y_2099_;
v___y_2085_ = v___y_2098_;
v___y_2086_ = v___y_2100_;
v___y_2087_ = v___x_2105_;
goto v___jp_2074_;
}
}
else
{
size_t v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_usize_of_nat(v___x_2002_);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_2006_, v_params_2000_, v___y_2099_, v___x_2106_, v___x_2101_);
lean_dec(v_a_2006_);
v___y_2075_ = v___y_2090_;
v___y_2076_ = v___y_2097_;
v___y_2077_ = v___y_2091_;
v___y_2078_ = v___y_2092_;
v___y_2079_ = v___y_2095_;
v___y_2080_ = v___y_2094_;
v___y_2081_ = v___y_2093_;
v___y_2082_ = v___y_2096_;
v___y_2083_ = v___y_2097_;
v___y_2084_ = v___y_2099_;
v___y_2085_ = v___y_2098_;
v___y_2086_ = v___y_2100_;
v___y_2087_ = v___x_2107_;
goto v___jp_2074_;
}
}
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec(v_a_2006_);
v___x_2108_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4));
v___x_2109_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7);
v___x_2110_ = l_Lean_Compiler_LCNF_mkParam(v___y_2097_, v___x_2108_, v___x_2109_, v___x_2012_, v___y_2098_, v___y_2096_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = lean_unsigned_to_nat(1u);
v___x_2113_ = lean_mk_empty_array_with_capacity(v___x_2112_);
v___x_2114_ = lean_array_push(v___x_2113_, v_a_2111_);
lean_inc(v___y_2094_);
lean_inc_ref(v___y_2093_);
lean_inc(v___y_2096_);
lean_inc_ref(v___y_2098_);
v___x_2115_ = lean_apply_6(v___y_2092_, v___x_2114_, v___y_2098_, v___y_2096_, v___y_2093_, v___y_2094_, lean_box(0));
v___y_2019_ = v___y_2090_;
v___y_2020_ = v___y_2097_;
v___y_2021_ = v___y_2091_;
v___y_2022_ = v___y_2094_;
v___y_2023_ = v___y_2093_;
v___y_2024_ = v___y_2095_;
v___y_2025_ = v___y_2096_;
v___y_2026_ = v___y_2097_;
v___y_2027_ = v___y_2098_;
v___y_2028_ = v___y_2099_;
v___y_2029_ = v___y_2100_;
v___y_2030_ = v___x_2115_;
goto v___jp_2018_;
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v___y_2100_);
lean_dec_ref(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v_params_2000_);
lean_dec_ref(v_type_1999_);
lean_dec(v_levelParams_1998_);
lean_dec(v_name_1997_);
v_a_2116_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2110_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2110_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
v___jp_2124_:
{
size_t v_sz_2129_; size_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___f_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v_sz_2129_ = lean_array_size(v_params_2000_);
v___x_2130_ = ((size_t)0ULL);
lean_inc_ref(v_params_2000_);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_2006_, v_sz_2129_, v___x_2130_, v_params_2000_);
v___x_2132_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9));
lean_inc_n(v_name_1997_, 2);
v___x_2133_ = l_Lean_Name_append(v_name_1997_, v___x_2132_);
v___x_2134_ = lean_box(v___x_2017_);
v___x_2135_ = lean_box(v_safe_2001_);
v___x_2136_ = lean_box(v_recursive_1994_);
lean_inc_ref(v___x_2131_);
lean_inc(v___x_2133_);
v___f_2137_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2137_, 0, v_name_1997_);
lean_closure_set(v___f_2137_, 1, v___x_2133_);
lean_closure_set(v___f_2137_, 2, v___x_2131_);
lean_closure_set(v___f_2137_, 3, v___x_2134_);
lean_closure_set(v___f_2137_, 4, v_value_1992_);
lean_closure_set(v___f_2137_, 5, v_code_1996_);
lean_closure_set(v___f_2137_, 6, v___x_2135_);
lean_closure_set(v___f_2137_, 7, v___x_2136_);
lean_closure_set(v___f_2137_, 8, v_inlineAttr_x3f_1995_);
v___x_2138_ = 0;
v___x_2139_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_2140_ = lean_nat_dec_lt(v___x_2003_, v___x_2002_);
if (v___x_2140_ == 0)
{
v___y_2090_ = v___x_2133_;
v___y_2091_ = v___x_2131_;
v___y_2092_ = v___f_2137_;
v___y_2093_ = v___y_2127_;
v___y_2094_ = v___y_2128_;
v___y_2095_ = v_sz_2129_;
v___y_2096_ = v___y_2126_;
v___y_2097_ = v___x_2138_;
v___y_2098_ = v___y_2125_;
v___y_2099_ = v___x_2130_;
v___y_2100_ = v___x_2139_;
goto v___jp_2089_;
}
else
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_nat_dec_le(v___x_2002_, v___x_2002_);
if (v___x_2141_ == 0)
{
if (v___x_2140_ == 0)
{
v___y_2090_ = v___x_2133_;
v___y_2091_ = v___x_2131_;
v___y_2092_ = v___f_2137_;
v___y_2093_ = v___y_2127_;
v___y_2094_ = v___y_2128_;
v___y_2095_ = v_sz_2129_;
v___y_2096_ = v___y_2126_;
v___y_2097_ = v___x_2138_;
v___y_2098_ = v___y_2125_;
v___y_2099_ = v___x_2130_;
v___y_2100_ = v___x_2139_;
goto v___jp_2089_;
}
else
{
size_t v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = lean_usize_of_nat(v___x_2002_);
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_2006_, v_params_2000_, v___x_2130_, v___x_2142_, v___x_2139_);
v___y_2090_ = v___x_2133_;
v___y_2091_ = v___x_2131_;
v___y_2092_ = v___f_2137_;
v___y_2093_ = v___y_2127_;
v___y_2094_ = v___y_2128_;
v___y_2095_ = v_sz_2129_;
v___y_2096_ = v___y_2126_;
v___y_2097_ = v___x_2138_;
v___y_2098_ = v___y_2125_;
v___y_2099_ = v___x_2130_;
v___y_2100_ = v___x_2143_;
goto v___jp_2089_;
}
}
else
{
size_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_usize_of_nat(v___x_2002_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_2006_, v_params_2000_, v___x_2130_, v___x_2144_, v___x_2139_);
v___y_2090_ = v___x_2133_;
v___y_2091_ = v___x_2131_;
v___y_2092_ = v___f_2137_;
v___y_2093_ = v___y_2127_;
v___y_2094_ = v___y_2128_;
v___y_2095_ = v_sz_2129_;
v___y_2096_ = v___y_2126_;
v___y_2097_ = v___x_2138_;
v___y_2098_ = v___y_2125_;
v___y_2099_ = v___x_2130_;
v___y_2100_ = v___x_2145_;
goto v___jp_2089_;
}
}
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_dec(v_a_2006_);
lean_dec_ref(v_code_1996_);
lean_dec_ref_known(v_value_1992_, 1);
v___x_2174_ = lean_unsigned_to_nat(1u);
v___x_2175_ = lean_mk_empty_array_with_capacity(v___x_2174_);
v___x_2176_ = lean_array_push(v___x_2175_, v_decl_1948_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2176_);
v___x_2178_ = v___x_2008_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v_code_1996_);
lean_dec_ref_known(v_value_1992_, 1);
lean_dec_ref(v_decl_1948_);
v_a_2181_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2005_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2005_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2198_; 
v_isSharedCheck_2198_ = !lean_is_exclusive(v_value_1992_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; 
v_unused_2199_ = lean_ctor_get(v_value_1992_, 0);
lean_dec(v_unused_2199_);
v___x_2190_ = v_value_1992_;
v_isShared_2191_ = v_isSharedCheck_2198_;
goto v_resetjp_2189_;
}
else
{
lean_dec(v_value_1992_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2198_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = lean_mk_empty_array_with_capacity(v___x_2192_);
v___x_2194_ = lean_array_push(v___x_2193_, v_decl_1948_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2194_);
v___x_2196_ = v___x_2190_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2209_; 
v_isSharedCheck_2209_ = !lean_is_exclusive(v_value_1992_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v_value_1992_, 0);
lean_dec(v_unused_2210_);
v___x_2201_ = v_value_1992_;
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
else
{
lean_dec(v_value_1992_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2209_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2203_ = lean_unsigned_to_nat(1u);
v___x_2204_ = lean_mk_empty_array_with_capacity(v___x_2203_);
v___x_2205_ = lean_array_push(v___x_2204_, v_decl_1948_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set_tag(v___x_2201_, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2205_);
v___x_2207_ = v___x_2201_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
v___jp_1954_:
{
if (lean_obj_tag(v___y_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_a_1961_ = lean_ctor_get(v___y_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___y_1960_, 1);
v___x_1962_ = lean_st_ref_get(v___y_1958_);
lean_dec(v___y_1958_);
lean_dec(v___x_1962_);
v___x_1963_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___y_1957_, v___y_1959_, v___y_1956_);
lean_dec_ref(v___y_1959_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1974_; 
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v___x_1963_, 0);
lean_dec(v_unused_1975_);
v___x_1965_ = v___x_1963_;
v_isShared_1966_ = v_isSharedCheck_1974_;
goto v_resetjp_1964_;
}
else
{
lean_dec(v___x_1963_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1974_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1967_ = lean_unsigned_to_nat(2u);
v___x_1968_ = lean_mk_empty_array_with_capacity(v___x_1967_);
v___x_1969_ = lean_array_push(v___x_1968_, v___y_1955_);
v___x_1970_ = lean_array_push(v___x_1969_, v_a_1961_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1970_);
v___x_1972_ = v___x_1965_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_dec(v_a_1961_);
lean_dec_ref(v___y_1955_);
v_a_1976_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1963_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1963_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1955_);
v_a_1984_ = lean_ctor_get(v___y_1960_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___y_1960_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___y_1960_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___y_1960_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object* v_decl_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v_decl_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
return v_res_2217_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* v_00_u03b2_2218_, lean_object* v_m_2219_, lean_object* v_a_2220_){
_start:
{
uint8_t v___x_2221_; 
v___x_2221_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_2219_, v_a_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* v_00_u03b2_2222_, lean_object* v_m_2223_, lean_object* v_a_2224_){
_start:
{
uint8_t v_res_2225_; lean_object* v_r_2226_; 
v_res_2225_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(v_00_u03b2_2222_, v_m_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_m_2223_);
v_r_2226_ = lean_box(v_res_2225_);
return v_r_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* v_as_2227_, size_t v_sz_2228_, size_t v_i_2229_, lean_object* v_b_2230_, uint8_t v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_2227_, v_sz_2228_, v_i_2229_, v_b_2230_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* v_as_2239_, lean_object* v_sz_2240_, lean_object* v_i_2241_, lean_object* v_b_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
size_t v_sz_boxed_2250_; size_t v_i_boxed_2251_; uint8_t v___y_13039__boxed_2252_; lean_object* v_res_2253_; 
v_sz_boxed_2250_ = lean_unbox_usize(v_sz_2240_);
lean_dec(v_sz_2240_);
v_i_boxed_2251_ = lean_unbox_usize(v_i_2241_);
lean_dec(v_i_2241_);
v___y_13039__boxed_2252_ = lean_unbox(v___y_2243_);
v_res_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_2239_, v_sz_boxed_2250_, v_i_boxed_2251_, v_b_2242_, v___y_13039__boxed_2252_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v_as_2239_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* v_as_2254_, size_t v_i_2255_, size_t v_stop_2256_, lean_object* v_b_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_a_2264_; uint8_t v___x_2268_; 
v___x_2268_ = lean_usize_dec_eq(v_i_2255_, v_stop_2256_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_array_uget_borrowed(v_as_2254_, v_i_2255_);
lean_inc(v___x_2269_);
v___x_2270_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v___x_2269_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2272_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2272_ = l_Array_append___redArg(v_b_2257_, v_a_2271_);
lean_dec(v_a_2271_);
v_a_2264_ = v___x_2272_;
goto v___jp_2263_;
}
else
{
lean_dec_ref(v_b_2257_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2273_; 
v_a_2273_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2270_, 1);
v_a_2264_ = v_a_2273_;
goto v___jp_2263_;
}
else
{
return v___x_2270_;
}
}
}
else
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v_b_2257_);
return v___x_2274_;
}
v___jp_2263_:
{
size_t v___x_2265_; size_t v___x_2266_; 
v___x_2265_ = ((size_t)1ULL);
v___x_2266_ = lean_usize_add(v_i_2255_, v___x_2265_);
v_i_2255_ = v___x_2266_;
v_b_2257_ = v_a_2264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* v_as_2275_, lean_object* v_i_2276_, lean_object* v_stop_2277_, lean_object* v_b_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
size_t v_i_boxed_2284_; size_t v_stop_boxed_2285_; lean_object* v_res_2286_; 
v_i_boxed_2284_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v_stop_boxed_2285_ = lean_unbox_usize(v_stop_2277_);
lean_dec(v_stop_2277_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_2275_, v_i_boxed_2284_, v_stop_boxed_2285_, v_b_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec_ref(v_as_2275_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* v___x_2287_, lean_object* v_decls_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2294_ = lean_mk_empty_array_with_capacity(v___x_2287_);
v___x_2295_ = lean_array_get_size(v_decls_2288_);
v___x_2296_ = lean_nat_dec_lt(v___x_2287_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2294_);
return v___x_2297_;
}
else
{
uint8_t v___x_2298_; 
v___x_2298_ = lean_nat_dec_le(v___x_2295_, v___x_2295_);
if (v___x_2298_ == 0)
{
if (v___x_2296_ == 0)
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2294_);
return v___x_2299_;
}
else
{
size_t v___x_2300_; size_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = ((size_t)0ULL);
v___x_2301_ = lean_usize_of_nat(v___x_2295_);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2288_, v___x_2300_, v___x_2301_, v___x_2294_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2302_;
}
}
else
{
size_t v___x_2303_; size_t v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = ((size_t)0ULL);
v___x_2304_ = lean_usize_of_nat(v___x_2295_);
v___x_2305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2288_, v___x_2303_, v___x_2304_, v___x_2294_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* v___x_2306_, lean_object* v_decls_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(v___x_2306_, v_decls_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec_ref(v_decls_2307_);
lean_dec(v___x_2306_);
return v_res_2313_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = lean_unsigned_to_nat(2803462840u);
v___x_2377_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2378_ = l_Lean_Name_num___override(v___x_2377_, v___x_2376_);
return v___x_2378_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2381_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2382_ = l_Lean_Name_str___override(v___x_2381_, v___x_2380_);
return v___x_2382_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2385_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2386_ = l_Lean_Name_str___override(v___x_2385_, v___x_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = lean_unsigned_to_nat(2u);
v___x_2388_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2389_ = l_Lean_Name_num___override(v___x_2388_, v___x_2387_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2391_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_2392_ = 1;
v___x_2393_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2394_ = l_Lean_registerTraceClass(v___x_2391_, v___x_2392_, v___x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
return v_res_2396_;
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
