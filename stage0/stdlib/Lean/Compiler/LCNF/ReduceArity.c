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
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
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
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
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
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_288_; lean_object* v_fvarId_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_288_ = lean_array_fget_borrowed(v_array_280_, v_start_281_);
v_fvarId_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_fvarId_289_);
v___x_290_ = lean_box(0);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_start_281_, v___x_291_);
lean_dec(v_start_281_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_292_);
v___x_294_ = v___x_284_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_array_280_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_stop_282_);
v___x_294_ = v_reuseFailAlloc_297_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_289_, v___y_277_, v___y_278_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_dec_ref_known(v___x_295_, 1);
v_a_275_ = v___x_294_;
v_b_276_ = v___x_290_;
goto _start;
}
else
{
lean_dec_ref(v___x_294_);
return v___x_295_;
}
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
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_343_ = lean_box(0);
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_add(v_start_336_, v___x_344_);
lean_inc_ref(v_array_335_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_345_);
v___x_347_ = v___x_339_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_array_335_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_351_, 2, v_stop_337_);
v___x_347_ = v_reuseFailAlloc_351_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_array_fget(v_array_335_, v_start_336_);
lean_dec(v_start_336_);
lean_dec_ref(v_array_335_);
v___x_349_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v___x_348_, v___y_332_, v___y_333_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_dec_ref_known(v___x_349_, 1);
v_a_330_ = v___x_347_;
v_b_331_ = v___x_343_;
goto _start;
}
else
{
lean_dec_ref(v___x_347_);
return v___x_349_;
}
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
v___x_786_ = ((lean_object*)(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0));
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_decl_773_);
lean_ctor_set(v___x_787_, 1, v___y_785_);
v___x_788_ = lean_st_mk_ref(v___x_783_);
v___x_789_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v___x_786_, v_value_780_, v___x_787_, v___x_788_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec_ref_known(v___x_787_, 2);
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
v___x_793_ = lean_st_ref_get(v___x_788_);
lean_dec(v___x_788_);
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
lean_dec(v___x_788_);
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
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
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
v___x_860_ = lean_unsigned_to_nat(650u);
v___x_861_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1));
v___x_862_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0));
v___x_863_ = l_mkPanicMessageWithDecl(v___x_862_, v___x_861_, v___x_860_, v___x_859_, v___x_858_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* v_code_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_decl_878_; lean_object* v_k_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; 
switch(lean_obj_tag(v_code_870_))
{
case 0:
{
lean_object* v_decl_992_; lean_object* v_k_993_; lean_object* v_argsNew_995_; lean_object* v___y_996_; lean_object* v_auxDeclName_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v_value_1054_; 
v_decl_992_ = lean_ctor_get(v_code_870_, 0);
v_k_993_ = lean_ctor_get(v_code_870_, 1);
v_value_1054_ = lean_ctor_get(v_decl_992_, 3);
if (lean_obj_tag(v_value_1054_) == 3)
{
lean_object* v_declName_1055_; lean_object* v_args_1056_; lean_object* v_declName_1057_; lean_object* v_auxDeclName_1058_; lean_object* v_paramMask_1059_; uint8_t v_allUnused_1060_; uint8_t v___x_1061_; 
v_declName_1055_ = lean_ctor_get(v_value_1054_, 0);
v_args_1056_ = lean_ctor_get(v_value_1054_, 2);
v_declName_1057_ = lean_ctor_get(v_a_871_, 0);
v_auxDeclName_1058_ = lean_ctor_get(v_a_871_, 1);
v_paramMask_1059_ = lean_ctor_get(v_a_871_, 2);
v_allUnused_1060_ = lean_ctor_get_uint8(v_a_871_, sizeof(void*)*3);
v___x_1061_ = lean_name_eq(v_declName_1055_, v_declName_1057_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
lean_inc_ref(v_k_993_);
v___x_1062_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_993_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1099_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1099_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1099_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
size_t v___x_1067_; size_t v___x_1068_; uint8_t v___x_1069_; 
v___x_1067_ = lean_ptr_addr(v_k_993_);
v___x_1068_ = lean_ptr_addr(v_a_1063_);
v___x_1069_ = lean_usize_dec_eq(v___x_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1079_; 
lean_inc_ref(v_decl_992_);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; lean_object* v_unused_1081_; 
v_unused_1080_ = lean_ctor_get(v_code_870_, 1);
lean_dec(v_unused_1080_);
v_unused_1081_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_1081_);
v___x_1071_ = v_code_870_;
v_isShared_1072_ = v_isSharedCheck_1079_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v_code_870_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1079_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 1, v_a_1063_);
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_decl_992_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_a_1063_);
v___x_1074_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1076_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1074_);
v___x_1076_ = v___x_1065_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
size_t v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = lean_ptr_addr(v_decl_992_);
v___x_1083_ = lean_usize_dec_eq(v___x_1082_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1093_; 
lean_inc_ref(v_decl_992_);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; lean_object* v_unused_1095_; 
v_unused_1094_ = lean_ctor_get(v_code_870_, 1);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_1095_);
v___x_1085_ = v_code_870_;
v_isShared_1086_ = v_isSharedCheck_1093_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v_code_870_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1093_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 1, v_a_1063_);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_decl_992_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_a_1063_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1088_);
v___x_1090_ = v___x_1065_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v___x_1097_; 
lean_dec(v_a_1063_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v_code_870_);
v___x_1097_ = v___x_1065_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_code_870_);
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
lean_dec_ref_known(v_code_870_, 2);
return v___x_1062_;
}
}
else
{
if (v_allUnused_1060_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = lean_array_get_size(v_args_1056_);
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_1103_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1056_, v___x_1100_, v_paramMask_1059_, v___x_1101_, v___x_1102_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v_argsNew_995_ = v_a_1104_;
v___y_996_ = v_a_871_;
v_auxDeclName_997_ = v_auxDeclName_1058_;
v___y_998_ = v_a_872_;
v___y_999_ = v_a_873_;
v___y_1000_ = v_a_874_;
v___y_1001_ = v_a_875_;
goto v___jp_994_;
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref_known(v_code_870_, 2);
v_a_1105_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1103_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1103_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1113_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5));
v___x_1114_ = lean_array_get_size(v_paramMask_1059_);
v___x_1115_ = lean_array_get_size(v_args_1056_);
v___x_1116_ = l_Array_extract___redArg(v_args_1056_, v___x_1114_, v___x_1115_);
v___x_1117_ = l_Array_append___redArg(v___x_1113_, v___x_1116_);
lean_dec_ref(v___x_1116_);
v_argsNew_995_ = v___x_1117_;
v___y_996_ = v_a_871_;
v_auxDeclName_997_ = v_auxDeclName_1058_;
v___y_998_ = v_a_872_;
v___y_999_ = v_a_873_;
v___y_1000_ = v_a_874_;
v___y_1001_ = v_a_875_;
goto v___jp_994_;
}
}
}
else
{
lean_object* v___x_1118_; 
lean_inc_ref(v_k_993_);
v___x_1118_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_993_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1155_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1155_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1155_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
size_t v___x_1123_; size_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1123_ = lean_ptr_addr(v_k_993_);
v___x_1124_ = lean_ptr_addr(v_a_1119_);
v___x_1125_ = lean_usize_dec_eq(v___x_1123_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1135_; 
lean_inc_ref(v_decl_992_);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; lean_object* v_unused_1137_; 
v_unused_1136_ = lean_ctor_get(v_code_870_, 1);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_1137_);
v___x_1127_ = v_code_870_;
v_isShared_1128_ = v_isSharedCheck_1135_;
goto v_resetjp_1126_;
}
else
{
lean_dec(v_code_870_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1135_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 1, v_a_1119_);
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_decl_992_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_a_1119_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1130_);
v___x_1132_ = v___x_1121_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
size_t v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_ptr_addr(v_decl_992_);
v___x_1139_ = lean_usize_dec_eq(v___x_1138_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1149_; 
lean_inc_ref(v_decl_992_);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; lean_object* v_unused_1151_; 
v_unused_1150_ = lean_ctor_get(v_code_870_, 1);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_1151_);
v___x_1141_ = v_code_870_;
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v_code_870_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1149_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v_a_1119_);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_decl_992_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_a_1119_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1144_);
v___x_1146_ = v___x_1121_;
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
lean_object* v___x_1153_; 
lean_dec(v_a_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v_code_870_);
v___x_1153_ = v___x_1121_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_code_870_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_870_, 2);
return v___x_1118_;
}
}
v___jp_994_:
{
uint8_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1002_ = 0;
v___x_1003_ = lean_box(0);
lean_inc(v_auxDeclName_997_);
v___x_1004_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1004_, 0, v_auxDeclName_997_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
lean_ctor_set(v___x_1004_, 2, v_argsNew_995_);
lean_inc_ref(v_decl_992_);
v___x_1005_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1002_, v_decl_992_, v___x_1004_, v___y_999_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
lean_inc_ref(v_k_993_);
v___x_1007_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_993_, v___y_996_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1045_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1045_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1045_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
size_t v___x_1012_; size_t v___x_1013_; uint8_t v___x_1014_; 
v___x_1012_ = lean_ptr_addr(v_k_993_);
v___x_1013_ = lean_ptr_addr(v_a_1008_);
v___x_1014_ = lean_usize_dec_eq(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1024_; 
v_isSharedCheck_1024_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; lean_object* v_unused_1026_; 
v_unused_1025_ = lean_ctor_get(v_code_870_, 1);
lean_dec(v_unused_1025_);
v_unused_1026_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_1026_);
v___x_1016_ = v_code_870_;
v_isShared_1017_ = v_isSharedCheck_1024_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v_code_870_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1024_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v_a_1008_);
lean_ctor_set(v___x_1016_, 0, v_a_1006_);
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1006_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_a_1008_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1019_);
v___x_1021_ = v___x_1010_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
else
{
size_t v___x_1027_; size_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1027_ = lean_ptr_addr(v_decl_992_);
v___x_1028_ = lean_ptr_addr(v_a_1006_);
v___x_1029_ = lean_usize_dec_eq(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1039_; 
v_isSharedCheck_1039_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; lean_object* v_unused_1041_; 
v_unused_1040_ = lean_ctor_get(v_code_870_, 1);
lean_dec(v_unused_1040_);
v_unused_1041_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_1041_);
v___x_1031_ = v_code_870_;
v_isShared_1032_ = v_isSharedCheck_1039_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v_code_870_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1039_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v_a_1008_);
lean_ctor_set(v___x_1031_, 0, v_a_1006_);
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1006_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_a_1008_);
v___x_1034_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1034_);
v___x_1036_ = v___x_1010_;
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
}
else
{
lean_object* v___x_1043_; 
lean_dec(v_a_1008_);
lean_dec(v_a_1006_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v_code_870_);
v___x_1043_ = v___x_1010_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_code_870_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
else
{
lean_dec(v_a_1006_);
lean_dec_ref_known(v_code_870_, 2);
return v___x_1007_;
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref_known(v_code_870_, 2);
v_a_1046_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1005_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1005_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1156_; lean_object* v_k_1157_; 
v_decl_1156_ = lean_ctor_get(v_code_870_, 0);
v_k_1157_ = lean_ctor_get(v_code_870_, 1);
lean_inc_ref(v_k_1157_);
lean_inc_ref(v_decl_1156_);
v_decl_878_ = v_decl_1156_;
v_k_879_ = v_k_1157_;
v___y_880_ = v_a_871_;
v___y_881_ = v_a_872_;
v___y_882_ = v_a_873_;
v___y_883_ = v_a_874_;
v___y_884_ = v_a_875_;
goto v___jp_877_;
}
case 2:
{
lean_object* v_decl_1158_; lean_object* v_k_1159_; 
v_decl_1158_ = lean_ctor_get(v_code_870_, 0);
v_k_1159_ = lean_ctor_get(v_code_870_, 1);
lean_inc_ref(v_k_1159_);
lean_inc_ref(v_decl_1158_);
v_decl_878_ = v_decl_1158_;
v_k_879_ = v_k_1159_;
v___y_880_ = v_a_871_;
v___y_881_ = v_a_872_;
v___y_882_ = v_a_873_;
v___y_883_ = v_a_874_;
v___y_884_ = v_a_875_;
goto v___jp_877_;
}
case 4:
{
lean_object* v_cases_1160_; lean_object* v_typeName_1161_; lean_object* v_resultType_1162_; lean_object* v_discr_1163_; lean_object* v_alts_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1203_; 
v_cases_1160_ = lean_ctor_get(v_code_870_, 0);
lean_inc_ref(v_cases_1160_);
v_typeName_1161_ = lean_ctor_get(v_cases_1160_, 0);
v_resultType_1162_ = lean_ctor_get(v_cases_1160_, 1);
v_discr_1163_ = lean_ctor_get(v_cases_1160_, 2);
v_alts_1164_ = lean_ctor_get(v_cases_1160_, 3);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_cases_1160_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1166_ = v_cases_1160_;
v_isShared_1167_ = v_isSharedCheck_1203_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_alts_1164_);
lean_inc(v_discr_1163_);
lean_inc(v_resultType_1162_);
lean_inc(v_typeName_1161_);
lean_dec(v_cases_1160_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1203_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1164_);
v___x_1169_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v___x_1168_, v_alts_1164_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1194_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1194_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1194_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
size_t v___x_1174_; size_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_ptr_addr(v_alts_1164_);
lean_dec_ref(v_alts_1164_);
v___x_1175_ = lean_ptr_addr(v_a_1170_);
v___x_1176_ = lean_usize_dec_eq(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1189_; 
v_isSharedCheck_1189_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; 
v_unused_1190_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_1190_);
v___x_1178_ = v_code_870_;
v_isShared_1179_ = v_isSharedCheck_1189_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v_code_870_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1189_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 3, v_a_1170_);
v___x_1181_ = v___x_1166_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_typeName_1161_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_resultType_1162_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_discr_1163_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_a_1170_);
v___x_1181_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1181_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1185_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1183_);
v___x_1185_ = v___x_1172_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
else
{
lean_object* v___x_1192_; 
lean_dec(v_a_1170_);
lean_del_object(v___x_1166_);
lean_dec(v_discr_1163_);
lean_dec_ref(v_resultType_1162_);
lean_dec(v_typeName_1161_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v_code_870_);
v___x_1192_ = v___x_1172_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_code_870_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_del_object(v___x_1166_);
lean_dec_ref(v_alts_1164_);
lean_dec(v_discr_1163_);
lean_dec_ref(v_resultType_1162_);
lean_dec(v_typeName_1161_);
lean_dec_ref_known(v_code_870_, 1);
v_a_1195_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1169_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1169_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
default: 
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v_code_870_);
return v___x_1204_;
}
}
v___jp_877_:
{
lean_object* v_params_885_; lean_object* v_type_886_; lean_object* v_value_887_; uint8_t v___x_888_; lean_object* v___x_889_; 
v_params_885_ = lean_ctor_get(v_decl_878_, 2);
lean_inc_ref(v_params_885_);
v_type_886_ = lean_ctor_get(v_decl_878_, 3);
lean_inc_ref(v_type_886_);
v_value_887_ = lean_ctor_get(v_decl_878_, 4);
v___x_888_ = 0;
lean_inc_ref(v_value_887_);
v___x_889_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_value_887_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_891_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_888_, v_decl_878_, v_type_886_, v_params_885_, v_a_890_, v___y_882_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_893_) == 0)
{
switch(lean_obj_tag(v_code_870_))
{
case 1:
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_933_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_933_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_933_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_933_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_decl_898_; lean_object* v_k_899_; size_t v___x_900_; size_t v___x_901_; uint8_t v___x_902_; 
v_decl_898_ = lean_ctor_get(v_code_870_, 0);
v_k_899_ = lean_ctor_get(v_code_870_, 1);
v___x_900_ = lean_ptr_addr(v_k_899_);
v___x_901_ = lean_ptr_addr(v_a_894_);
v___x_902_ = lean_usize_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v_isSharedCheck_912_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; lean_object* v_unused_914_; 
v_unused_913_ = lean_ctor_get(v_code_870_, 1);
lean_dec(v_unused_913_);
v_unused_914_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_914_);
v___x_904_ = v_code_870_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_dec(v_code_870_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v_a_894_);
lean_ctor_set(v___x_904_, 0, v_a_892_);
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_892_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_a_894_);
v___x_907_ = v_reuseFailAlloc_911_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_909_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_907_);
v___x_909_ = v___x_896_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
size_t v___x_915_; size_t v___x_916_; uint8_t v___x_917_; 
v___x_915_ = lean_ptr_addr(v_decl_898_);
v___x_916_ = lean_ptr_addr(v_a_892_);
v___x_917_ = lean_usize_dec_eq(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_927_; 
v_isSharedCheck_927_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; lean_object* v_unused_929_; 
v_unused_928_ = lean_ctor_get(v_code_870_, 1);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_929_);
v___x_919_ = v_code_870_;
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
else
{
lean_dec(v_code_870_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 1, v_a_894_);
lean_ctor_set(v___x_919_, 0, v_a_892_);
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_892_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_a_894_);
v___x_922_ = v_reuseFailAlloc_926_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_922_);
v___x_924_ = v___x_896_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
else
{
lean_object* v___x_931_; 
lean_dec(v_a_894_);
lean_dec(v_a_892_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v_code_870_);
v___x_931_ = v___x_896_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_code_870_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
case 2:
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_973_; 
v_a_934_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_973_ == 0)
{
v___x_936_ = v___x_893_;
v_isShared_937_ = v_isSharedCheck_973_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_893_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_973_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_decl_938_; lean_object* v_k_939_; size_t v___x_940_; size_t v___x_941_; uint8_t v___x_942_; 
v_decl_938_ = lean_ctor_get(v_code_870_, 0);
v_k_939_ = lean_ctor_get(v_code_870_, 1);
v___x_940_ = lean_ptr_addr(v_k_939_);
v___x_941_ = lean_ptr_addr(v_a_934_);
v___x_942_ = lean_usize_dec_eq(v___x_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_952_; 
v_isSharedCheck_952_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; lean_object* v_unused_954_; 
v_unused_953_ = lean_ctor_get(v_code_870_, 1);
lean_dec(v_unused_953_);
v_unused_954_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_954_);
v___x_944_ = v_code_870_;
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
else
{
lean_dec(v_code_870_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v_a_934_);
lean_ctor_set(v___x_944_, 0, v_a_892_);
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_892_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_a_934_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_947_);
v___x_949_ = v___x_936_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
size_t v___x_955_; size_t v___x_956_; uint8_t v___x_957_; 
v___x_955_ = lean_ptr_addr(v_decl_938_);
v___x_956_ = lean_ptr_addr(v_a_892_);
v___x_957_ = lean_usize_dec_eq(v___x_955_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_967_; 
v_isSharedCheck_967_ = !lean_is_exclusive(v_code_870_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; lean_object* v_unused_969_; 
v_unused_968_ = lean_ctor_get(v_code_870_, 1);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v_code_870_, 0);
lean_dec(v_unused_969_);
v___x_959_ = v_code_870_;
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
else
{
lean_dec(v_code_870_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v_a_934_);
lean_ctor_set(v___x_959_, 0, v_a_892_);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_892_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_a_934_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_962_);
v___x_964_ = v___x_936_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v___x_971_; 
lean_dec(v_a_934_);
lean_dec(v_a_892_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_code_870_);
v___x_971_ = v___x_936_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_code_870_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
default: 
{
lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_892_);
lean_dec_ref(v_code_870_);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v___x_893_, 0);
lean_dec(v_unused_983_);
v___x_975_ = v___x_893_;
v_isShared_976_ = v_isSharedCheck_982_;
goto v_resetjp_974_;
}
else
{
lean_dec(v___x_893_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_982_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_977_ = lean_obj_once(&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3, &l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once, _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3);
v___x_978_ = l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(v___x_977_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_978_);
v___x_980_ = v___x_975_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
else
{
lean_dec(v_a_892_);
lean_dec_ref(v_code_870_);
return v___x_893_;
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_k_879_);
lean_dec_ref(v_code_870_);
v_a_984_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_891_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_891_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_dec_ref(v_type_886_);
lean_dec_ref(v_params_885_);
lean_dec_ref(v_k_879_);
lean_dec_ref(v_decl_878_);
lean_dec_ref(v_code_870_);
return v___x_889_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(lean_object* v_i_1205_, lean_object* v_as_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_array_get_size(v_as_1206_);
v___x_1214_ = lean_nat_dec_lt(v_i_1205_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
lean_dec(v_i_1205_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v_as_1206_);
return v___x_1215_;
}
else
{
lean_object* v_a_1216_; lean_object* v___y_1218_; 
v_a_1216_ = lean_array_fget_borrowed(v_as_1206_, v_i_1205_);
switch(lean_obj_tag(v_a_1216_))
{
case 0:
{
lean_object* v_code_1240_; 
v_code_1240_ = lean_ctor_get(v_a_1216_, 2);
lean_inc_ref(v_code_1240_);
v___y_1218_ = v_code_1240_;
goto v___jp_1217_;
}
case 1:
{
lean_object* v_code_1241_; 
v_code_1241_ = lean_ctor_get(v_a_1216_, 1);
lean_inc_ref(v_code_1241_);
v___y_1218_ = v_code_1241_;
goto v___jp_1217_;
}
default: 
{
lean_object* v_code_1242_; 
v_code_1242_ = lean_ctor_get(v_a_1216_, 0);
lean_inc_ref(v_code_1242_);
v___y_1218_ = v_code_1242_;
goto v___jp_1217_;
}
}
v___jp_1217_:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v___y_1218_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; uint8_t v___x_1224_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
lean_inc(v_a_1216_);
v___x_1221_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1216_, v_a_1220_);
v___x_1222_ = lean_ptr_addr(v_a_1216_);
v___x_1223_ = lean_ptr_addr(v___x_1221_);
v___x_1224_ = lean_usize_dec_eq(v___x_1222_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_unsigned_to_nat(1u);
v___x_1226_ = lean_nat_add(v_i_1205_, v___x_1225_);
v___x_1227_ = lean_array_fset(v_as_1206_, v_i_1205_, v___x_1221_);
lean_dec(v_i_1205_);
v_i_1205_ = v___x_1226_;
v_as_1206_ = v___x_1227_;
goto _start;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_dec_ref(v___x_1221_);
v___x_1229_ = lean_unsigned_to_nat(1u);
v___x_1230_ = lean_nat_add(v_i_1205_, v___x_1229_);
lean_dec(v_i_1205_);
v_i_1205_ = v___x_1230_;
goto _start;
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec_ref(v_as_1206_);
lean_dec(v_i_1205_);
v_a_1232_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1219_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1219_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(lean_object* v_i_1243_, lean_object* v_as_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v_i_1243_, v_as_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object* v_code_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_code_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v_a_1253_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object* v_args_1260_, lean_object* v_upperBound_1261_, lean_object* v___x_1262_, lean_object* v_inst_1263_, lean_object* v_R_1264_, lean_object* v_a_1265_, lean_object* v_b_1266_, lean_object* v_c_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1260_, v_upperBound_1261_, v___x_1262_, v_a_1265_, v_b_1266_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object* v_args_1275_, lean_object* v_upperBound_1276_, lean_object* v___x_1277_, lean_object* v_inst_1278_, lean_object* v_R_1279_, lean_object* v_a_1280_, lean_object* v_b_1281_, lean_object* v_c_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(v_args_1275_, v_upperBound_1276_, v___x_1277_, v_inst_1278_, v_R_1279_, v_a_1280_, v_b_1281_, v_c_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v___x_1277_);
lean_dec(v_upperBound_1276_);
lean_dec_ref(v_args_1275_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object* v_f_1290_, lean_object* v_v_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
if (lean_obj_tag(v_v_1291_) == 0)
{
lean_object* v_code_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1322_; 
v_code_1298_ = lean_ctor_get(v_v_1291_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_v_1291_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1300_ = v_v_1291_;
v_isShared_1301_ = v_isSharedCheck_1322_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_code_1298_);
lean_dec(v_v_1291_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1322_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; 
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v___y_1294_);
lean_inc_ref(v___y_1293_);
lean_inc_ref(v___y_1292_);
v___x_1302_ = lean_apply_7(v_f_1290_, v_code_1298_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, lean_box(0));
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1313_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1313_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1313_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v_a_1303_);
v___x_1308_ = v___x_1300_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1310_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1308_);
v___x_1310_ = v___x_1305_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_del_object(v___x_1300_);
v_a_1314_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1302_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1302_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
else
{
lean_object* v___x_1323_; 
lean_dec_ref(v_f_1290_);
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_v_1291_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object* v_f_1324_, lean_object* v_v_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1324_, v_v_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(uint8_t v_pu_1333_, lean_object* v_f_1334_, lean_object* v_v_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1334_, v_v_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object* v_pu_1343_, lean_object* v_f_1344_, lean_object* v_v_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v_pu_boxed_1352_; lean_object* v_res_1353_; 
v_pu_boxed_1352_ = lean_unbox(v_pu_1343_);
v_res_1353_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(v_pu_boxed_1352_, v_f_1344_, v_v_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1353_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1354_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1(void){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2(void){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1357_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
lean_ctor_set(v___x_1359_, 2, v___x_1358_);
lean_ctor_set(v___x_1359_, 3, v___x_1358_);
lean_ctor_set(v___x_1359_, 4, v___x_1357_);
lean_ctor_set(v___x_1359_, 5, v___x_1357_);
lean_ctor_set(v___x_1359_, 6, v___x_1357_);
lean_ctor_set(v___x_1359_, 7, v___x_1357_);
lean_ctor_set(v___x_1359_, 8, v___x_1357_);
lean_ctor_set(v___x_1359_, 9, v___x_1357_);
lean_ctor_set(v___x_1359_, 10, v___x_1357_);
return v___x_1359_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3(void){
_start:
{
lean_object* v___x_1360_; double v___x_1361_; 
v___x_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_float_of_nat(v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* v_cls_1365_, lean_object* v_msg_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_toCold_1372_; lean_object* v_ref_1373_; lean_object* v___x_1374_; lean_object* v_env_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_toCold_1372_ = lean_ctor_get(v___y_1369_, 0);
v_ref_1373_ = lean_ctor_get(v___y_1369_, 2);
v___x_1374_ = lean_st_ref_get(v___y_1370_);
v_env_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref(v_env_1375_);
lean_dec(v___x_1374_);
v___x_1376_ = lean_st_ref_get(v___y_1368_);
v___x_1377_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1367_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1436_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1436_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1436_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_lctx_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1434_; 
v_lctx_1382_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v___x_1376_, 1);
lean_dec(v_unused_1435_);
v___x_1384_ = v___x_1376_;
v_isShared_1385_ = v_isSharedCheck_1434_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_lctx_1382_);
lean_dec(v___x_1376_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1434_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v_options_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v_options_1386_ = lean_ctor_get(v_toCold_1372_, 2);
v___x_1387_ = lean_unbox(v_a_1378_);
lean_dec(v_a_1378_);
v___x_1388_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1382_, v___x_1387_);
lean_dec_ref(v_lctx_1382_);
v___x_1389_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2);
lean_inc_ref(v_options_1386_);
v___x_1390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1390_, 0, v_env_1375_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
lean_ctor_set(v___x_1390_, 2, v___x_1388_);
lean_ctor_set(v___x_1390_, 3, v_options_1386_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set_tag(v___x_1384_, 3);
lean_ctor_set(v___x_1384_, 1, v_msg_1366_);
lean_ctor_set(v___x_1384_, 0, v___x_1390_);
v___x_1392_ = v___x_1384_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_msg_1366_);
v___x_1392_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v_traceState_1394_; lean_object* v_env_1395_; lean_object* v_nextMacroScope_1396_; lean_object* v_ngen_1397_; lean_object* v_auxDeclNGen_1398_; lean_object* v_cache_1399_; lean_object* v_messages_1400_; lean_object* v_infoState_1401_; lean_object* v_snapshotTasks_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1432_; 
v___x_1393_ = lean_st_ref_take(v___y_1370_);
v_traceState_1394_ = lean_ctor_get(v___x_1393_, 4);
v_env_1395_ = lean_ctor_get(v___x_1393_, 0);
v_nextMacroScope_1396_ = lean_ctor_get(v___x_1393_, 1);
v_ngen_1397_ = lean_ctor_get(v___x_1393_, 2);
v_auxDeclNGen_1398_ = lean_ctor_get(v___x_1393_, 3);
v_cache_1399_ = lean_ctor_get(v___x_1393_, 5);
v_messages_1400_ = lean_ctor_get(v___x_1393_, 6);
v_infoState_1401_ = lean_ctor_get(v___x_1393_, 7);
v_snapshotTasks_1402_ = lean_ctor_get(v___x_1393_, 8);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1404_ = v___x_1393_;
v_isShared_1405_ = v_isSharedCheck_1432_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_snapshotTasks_1402_);
lean_inc(v_infoState_1401_);
lean_inc(v_messages_1400_);
lean_inc(v_cache_1399_);
lean_inc(v_traceState_1394_);
lean_inc(v_auxDeclNGen_1398_);
lean_inc(v_ngen_1397_);
lean_inc(v_nextMacroScope_1396_);
lean_inc(v_env_1395_);
lean_dec(v___x_1393_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1432_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint64_t v_tid_1406_; lean_object* v_traces_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1431_; 
v_tid_1406_ = lean_ctor_get_uint64(v_traceState_1394_, sizeof(void*)*1);
v_traces_1407_ = lean_ctor_get(v_traceState_1394_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_traceState_1394_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1409_ = v_traceState_1394_;
v_isShared_1410_ = v_isSharedCheck_1431_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_traces_1407_);
lean_dec(v_traceState_1394_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1431_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; double v___x_1413_; uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_box(0);
v___x_1413_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3);
v___x_1414_ = 0;
v___x_1415_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4));
v___x_1416_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1416_, 0, v_cls_1365_);
lean_ctor_set(v___x_1416_, 1, v___x_1412_);
lean_ctor_set(v___x_1416_, 2, v___x_1415_);
lean_ctor_set_float(v___x_1416_, sizeof(void*)*3, v___x_1413_);
lean_ctor_set_float(v___x_1416_, sizeof(void*)*3 + 8, v___x_1413_);
lean_ctor_set_uint8(v___x_1416_, sizeof(void*)*3 + 16, v___x_1414_);
v___x_1417_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5));
v___x_1418_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1392_);
lean_ctor_set(v___x_1418_, 2, v___x_1417_);
lean_inc(v_ref_1373_);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v_ref_1373_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
v___x_1420_ = l_Lean_PersistentArray_push___redArg(v_traces_1407_, v___x_1419_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1420_);
v___x_1422_ = v___x_1409_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1420_);
lean_ctor_set_uint64(v_reuseFailAlloc_1430_, sizeof(void*)*1, v_tid_1406_);
v___x_1422_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1424_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v___x_1422_);
v___x_1424_ = v___x_1404_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_env_1395_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_nextMacroScope_1396_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_ngen_1397_);
lean_ctor_set(v_reuseFailAlloc_1429_, 3, v_auxDeclNGen_1398_);
lean_ctor_set(v_reuseFailAlloc_1429_, 4, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1429_, 5, v_cache_1399_);
lean_ctor_set(v_reuseFailAlloc_1429_, 6, v_messages_1400_);
lean_ctor_set(v_reuseFailAlloc_1429_, 7, v_infoState_1401_);
lean_ctor_set(v_reuseFailAlloc_1429_, 8, v_snapshotTasks_1402_);
v___x_1424_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_st_ref_put(v___y_1370_, v___x_1424_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1411_);
v___x_1427_ = v___x_1380_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1411_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
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
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v___x_1376_);
lean_dec_ref(v_env_1375_);
lean_dec_ref(v_msg_1366_);
lean_dec(v_cls_1365_);
v_a_1437_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1377_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1377_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___boxed(lean_object* v_cls_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v_cls_1445_, v_msg_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(lean_object* v_name_1454_, lean_object* v___x_1455_, lean_object* v___x_1456_, uint8_t v___x_1457_, lean_object* v_value_1458_, lean_object* v_code_1459_, uint8_t v_safe_1460_, uint8_t v_recursive_1461_, lean_object* v_inlineAttr_x3f_1462_, lean_object* v_params_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_inc(v___x_1455_);
v___x_1469_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1469_, 0, v_name_1454_);
lean_ctor_set(v___x_1469_, 1, v___x_1455_);
lean_ctor_set(v___x_1469_, 2, v___x_1456_);
lean_ctor_set_uint8(v___x_1469_, sizeof(void*)*3, v___x_1457_);
v___x_1470_ = 0;
v___x_1471_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___closed__0));
v___x_1472_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v___x_1471_, v_value_1458_, v___x_1469_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec_ref_known(v___x_1469_, 3);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_1470_, v_code_1459_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
lean_inc_ref(v_params_1463_);
v___x_1476_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_1470_, v_params_1463_, v_a_1475_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v_a_1475_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1479_, 0, v___x_1455_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
lean_ctor_set(v___x_1479_, 2, v_a_1477_);
lean_ctor_set(v___x_1479_, 3, v_params_1463_);
lean_ctor_set_uint8(v___x_1479_, sizeof(void*)*4, v_safe_1460_);
v___x_1480_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
lean_ctor_set(v___x_1480_, 1, v_a_1473_);
lean_ctor_set(v___x_1480_, 2, v_inlineAttr_x3f_1462_);
lean_ctor_set_uint8(v___x_1480_, sizeof(void*)*3, v_recursive_1461_);
lean_inc_ref(v___x_1480_);
v___x_1481_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1480_, v___y_1467_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; 
v_unused_1489_ = lean_ctor_get(v___x_1481_, 0);
lean_dec(v_unused_1489_);
v___x_1483_ = v___x_1481_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_dec(v___x_1481_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1480_);
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1480_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref_known(v___x_1480_, 3);
v_a_1490_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1481_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1481_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_a_1473_);
lean_dec_ref(v_params_1463_);
lean_dec(v_inlineAttr_x3f_1462_);
lean_dec(v___x_1455_);
v_a_1498_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1476_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1476_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v_a_1473_);
lean_dec_ref(v_params_1463_);
lean_dec(v_inlineAttr_x3f_1462_);
lean_dec(v___x_1455_);
v_a_1506_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1474_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1474_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
lean_dec_ref(v_params_1463_);
lean_dec(v_inlineAttr_x3f_1462_);
lean_dec_ref(v_code_1459_);
lean_dec(v___x_1455_);
v_a_1514_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1472_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1472_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed(lean_object* v_name_1522_, lean_object* v___x_1523_, lean_object* v___x_1524_, lean_object* v___x_1525_, lean_object* v_value_1526_, lean_object* v_code_1527_, lean_object* v_safe_1528_, lean_object* v_recursive_1529_, lean_object* v_inlineAttr_x3f_1530_, lean_object* v_params_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
uint8_t v___x_11835__boxed_1537_; uint8_t v_safe_boxed_1538_; uint8_t v_recursive_boxed_1539_; lean_object* v_res_1540_; 
v___x_11835__boxed_1537_ = lean_unbox(v___x_1525_);
v_safe_boxed_1538_ = lean_unbox(v_safe_1528_);
v_recursive_boxed_1539_ = lean_unbox(v_recursive_1529_);
v_res_1540_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(v_name_1522_, v___x_1523_, v___x_1524_, v___x_11835__boxed_1537_, v_value_1526_, v_code_1527_, v_safe_boxed_1538_, v_recursive_boxed_1539_, v_inlineAttr_x3f_1530_, v_params_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(lean_object* v___x_1547_, uint8_t v___x_1548_, lean_object* v_name_1549_, lean_object* v_levelParams_1550_, lean_object* v_type_1551_, lean_object* v_a_1552_, uint8_t v_safe_1553_, uint8_t v___x_1554_, lean_object* v_____r_1555_, lean_object* v_args_1556_, uint8_t v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1547_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
lean_ctor_set(v___x_1565_, 2, v_args_1556_);
v___x_1566_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__1));
v___x_1567_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1548_, v___x_1565_, v___x_1566_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v_fvarId_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v_fvarId_1569_ = lean_ctor_get(v_a_1568_, 0);
lean_inc(v_fvarId_1569_);
v___x_1570_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_fvarId_1569_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_a_1568_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
v___x_1573_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1573_, 0, v_name_1549_);
lean_ctor_set(v___x_1573_, 1, v_levelParams_1550_);
lean_ctor_set(v___x_1573_, 2, v_type_1551_);
lean_ctor_set(v___x_1573_, 3, v_a_1552_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*4, v_safe_1553_);
v___x_1574_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__2));
v___x_1575_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1572_);
lean_ctor_set(v___x_1575_, 2, v___x_1574_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*3, v___x_1554_);
lean_inc_ref(v___x_1575_);
v___x_1576_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1575_, v___y_1562_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v___x_1576_, 0);
lean_dec(v_unused_1584_);
v___x_1578_ = v___x_1576_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_dec(v___x_1576_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1575_);
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1575_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref_known(v___x_1575_, 3);
v_a_1585_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1576_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1576_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec_ref(v_a_1552_);
lean_dec_ref(v_type_1551_);
lean_dec(v_levelParams_1550_);
lean_dec(v_name_1549_);
v_a_1593_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1567_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1567_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___boxed(lean_object** _args){
lean_object* v___x_1601_ = _args[0];
lean_object* v___x_1602_ = _args[1];
lean_object* v_name_1603_ = _args[2];
lean_object* v_levelParams_1604_ = _args[3];
lean_object* v_type_1605_ = _args[4];
lean_object* v_a_1606_ = _args[5];
lean_object* v_safe_1607_ = _args[6];
lean_object* v___x_1608_ = _args[7];
lean_object* v_____r_1609_ = _args[8];
lean_object* v_args_1610_ = _args[9];
lean_object* v___y_1611_ = _args[10];
lean_object* v___y_1612_ = _args[11];
lean_object* v___y_1613_ = _args[12];
lean_object* v___y_1614_ = _args[13];
lean_object* v___y_1615_ = _args[14];
lean_object* v___y_1616_ = _args[15];
lean_object* v___y_1617_ = _args[16];
_start:
{
uint8_t v___x_11979__boxed_1618_; uint8_t v_safe_boxed_1619_; uint8_t v___x_11981__boxed_1620_; uint8_t v___y_11983__boxed_1621_; lean_object* v_res_1622_; 
v___x_11979__boxed_1618_ = lean_unbox(v___x_1602_);
v_safe_boxed_1619_ = lean_unbox(v_safe_1607_);
v___x_11981__boxed_1620_ = lean_unbox(v___x_1608_);
v___y_11983__boxed_1621_ = lean_unbox(v___y_1611_);
v_res_1622_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___x_1601_, v___x_11979__boxed_1618_, v_name_1603_, v_levelParams_1604_, v_type_1605_, v_a_1606_, v_safe_boxed_1619_, v___x_11981__boxed_1620_, v_____r_1609_, v_args_1610_, v___y_11983__boxed_1621_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* v_x_1623_, lean_object* v_x_1624_){
_start:
{
if (lean_obj_tag(v_x_1624_) == 0)
{
lean_inc(v_x_1623_);
return v_x_1623_;
}
else
{
lean_object* v_key_1625_; lean_object* v_tail_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_key_1625_ = lean_ctor_get(v_x_1624_, 0);
v_tail_1626_ = lean_ctor_get(v_x_1624_, 2);
v___x_1627_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1623_, v_tail_1626_);
lean_inc(v_key_1625_);
v___x_1628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1628_, 0, v_key_1625_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object* v_x_1629_, lean_object* v_x_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1629_, v_x_1630_);
lean_dec(v_x_1630_);
lean_dec(v_x_1629_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object* v_as_1632_, size_t v_i_1633_, size_t v_stop_1634_, lean_object* v_b_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = lean_usize_dec_eq(v_i_1633_, v_stop_1634_);
if (v___x_1636_ == 0)
{
size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1637_ = ((size_t)1ULL);
v___x_1638_ = lean_usize_sub(v_i_1633_, v___x_1637_);
v___x_1639_ = lean_array_uget_borrowed(v_as_1632_, v___x_1638_);
v___x_1640_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_b_1635_, v___x_1639_);
lean_dec(v_b_1635_);
v_i_1633_ = v___x_1638_;
v_b_1635_ = v___x_1640_;
goto _start;
}
else
{
return v_b_1635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object* v_as_1642_, lean_object* v_i_1643_, lean_object* v_stop_1644_, lean_object* v_b_1645_){
_start:
{
size_t v_i_boxed_1646_; size_t v_stop_boxed_1647_; lean_object* v_res_1648_; 
v_i_boxed_1646_ = lean_unbox_usize(v_i_1643_);
lean_dec(v_i_1643_);
v_stop_boxed_1647_ = lean_unbox_usize(v_stop_1644_);
lean_dec(v_stop_1644_);
v_res_1648_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_as_1642_, v_i_boxed_1646_, v_stop_boxed_1647_, v_b_1645_);
lean_dec_ref(v_as_1642_);
return v_res_1648_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object* v_m_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_buckets_1651_; lean_object* v___x_1652_; uint64_t v___x_1653_; uint64_t v___x_1654_; uint64_t v___x_1655_; uint64_t v_fold_1656_; uint64_t v___x_1657_; uint64_t v___x_1658_; uint64_t v___x_1659_; size_t v___x_1660_; size_t v___x_1661_; size_t v___x_1662_; size_t v___x_1663_; size_t v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v_buckets_1651_ = lean_ctor_get(v_m_1649_, 1);
v___x_1652_ = lean_array_get_size(v_buckets_1651_);
v___x_1653_ = l_Lean_instHashableFVarId_hash(v_a_1650_);
v___x_1654_ = 32ULL;
v___x_1655_ = lean_uint64_shift_right(v___x_1653_, v___x_1654_);
v_fold_1656_ = lean_uint64_xor(v___x_1653_, v___x_1655_);
v___x_1657_ = 16ULL;
v___x_1658_ = lean_uint64_shift_right(v_fold_1656_, v___x_1657_);
v___x_1659_ = lean_uint64_xor(v_fold_1656_, v___x_1658_);
v___x_1660_ = lean_uint64_to_usize(v___x_1659_);
v___x_1661_ = lean_usize_of_nat(v___x_1652_);
v___x_1662_ = ((size_t)1ULL);
v___x_1663_ = lean_usize_sub(v___x_1661_, v___x_1662_);
v___x_1664_ = lean_usize_land(v___x_1660_, v___x_1663_);
v___x_1665_ = lean_array_uget_borrowed(v_buckets_1651_, v___x_1664_);
v___x_1666_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_1650_, v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object* v_m_1667_, lean_object* v_a_1668_){
_start:
{
uint8_t v_res_1669_; lean_object* v_r_1670_; 
v_res_1669_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1667_, v_a_1668_);
lean_dec(v_a_1668_);
lean_dec_ref(v_m_1667_);
v_r_1670_ = lean_box(v_res_1669_);
return v_r_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* v_a_1671_, lean_object* v_as_1672_, size_t v_i_1673_, size_t v_stop_1674_, lean_object* v_b_1675_){
_start:
{
lean_object* v___y_1677_; uint8_t v___x_1681_; 
v___x_1681_ = lean_usize_dec_eq(v_i_1673_, v_stop_1674_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v_fvarId_1683_; uint8_t v___x_1684_; 
v___x_1682_ = lean_array_uget_borrowed(v_as_1672_, v_i_1673_);
v_fvarId_1683_ = lean_ctor_get(v___x_1682_, 0);
v___x_1684_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1671_, v_fvarId_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
lean_inc(v___x_1682_);
v___x_1685_ = lean_array_push(v_b_1675_, v___x_1682_);
v___y_1677_ = v___x_1685_;
goto v___jp_1676_;
}
else
{
v___y_1677_ = v_b_1675_;
goto v___jp_1676_;
}
}
else
{
return v_b_1675_;
}
v___jp_1676_:
{
size_t v___x_1678_; size_t v___x_1679_; 
v___x_1678_ = ((size_t)1ULL);
v___x_1679_ = lean_usize_add(v_i_1673_, v___x_1678_);
v_i_1673_ = v___x_1679_;
v_b_1675_ = v___y_1677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* v_a_1686_, lean_object* v_as_1687_, lean_object* v_i_1688_, lean_object* v_stop_1689_, lean_object* v_b_1690_){
_start:
{
size_t v_i_boxed_1691_; size_t v_stop_boxed_1692_; lean_object* v_res_1693_; 
v_i_boxed_1691_ = lean_unbox_usize(v_i_1688_);
lean_dec(v_i_1688_);
v_stop_boxed_1692_ = lean_unbox_usize(v_stop_1689_);
lean_dec(v_stop_1689_);
v_res_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1686_, v_as_1687_, v_i_boxed_1691_, v_stop_boxed_1692_, v_b_1690_);
lean_dec_ref(v_as_1687_);
lean_dec_ref(v_a_1686_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
if (lean_obj_tag(v_a_1694_) == 0)
{
lean_object* v___x_1696_; 
v___x_1696_ = l_List_reverse___redArg(v_a_1695_);
return v___x_1696_;
}
else
{
lean_object* v_head_1697_; lean_object* v_tail_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1707_; 
v_head_1697_ = lean_ctor_get(v_a_1694_, 0);
v_tail_1698_ = lean_ctor_get(v_a_1694_, 1);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_a_1694_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1700_ = v_a_1694_;
v_isShared_1701_ = v_isSharedCheck_1707_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_tail_1698_);
lean_inc(v_head_1697_);
lean_dec(v_a_1694_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1707_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = l_Lean_MessageData_ofExpr(v_head_1697_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v_a_1695_);
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_a_1695_);
v___x_1704_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
v_a_1694_ = v_tail_1698_;
v_a_1695_ = v___x_1704_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object* v_as_1708_, size_t v_sz_1709_, size_t v_i_1710_, lean_object* v_b_1711_){
_start:
{
lean_object* v_a_1714_; uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_lt(v_i_1710_, v_sz_1709_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_b_1711_);
return v___x_1719_;
}
else
{
lean_object* v_snd_1720_; lean_object* v_fst_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1756_; 
v_snd_1720_ = lean_ctor_get(v_b_1711_, 1);
v_fst_1721_ = lean_ctor_get(v_b_1711_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_b_1711_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1723_ = v_b_1711_;
v_isShared_1724_ = v_isSharedCheck_1756_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_snd_1720_);
lean_inc(v_fst_1721_);
lean_dec(v_b_1711_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1756_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_array_1725_; lean_object* v_start_1726_; lean_object* v_stop_1727_; uint8_t v___x_1728_; 
v_array_1725_ = lean_ctor_get(v_snd_1720_, 0);
v_start_1726_ = lean_ctor_get(v_snd_1720_, 1);
v_stop_1727_ = lean_ctor_get(v_snd_1720_, 2);
v___x_1728_ = lean_nat_dec_lt(v_start_1726_, v_stop_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1730_; 
if (v_isShared_1724_ == 0)
{
v___x_1730_ = v___x_1723_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_fst_1721_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_snd_1720_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
else
{
lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1752_; 
lean_inc(v_stop_1727_);
lean_inc(v_start_1726_);
lean_inc_ref(v_array_1725_);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_snd_1720_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; lean_object* v_unused_1754_; lean_object* v_unused_1755_; 
v_unused_1753_ = lean_ctor_get(v_snd_1720_, 2);
lean_dec(v_unused_1753_);
v_unused_1754_ = lean_ctor_get(v_snd_1720_, 1);
lean_dec(v_unused_1754_);
v_unused_1755_ = lean_ctor_get(v_snd_1720_, 0);
lean_dec(v_unused_1755_);
v___x_1734_ = v_snd_1720_;
v_isShared_1735_ = v_isSharedCheck_1752_;
goto v_resetjp_1733_;
}
else
{
lean_dec(v_snd_1720_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1752_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_a_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v_a_1736_ = lean_array_uget_borrowed(v_as_1708_, v_i_1710_);
v___x_1737_ = lean_array_fget(v_array_1725_, v_start_1726_);
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_start_1726_, v___x_1738_);
lean_dec(v_start_1726_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1739_);
v___x_1741_ = v___x_1734_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_array_1725_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_stop_1727_);
v___x_1741_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_unbox(v_a_1736_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1744_; 
lean_dec(v___x_1737_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v___x_1741_);
v___x_1744_ = v___x_1723_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_fst_1721_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___x_1741_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v_a_1714_ = v___x_1744_;
goto v___jp_1713_;
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1746_ = l_Lean_Compiler_LCNF_Param_toArg___redArg(v___x_1737_);
lean_dec(v___x_1737_);
v___x_1747_ = lean_array_push(v_fst_1721_, v___x_1746_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 1, v___x_1741_);
lean_ctor_set(v___x_1723_, 0, v___x_1747_);
v___x_1749_ = v___x_1723_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___x_1741_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
v_a_1714_ = v___x_1749_;
goto v___jp_1713_;
}
}
}
}
}
}
}
v___jp_1713_:
{
size_t v___x_1715_; size_t v___x_1716_; 
v___x_1715_ = ((size_t)1ULL);
v___x_1716_ = lean_usize_add(v_i_1710_, v___x_1715_);
v_i_1710_ = v___x_1716_;
v_b_1711_ = v_a_1714_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object* v_as_1757_, lean_object* v_sz_1758_, lean_object* v_i_1759_, lean_object* v_b_1760_, lean_object* v___y_1761_){
_start:
{
size_t v_sz_boxed_1762_; size_t v_i_boxed_1763_; lean_object* v_res_1764_; 
v_sz_boxed_1762_ = lean_unbox_usize(v_sz_1758_);
lean_dec(v_sz_1758_);
v_i_boxed_1763_ = lean_unbox_usize(v_i_1759_);
lean_dec(v_i_1759_);
v_res_1764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_1757_, v_sz_boxed_1762_, v_i_boxed_1763_, v_b_1760_);
lean_dec_ref(v_as_1757_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t v_sz_1765_, size_t v_i_1766_, lean_object* v_bs_1767_, uint8_t v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_usize_dec_lt(v_i_1766_, v_sz_1765_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_bs_1767_);
return v___x_1776_;
}
else
{
uint8_t v___x_1777_; lean_object* v_v_1778_; lean_object* v___x_1779_; lean_object* v_bs_x27_1780_; lean_object* v___x_1781_; 
v___x_1777_ = 0;
v_v_1778_ = lean_array_uget(v_bs_1767_, v_i_1766_);
v___x_1779_ = lean_unsigned_to_nat(0u);
v_bs_x27_1780_ = lean_array_uset(v_bs_1767_, v_i_1766_, v___x_1779_);
v___x_1781_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_1777_, v_v_1778_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1781_, 1);
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = lean_usize_add(v_i_1766_, v___x_1783_);
v___x_1785_ = lean_array_uset(v_bs_x27_1780_, v_i_1766_, v_a_1782_);
v_i_1766_ = v___x_1784_;
v_bs_1767_ = v___x_1785_;
goto _start;
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_bs_x27_1780_);
v_a_1787_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1781_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1781_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* v_sz_1795_, lean_object* v_i_1796_, lean_object* v_bs_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
size_t v_sz_boxed_1805_; size_t v_i_boxed_1806_; uint8_t v___y_12280__boxed_1807_; lean_object* v_res_1808_; 
v_sz_boxed_1805_ = lean_unbox_usize(v_sz_1795_);
lean_dec(v_sz_1795_);
v_i_boxed_1806_ = lean_unbox_usize(v_i_1796_);
lean_dec(v_i_1796_);
v___y_12280__boxed_1807_ = lean_unbox(v___y_1798_);
v_res_1808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_boxed_1805_, v_i_boxed_1806_, v_bs_1797_, v___y_12280__boxed_1807_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
if (lean_obj_tag(v_a_1809_) == 0)
{
lean_object* v___x_1811_; 
v___x_1811_ = l_List_reverse___redArg(v_a_1810_);
return v___x_1811_;
}
else
{
lean_object* v_head_1812_; lean_object* v_tail_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1822_; 
v_head_1812_ = lean_ctor_get(v_a_1809_, 0);
v_tail_1813_ = lean_ctor_get(v_a_1809_, 1);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_a_1809_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1815_ = v_a_1809_;
v_isShared_1816_ = v_isSharedCheck_1822_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_tail_1813_);
lean_inc(v_head_1812_);
lean_dec(v_a_1809_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1822_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = l_Lean_mkFVar(v_head_1812_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 1, v_a_1810_);
lean_ctor_set(v___x_1815_, 0, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_a_1810_);
v___x_1819_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
v_a_1809_ = v_tail_1813_;
v_a_1810_ = v___x_1819_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(lean_object* v_a_1823_, lean_object* v_as_1824_, size_t v_i_1825_, size_t v_stop_1826_, lean_object* v_b_1827_){
_start:
{
lean_object* v___y_1829_; uint8_t v___x_1833_; 
v___x_1833_ = lean_usize_dec_eq(v_i_1825_, v_stop_1826_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v_fvarId_1835_; uint8_t v___x_1836_; 
v___x_1834_ = lean_array_uget_borrowed(v_as_1824_, v_i_1825_);
v_fvarId_1835_ = lean_ctor_get(v___x_1834_, 0);
v___x_1836_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1823_, v_fvarId_1835_);
if (v___x_1836_ == 0)
{
v___y_1829_ = v_b_1827_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1837_; 
lean_inc(v___x_1834_);
v___x_1837_ = lean_array_push(v_b_1827_, v___x_1834_);
v___y_1829_ = v___x_1837_;
goto v___jp_1828_;
}
}
else
{
return v_b_1827_;
}
v___jp_1828_:
{
size_t v___x_1830_; size_t v___x_1831_; 
v___x_1830_ = ((size_t)1ULL);
v___x_1831_ = lean_usize_add(v_i_1825_, v___x_1830_);
v_i_1825_ = v___x_1831_;
v_b_1827_ = v___y_1829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6___boxed(lean_object* v_a_1838_, lean_object* v_as_1839_, lean_object* v_i_1840_, lean_object* v_stop_1841_, lean_object* v_b_1842_){
_start:
{
size_t v_i_boxed_1843_; size_t v_stop_boxed_1844_; lean_object* v_res_1845_; 
v_i_boxed_1843_ = lean_unbox_usize(v_i_1840_);
lean_dec(v_i_1840_);
v_stop_boxed_1844_ = lean_unbox_usize(v_stop_1841_);
lean_dec(v_stop_1841_);
v_res_1845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1838_, v_as_1839_, v_i_boxed_1843_, v_stop_boxed_1844_, v_b_1842_);
lean_dec_ref(v_as_1839_);
lean_dec_ref(v_a_1838_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object* v_a_1846_, lean_object* v_as_1847_, size_t v_i_1848_, size_t v_stop_1849_, lean_object* v_b_1850_){
_start:
{
lean_object* v___y_1852_; uint8_t v___x_1856_; 
v___x_1856_ = lean_usize_dec_eq(v_i_1848_, v_stop_1849_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v_fvarId_1858_; uint8_t v___x_1859_; 
v___x_1857_ = lean_array_uget_borrowed(v_as_1847_, v_i_1848_);
v_fvarId_1858_ = lean_ctor_get(v___x_1857_, 0);
v___x_1859_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1846_, v_fvarId_1858_);
if (v___x_1859_ == 0)
{
v___y_1852_ = v_b_1850_;
goto v___jp_1851_;
}
else
{
lean_object* v___x_1860_; 
lean_inc(v___x_1857_);
v___x_1860_ = lean_array_push(v_b_1850_, v___x_1857_);
v___y_1852_ = v___x_1860_;
goto v___jp_1851_;
}
}
else
{
return v_b_1850_;
}
v___jp_1851_:
{
size_t v___x_1853_; size_t v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_add(v_i_1848_, v___x_1853_);
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1846_, v_as_1847_, v___x_1854_, v_stop_1849_, v___y_1852_);
return v___x_1855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object* v_a_1861_, lean_object* v_as_1862_, lean_object* v_i_1863_, lean_object* v_stop_1864_, lean_object* v_b_1865_){
_start:
{
size_t v_i_boxed_1866_; size_t v_stop_boxed_1867_; lean_object* v_res_1868_; 
v_i_boxed_1866_ = lean_unbox_usize(v_i_1863_);
lean_dec(v_i_1863_);
v_stop_boxed_1867_ = lean_unbox_usize(v_stop_1864_);
lean_dec(v_stop_1864_);
v_res_1868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1861_, v_as_1862_, v_i_boxed_1866_, v_stop_boxed_1867_, v_b_1865_);
lean_dec_ref(v_as_1862_);
lean_dec_ref(v_a_1861_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object* v_a_1869_, size_t v_sz_1870_, size_t v_i_1871_, lean_object* v_bs_1872_){
_start:
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_usize_dec_lt(v_i_1871_, v_sz_1870_);
if (v___x_1873_ == 0)
{
return v_bs_1872_;
}
else
{
lean_object* v_v_1874_; lean_object* v_fvarId_1875_; lean_object* v___x_1876_; lean_object* v_bs_x27_1877_; uint8_t v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_v_1874_ = lean_array_uget_borrowed(v_bs_1872_, v_i_1871_);
v_fvarId_1875_ = lean_ctor_get(v_v_1874_, 0);
lean_inc(v_fvarId_1875_);
v___x_1876_ = lean_unsigned_to_nat(0u);
v_bs_x27_1877_ = lean_array_uset(v_bs_1872_, v_i_1871_, v___x_1876_);
v___x_1878_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1869_, v_fvarId_1875_);
lean_dec(v_fvarId_1875_);
v___x_1879_ = ((size_t)1ULL);
v___x_1880_ = lean_usize_add(v_i_1871_, v___x_1879_);
v___x_1881_ = lean_box(v___x_1878_);
v___x_1882_ = lean_array_uset(v_bs_x27_1877_, v_i_1871_, v___x_1881_);
v_i_1871_ = v___x_1880_;
v_bs_1872_ = v___x_1882_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object* v_a_1884_, lean_object* v_sz_1885_, lean_object* v_i_1886_, lean_object* v_bs_1887_){
_start:
{
size_t v_sz_boxed_1888_; size_t v_i_boxed_1889_; lean_object* v_res_1890_; 
v_sz_boxed_1888_ = lean_unbox_usize(v_sz_1885_);
lean_dec(v_sz_1885_);
v_i_boxed_1889_ = lean_unbox_usize(v_i_1886_);
lean_dec(v_i_1886_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1884_, v_sz_boxed_1888_, v_i_boxed_1889_, v_bs_1887_);
lean_dec_ref(v_a_1884_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* v_a_1891_, size_t v_sz_1892_, size_t v_i_1893_, lean_object* v_bs_1894_){
_start:
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_usize_dec_lt(v_i_1893_, v_sz_1892_);
if (v___x_1895_ == 0)
{
return v_bs_1894_;
}
else
{
lean_object* v_v_1896_; lean_object* v_fvarId_1897_; lean_object* v___x_1898_; lean_object* v_bs_x27_1899_; uint8_t v___x_1900_; size_t v___x_1901_; size_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_v_1896_ = lean_array_uget_borrowed(v_bs_1894_, v_i_1893_);
v_fvarId_1897_ = lean_ctor_get(v_v_1896_, 0);
lean_inc(v_fvarId_1897_);
v___x_1898_ = lean_unsigned_to_nat(0u);
v_bs_x27_1899_ = lean_array_uset(v_bs_1894_, v_i_1893_, v___x_1898_);
v___x_1900_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1891_, v_fvarId_1897_);
lean_dec(v_fvarId_1897_);
v___x_1901_ = ((size_t)1ULL);
v___x_1902_ = lean_usize_add(v_i_1893_, v___x_1901_);
v___x_1903_ = lean_box(v___x_1900_);
v___x_1904_ = lean_array_uset(v_bs_x27_1899_, v_i_1893_, v___x_1903_);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1891_, v_sz_1892_, v___x_1902_, v___x_1904_);
return v___x_1905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object* v_a_1906_, lean_object* v_sz_1907_, lean_object* v_i_1908_, lean_object* v_bs_1909_){
_start:
{
size_t v_sz_boxed_1910_; size_t v_i_boxed_1911_; lean_object* v_res_1912_; 
v_sz_boxed_1910_ = lean_unbox_usize(v_sz_1907_);
lean_dec(v_sz_1907_);
v_i_boxed_1911_ = lean_unbox_usize(v_i_1908_);
lean_dec(v_i_1908_);
v_res_1912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1906_, v_sz_boxed_1910_, v_i_boxed_1911_, v_bs_1909_);
lean_dec_ref(v_a_1906_);
return v_res_1912_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_box(0);
v___x_1914_ = lean_unsigned_to_nat(16u);
v___x_1915_ = lean_mk_array(v___x_1914_, v___x_1913_);
return v___x_1915_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0);
v___x_1917_ = lean_unsigned_to_nat(0u);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v___x_1916_);
return v___x_1918_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = lean_box(0);
v___x_1928_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6));
v___x_1929_ = l_Lean_Expr_const___override(v___x_1928_, v___x_1927_);
return v___x_1929_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_1942_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14));
v___x_1943_ = l_Lean_Name_append(v___x_1942_, v___x_1941_);
return v___x_1943_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16));
v___x_1946_ = l_Lean_stringToMessageData(v___x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* v_decl_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v___y_1954_; lean_object* v___y_1955_; uint8_t v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v_value_1991_; 
v_value_1991_ = lean_ctor_get(v_decl_1947_, 1);
lean_inc_ref(v_value_1991_);
if (lean_obj_tag(v_value_1991_) == 0)
{
lean_object* v_toSignature_1992_; uint8_t v_recursive_1993_; lean_object* v_inlineAttr_x3f_1994_; lean_object* v_code_1995_; lean_object* v_name_1996_; lean_object* v_levelParams_1997_; lean_object* v_type_1998_; lean_object* v_params_1999_; uint8_t v_safe_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_toSignature_1992_ = lean_ctor_get(v_decl_1947_, 0);
v_recursive_1993_ = lean_ctor_get_uint8(v_decl_1947_, sizeof(void*)*3);
v_inlineAttr_x3f_1994_ = lean_ctor_get(v_decl_1947_, 2);
v_code_1995_ = lean_ctor_get(v_value_1991_, 0);
v_name_1996_ = lean_ctor_get(v_toSignature_1992_, 0);
v_levelParams_1997_ = lean_ctor_get(v_toSignature_1992_, 1);
v_type_1998_ = lean_ctor_get(v_toSignature_1992_, 2);
v_params_1999_ = lean_ctor_get(v_toSignature_1992_, 3);
v_safe_2000_ = lean_ctor_get_uint8(v_toSignature_1992_, sizeof(void*)*4);
v___x_2001_ = lean_array_get_size(v_params_1999_);
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = lean_nat_dec_eq(v___x_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
lean_inc_ref(v_code_1995_);
lean_inc_ref(v_decl_1947_);
v___x_2004_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2179_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2179_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2179_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v_size_2009_; lean_object* v_buckets_2010_; uint8_t v___x_2011_; 
v_size_2009_ = lean_ctor_get(v_a_2005_, 0);
v_buckets_2010_ = lean_ctor_get(v_a_2005_, 1);
v___x_2011_ = lean_nat_dec_eq(v_size_2009_, v___x_2001_);
if (v___x_2011_ == 0)
{
lean_object* v_toCold_2012_; lean_object* v_options_2013_; lean_object* v_inheritedTraceOptions_2014_; uint8_t v_hasTrace_2015_; uint8_t v___x_2016_; lean_object* v___y_2018_; uint8_t v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; size_t v___y_2023_; lean_object* v___y_2024_; uint8_t v___y_2025_; lean_object* v___y_2026_; size_t v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2074_; uint8_t v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; size_t v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; uint8_t v___y_2082_; size_t v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; size_t v___y_2094_; lean_object* v___y_2095_; uint8_t v___y_2096_; lean_object* v___y_2097_; size_t v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; 
lean_inc_ref(v_params_1999_);
lean_inc_ref(v_type_1998_);
lean_inc(v_levelParams_1997_);
lean_inc(v_name_1996_);
lean_inc(v_inlineAttr_x3f_1994_);
lean_del_object(v___x_2007_);
lean_dec_ref(v_decl_1947_);
v_toCold_2012_ = lean_ctor_get(v_a_1950_, 0);
v_options_2013_ = lean_ctor_get(v_toCold_2012_, 2);
v_inheritedTraceOptions_2014_ = lean_ctor_get(v_toCold_2012_, 11);
v_hasTrace_2015_ = lean_ctor_get_uint8(v_options_2013_, sizeof(void*)*1);
v___x_2016_ = lean_nat_dec_eq(v_size_2009_, v___x_2002_);
if (v_hasTrace_2015_ == 0)
{
v___y_2124_ = v_a_1948_;
v___y_2125_ = v_a_1949_;
v___y_2126_ = v_a_1950_;
v___y_2127_ = v_a_1951_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2145_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_2146_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15);
v___x_2147_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2014_, v_options_2013_, v___x_2146_);
if (v___x_2147_ == 0)
{
v___y_2124_ = v_a_1948_;
v___y_2125_ = v_a_1949_;
v___y_2126_ = v_a_1950_;
v___y_2127_ = v_a_1951_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___y_2152_; lean_object* v___x_2167_; lean_object* v___x_2168_; uint8_t v___x_2169_; 
lean_inc(v_name_1996_);
v___x_2148_ = l_Lean_MessageData_ofName(v_name_1996_);
v___x_2149_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2167_ = lean_box(0);
v___x_2168_ = lean_array_get_size(v_buckets_2010_);
v___x_2169_ = lean_nat_dec_lt(v___x_2002_, v___x_2168_);
if (v___x_2169_ == 0)
{
v___y_2152_ = v___x_2167_;
goto v___jp_2151_;
}
else
{
size_t v___x_2170_; size_t v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_usize_of_nat(v___x_2168_);
v___x_2171_ = ((size_t)0ULL);
v___x_2172_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_buckets_2010_, v___x_2170_, v___x_2171_, v___x_2167_);
v___y_2152_ = v___x_2172_;
goto v___jp_2151_;
}
v___jp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2153_ = lean_box(0);
v___x_2154_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(v___y_2152_, v___x_2153_);
v___x_2155_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(v___x_2154_, v___x_2153_);
v___x_2156_ = l_Lean_MessageData_ofList(v___x_2155_);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2150_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v___x_2145_, v___x_2157_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_dec_ref_known(v___x_2158_, 1);
v___y_2124_ = v_a_1948_;
v___y_2125_ = v_a_1949_;
v___y_2126_ = v_a_1950_;
v___y_2127_ = v_a_1951_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_a_2005_);
lean_dec_ref(v_params_1999_);
lean_dec_ref(v_type_1998_);
lean_dec(v_levelParams_1997_);
lean_dec(v_name_1996_);
lean_dec_ref(v_code_1995_);
lean_dec(v_inlineAttr_x3f_1994_);
lean_dec_ref_known(v_value_1991_, 1);
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
}
v___jp_2017_:
{
if (lean_obj_tag(v___y_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v_a_2030_ = lean_ctor_get(v___y_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___y_2029_, 1);
v___x_2031_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1);
v___x_2032_ = lean_st_mk_ref(v___x_2031_);
v___x_2033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v___y_2023_, v___y_2027_, v_params_1999_, v___x_2011_, v___x_2032_, v___y_2026_, v___y_2024_, v___y_2022_, v___y_2021_);
if (lean_obj_tag(v___x_2033_) == 0)
{
if (v___x_2016_ == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; size_t v_sz_2039_; lean_object* v___x_2040_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc_n(v_a_2034_, 2);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_2036_ = lean_array_get_size(v_a_2034_);
v___x_2037_ = l_Array_toSubarray___redArg(v_a_2034_, v___x_2002_, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2035_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v_sz_2039_ = lean_array_size(v___y_2020_);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v___y_2020_, v_sz_2039_, v___y_2027_, v___x_2038_);
lean_dec_ref(v___y_2020_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v_fst_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v_fst_2042_ = lean_ctor_get(v_a_2041_, 0);
lean_inc(v_fst_2042_);
lean_dec(v_a_2041_);
v___x_2043_ = lean_box(0);
v___x_2044_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___y_2018_, v___y_2019_, v_name_1996_, v_levelParams_1997_, v_type_1998_, v_a_2034_, v_safe_2000_, v___x_2011_, v___x_2043_, v_fst_2042_, v___x_2011_, v___x_2032_, v___y_2026_, v___y_2024_, v___y_2022_, v___y_2021_);
v___y_1954_ = v_a_2030_;
v___y_1955_ = v___y_2024_;
v___y_1956_ = v___y_2025_;
v___y_1957_ = v___x_2032_;
v___y_1958_ = v___y_2028_;
v___y_1959_ = v___x_2044_;
goto v___jp_1953_;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_2034_);
lean_dec(v___x_2032_);
lean_dec(v_a_2030_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2018_);
lean_dec_ref(v_type_1998_);
lean_dec(v_levelParams_1997_);
lean_dec(v_name_1996_);
v_a_2045_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2040_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2040_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec_ref(v___y_2020_);
v_a_2053_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2054_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5));
v___x_2055_ = lean_box(0);
v___x_2056_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___y_2018_, v___y_2019_, v_name_1996_, v_levelParams_1997_, v_type_1998_, v_a_2053_, v_safe_2000_, v___x_2011_, v___x_2055_, v___x_2054_, v___x_2011_, v___x_2032_, v___y_2026_, v___y_2024_, v___y_2022_, v___y_2021_);
v___y_1954_ = v_a_2030_;
v___y_1955_ = v___y_2024_;
v___y_1956_ = v___y_2025_;
v___y_1957_ = v___x_2032_;
v___y_1958_ = v___y_2028_;
v___y_1959_ = v___x_2056_;
goto v___jp_1953_;
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v___x_2032_);
lean_dec(v_a_2030_);
lean_dec_ref(v___y_2028_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2018_);
lean_dec_ref(v_type_1998_);
lean_dec(v_levelParams_1997_);
lean_dec(v_name_1996_);
v_a_2057_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2033_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2033_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v___y_2028_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2018_);
lean_dec_ref(v_params_1999_);
lean_dec_ref(v_type_1998_);
lean_dec(v_levelParams_1997_);
lean_dec(v_name_1996_);
v_a_2065_ = lean_ctor_get(v___y_2029_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___y_2029_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___y_2029_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___y_2029_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
v___jp_2073_:
{
lean_object* v___x_2087_; 
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2080_);
lean_inc(v___y_2081_);
lean_inc_ref(v___y_2084_);
v___x_2087_ = lean_apply_6(v___y_2077_, v___y_2086_, v___y_2084_, v___y_2081_, v___y_2080_, v___y_2079_, lean_box(0));
v___y_2018_ = v___y_2074_;
v___y_2019_ = v___y_2075_;
v___y_2020_ = v___y_2076_;
v___y_2021_ = v___y_2079_;
v___y_2022_ = v___y_2080_;
v___y_2023_ = v___y_2078_;
v___y_2024_ = v___y_2081_;
v___y_2025_ = v___y_2082_;
v___y_2026_ = v___y_2084_;
v___y_2027_ = v___y_2083_;
v___y_2028_ = v___y_2085_;
v___y_2029_ = v___x_2087_;
goto v___jp_2017_;
}
v___jp_2088_:
{
if (v___x_2016_ == 0)
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_2101_ = lean_nat_dec_lt(v___x_2002_, v___x_2001_);
if (v___x_2101_ == 0)
{
lean_dec(v_a_2005_);
v___y_2074_ = v___y_2089_;
v___y_2075_ = v___y_2096_;
v___y_2076_ = v___y_2090_;
v___y_2077_ = v___y_2091_;
v___y_2078_ = v___y_2094_;
v___y_2079_ = v___y_2093_;
v___y_2080_ = v___y_2092_;
v___y_2081_ = v___y_2095_;
v___y_2082_ = v___y_2096_;
v___y_2083_ = v___y_2098_;
v___y_2084_ = v___y_2097_;
v___y_2085_ = v___y_2099_;
v___y_2086_ = v___x_2100_;
goto v___jp_2073_;
}
else
{
uint8_t v___x_2102_; 
v___x_2102_ = lean_nat_dec_le(v___x_2001_, v___x_2001_);
if (v___x_2102_ == 0)
{
if (v___x_2101_ == 0)
{
lean_dec(v_a_2005_);
v___y_2074_ = v___y_2089_;
v___y_2075_ = v___y_2096_;
v___y_2076_ = v___y_2090_;
v___y_2077_ = v___y_2091_;
v___y_2078_ = v___y_2094_;
v___y_2079_ = v___y_2093_;
v___y_2080_ = v___y_2092_;
v___y_2081_ = v___y_2095_;
v___y_2082_ = v___y_2096_;
v___y_2083_ = v___y_2098_;
v___y_2084_ = v___y_2097_;
v___y_2085_ = v___y_2099_;
v___y_2086_ = v___x_2100_;
goto v___jp_2073_;
}
else
{
size_t v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = lean_usize_of_nat(v___x_2001_);
v___x_2104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_2005_, v_params_1999_, v___y_2098_, v___x_2103_, v___x_2100_);
lean_dec(v_a_2005_);
v___y_2074_ = v___y_2089_;
v___y_2075_ = v___y_2096_;
v___y_2076_ = v___y_2090_;
v___y_2077_ = v___y_2091_;
v___y_2078_ = v___y_2094_;
v___y_2079_ = v___y_2093_;
v___y_2080_ = v___y_2092_;
v___y_2081_ = v___y_2095_;
v___y_2082_ = v___y_2096_;
v___y_2083_ = v___y_2098_;
v___y_2084_ = v___y_2097_;
v___y_2085_ = v___y_2099_;
v___y_2086_ = v___x_2104_;
goto v___jp_2073_;
}
}
else
{
size_t v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_usize_of_nat(v___x_2001_);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_2005_, v_params_1999_, v___y_2098_, v___x_2105_, v___x_2100_);
lean_dec(v_a_2005_);
v___y_2074_ = v___y_2089_;
v___y_2075_ = v___y_2096_;
v___y_2076_ = v___y_2090_;
v___y_2077_ = v___y_2091_;
v___y_2078_ = v___y_2094_;
v___y_2079_ = v___y_2093_;
v___y_2080_ = v___y_2092_;
v___y_2081_ = v___y_2095_;
v___y_2082_ = v___y_2096_;
v___y_2083_ = v___y_2098_;
v___y_2084_ = v___y_2097_;
v___y_2085_ = v___y_2099_;
v___y_2086_ = v___x_2106_;
goto v___jp_2073_;
}
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_dec(v_a_2005_);
v___x_2107_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4));
v___x_2108_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7);
v___x_2109_ = l_Lean_Compiler_LCNF_mkParam(v___y_2096_, v___x_2107_, v___x_2108_, v___x_2011_, v___y_2097_, v___y_2095_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2111_ = lean_unsigned_to_nat(1u);
v___x_2112_ = lean_mk_empty_array_with_capacity(v___x_2111_);
v___x_2113_ = lean_array_push(v___x_2112_, v_a_2110_);
lean_inc(v___y_2093_);
lean_inc_ref(v___y_2092_);
lean_inc(v___y_2095_);
lean_inc_ref(v___y_2097_);
v___x_2114_ = lean_apply_6(v___y_2091_, v___x_2113_, v___y_2097_, v___y_2095_, v___y_2092_, v___y_2093_, lean_box(0));
v___y_2018_ = v___y_2089_;
v___y_2019_ = v___y_2096_;
v___y_2020_ = v___y_2090_;
v___y_2021_ = v___y_2093_;
v___y_2022_ = v___y_2092_;
v___y_2023_ = v___y_2094_;
v___y_2024_ = v___y_2095_;
v___y_2025_ = v___y_2096_;
v___y_2026_ = v___y_2097_;
v___y_2027_ = v___y_2098_;
v___y_2028_ = v___y_2099_;
v___y_2029_ = v___x_2114_;
goto v___jp_2017_;
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v___y_2099_);
lean_dec_ref(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v_params_1999_);
lean_dec_ref(v_type_1998_);
lean_dec(v_levelParams_1997_);
lean_dec(v_name_1996_);
v_a_2115_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2109_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2109_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
}
v___jp_2123_:
{
size_t v_sz_2128_; size_t v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___f_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v_sz_2128_ = lean_array_size(v_params_1999_);
v___x_2129_ = ((size_t)0ULL);
lean_inc_ref(v_params_1999_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_2005_, v_sz_2128_, v___x_2129_, v_params_1999_);
v___x_2131_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9));
lean_inc_n(v_name_1996_, 2);
v___x_2132_ = l_Lean_Name_append(v_name_1996_, v___x_2131_);
v___x_2133_ = lean_box(v___x_2016_);
v___x_2134_ = lean_box(v_safe_2000_);
v___x_2135_ = lean_box(v_recursive_1993_);
lean_inc_ref(v___x_2130_);
lean_inc(v___x_2132_);
v___f_2136_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2136_, 0, v_name_1996_);
lean_closure_set(v___f_2136_, 1, v___x_2132_);
lean_closure_set(v___f_2136_, 2, v___x_2130_);
lean_closure_set(v___f_2136_, 3, v___x_2133_);
lean_closure_set(v___f_2136_, 4, v_value_1991_);
lean_closure_set(v___f_2136_, 5, v_code_1995_);
lean_closure_set(v___f_2136_, 6, v___x_2134_);
lean_closure_set(v___f_2136_, 7, v___x_2135_);
lean_closure_set(v___f_2136_, 8, v_inlineAttr_x3f_1994_);
v___x_2137_ = 0;
v___x_2138_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_2139_ = lean_nat_dec_lt(v___x_2002_, v___x_2001_);
if (v___x_2139_ == 0)
{
v___y_2089_ = v___x_2132_;
v___y_2090_ = v___x_2130_;
v___y_2091_ = v___f_2136_;
v___y_2092_ = v___y_2126_;
v___y_2093_ = v___y_2127_;
v___y_2094_ = v_sz_2128_;
v___y_2095_ = v___y_2125_;
v___y_2096_ = v___x_2137_;
v___y_2097_ = v___y_2124_;
v___y_2098_ = v___x_2129_;
v___y_2099_ = v___x_2138_;
goto v___jp_2088_;
}
else
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_nat_dec_le(v___x_2001_, v___x_2001_);
if (v___x_2140_ == 0)
{
if (v___x_2139_ == 0)
{
v___y_2089_ = v___x_2132_;
v___y_2090_ = v___x_2130_;
v___y_2091_ = v___f_2136_;
v___y_2092_ = v___y_2126_;
v___y_2093_ = v___y_2127_;
v___y_2094_ = v_sz_2128_;
v___y_2095_ = v___y_2125_;
v___y_2096_ = v___x_2137_;
v___y_2097_ = v___y_2124_;
v___y_2098_ = v___x_2129_;
v___y_2099_ = v___x_2138_;
goto v___jp_2088_;
}
else
{
size_t v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_usize_of_nat(v___x_2001_);
v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_2005_, v_params_1999_, v___x_2129_, v___x_2141_, v___x_2138_);
v___y_2089_ = v___x_2132_;
v___y_2090_ = v___x_2130_;
v___y_2091_ = v___f_2136_;
v___y_2092_ = v___y_2126_;
v___y_2093_ = v___y_2127_;
v___y_2094_ = v_sz_2128_;
v___y_2095_ = v___y_2125_;
v___y_2096_ = v___x_2137_;
v___y_2097_ = v___y_2124_;
v___y_2098_ = v___x_2129_;
v___y_2099_ = v___x_2142_;
goto v___jp_2088_;
}
}
else
{
size_t v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = lean_usize_of_nat(v___x_2001_);
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_2005_, v_params_1999_, v___x_2129_, v___x_2143_, v___x_2138_);
v___y_2089_ = v___x_2132_;
v___y_2090_ = v___x_2130_;
v___y_2091_ = v___f_2136_;
v___y_2092_ = v___y_2126_;
v___y_2093_ = v___y_2127_;
v___y_2094_ = v_sz_2128_;
v___y_2095_ = v___y_2125_;
v___y_2096_ = v___x_2137_;
v___y_2097_ = v___y_2124_;
v___y_2098_ = v___x_2129_;
v___y_2099_ = v___x_2144_;
goto v___jp_2088_;
}
}
}
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
lean_dec(v_a_2005_);
lean_dec_ref(v_code_1995_);
lean_dec_ref_known(v_value_1991_, 1);
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = lean_mk_empty_array_with_capacity(v___x_2173_);
v___x_2175_ = lean_array_push(v___x_2174_, v_decl_1947_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2175_);
v___x_2177_ = v___x_2007_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_code_1995_);
lean_dec_ref_known(v_value_1991_, 1);
lean_dec_ref(v_decl_1947_);
v_a_2180_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2004_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2004_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2197_; 
v_isSharedCheck_2197_ = !lean_is_exclusive(v_value_1991_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_value_1991_, 0);
lean_dec(v_unused_2198_);
v___x_2189_ = v_value_1991_;
v_isShared_2190_ = v_isSharedCheck_2197_;
goto v_resetjp_2188_;
}
else
{
lean_dec(v_value_1991_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2197_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2191_ = lean_unsigned_to_nat(1u);
v___x_2192_ = lean_mk_empty_array_with_capacity(v___x_2191_);
v___x_2193_ = lean_array_push(v___x_2192_, v_decl_1947_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2193_);
v___x_2195_ = v___x_2189_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2208_; 
v_isSharedCheck_2208_ = !lean_is_exclusive(v_value_1991_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; 
v_unused_2209_ = lean_ctor_get(v_value_1991_, 0);
lean_dec(v_unused_2209_);
v___x_2200_ = v_value_1991_;
v_isShared_2201_ = v_isSharedCheck_2208_;
goto v_resetjp_2199_;
}
else
{
lean_dec(v_value_1991_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2208_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2202_ = lean_unsigned_to_nat(1u);
v___x_2203_ = lean_mk_empty_array_with_capacity(v___x_2202_);
v___x_2204_ = lean_array_push(v___x_2203_, v_decl_1947_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set_tag(v___x_2200_, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2204_);
v___x_2206_ = v___x_2200_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
v___jp_1953_:
{
if (lean_obj_tag(v___y_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v_a_1960_ = lean_ctor_get(v___y_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___y_1959_, 1);
v___x_1961_ = lean_st_ref_get(v___y_1957_);
lean_dec(v___y_1957_);
lean_dec(v___x_1961_);
v___x_1962_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___y_1956_, v___y_1958_, v___y_1955_);
lean_dec_ref(v___y_1958_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1973_; 
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v___x_1962_, 0);
lean_dec(v_unused_1974_);
v___x_1964_ = v___x_1962_;
v_isShared_1965_ = v_isSharedCheck_1973_;
goto v_resetjp_1963_;
}
else
{
lean_dec(v___x_1962_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1973_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1966_ = lean_unsigned_to_nat(2u);
v___x_1967_ = lean_mk_empty_array_with_capacity(v___x_1966_);
v___x_1968_ = lean_array_push(v___x_1967_, v___y_1954_);
v___x_1969_ = lean_array_push(v___x_1968_, v_a_1960_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1969_);
v___x_1971_ = v___x_1964_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec(v_a_1960_);
lean_dec_ref(v___y_1954_);
v_a_1975_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1962_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1962_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1954_);
v_a_1983_ = lean_ctor_get(v___y_1959_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___y_1959_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___y_1959_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___y_1959_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object* v_decl_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v_decl_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
return v_res_2216_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* v_00_u03b2_2217_, lean_object* v_m_2218_, lean_object* v_a_2219_){
_start:
{
uint8_t v___x_2220_; 
v___x_2220_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_2218_, v_a_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* v_00_u03b2_2221_, lean_object* v_m_2222_, lean_object* v_a_2223_){
_start:
{
uint8_t v_res_2224_; lean_object* v_r_2225_; 
v_res_2224_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(v_00_u03b2_2221_, v_m_2222_, v_a_2223_);
lean_dec(v_a_2223_);
lean_dec_ref(v_m_2222_);
v_r_2225_ = lean_box(v_res_2224_);
return v_r_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* v_as_2226_, size_t v_sz_2227_, size_t v_i_2228_, lean_object* v_b_2229_, uint8_t v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
v___x_2237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_2226_, v_sz_2227_, v_i_2228_, v_b_2229_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* v_as_2238_, lean_object* v_sz_2239_, lean_object* v_i_2240_, lean_object* v_b_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
size_t v_sz_boxed_2249_; size_t v_i_boxed_2250_; uint8_t v___y_13056__boxed_2251_; lean_object* v_res_2252_; 
v_sz_boxed_2249_ = lean_unbox_usize(v_sz_2239_);
lean_dec(v_sz_2239_);
v_i_boxed_2250_ = lean_unbox_usize(v_i_2240_);
lean_dec(v_i_2240_);
v___y_13056__boxed_2251_ = lean_unbox(v___y_2242_);
v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_2238_, v_sz_boxed_2249_, v_i_boxed_2250_, v_b_2241_, v___y_13056__boxed_2251_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v_as_2238_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* v_as_2253_, size_t v_i_2254_, size_t v_stop_2255_, lean_object* v_b_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_a_2263_; uint8_t v___x_2267_; 
v___x_2267_ = lean_usize_dec_eq(v_i_2254_, v_stop_2255_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = lean_array_uget_borrowed(v_as_2253_, v_i_2254_);
lean_inc(v___x_2268_);
v___x_2269_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v___x_2268_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = l_Array_append___redArg(v_b_2256_, v_a_2270_);
lean_dec(v_a_2270_);
v_a_2263_ = v___x_2271_;
goto v___jp_2262_;
}
else
{
lean_dec_ref(v_b_2256_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2272_; 
v_a_2272_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2269_, 1);
v_a_2263_ = v_a_2272_;
goto v___jp_2262_;
}
else
{
return v___x_2269_;
}
}
}
else
{
lean_object* v___x_2273_; 
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v_b_2256_);
return v___x_2273_;
}
v___jp_2262_:
{
size_t v___x_2264_; size_t v___x_2265_; 
v___x_2264_ = ((size_t)1ULL);
v___x_2265_ = lean_usize_add(v_i_2254_, v___x_2264_);
v_i_2254_ = v___x_2265_;
v_b_2256_ = v_a_2263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* v_as_2274_, lean_object* v_i_2275_, lean_object* v_stop_2276_, lean_object* v_b_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
size_t v_i_boxed_2283_; size_t v_stop_boxed_2284_; lean_object* v_res_2285_; 
v_i_boxed_2283_ = lean_unbox_usize(v_i_2275_);
lean_dec(v_i_2275_);
v_stop_boxed_2284_ = lean_unbox_usize(v_stop_2276_);
lean_dec(v_stop_2276_);
v_res_2285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_2274_, v_i_boxed_2283_, v_stop_boxed_2284_, v_b_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_as_2274_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* v___x_2286_, lean_object* v_decls_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2293_ = lean_mk_empty_array_with_capacity(v___x_2286_);
v___x_2294_ = lean_array_get_size(v_decls_2287_);
v___x_2295_ = lean_nat_dec_lt(v___x_2286_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2293_);
return v___x_2296_;
}
else
{
uint8_t v___x_2297_; 
v___x_2297_ = lean_nat_dec_le(v___x_2294_, v___x_2294_);
if (v___x_2297_ == 0)
{
if (v___x_2295_ == 0)
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2293_);
return v___x_2298_;
}
else
{
size_t v___x_2299_; size_t v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = ((size_t)0ULL);
v___x_2300_ = lean_usize_of_nat(v___x_2294_);
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2287_, v___x_2299_, v___x_2300_, v___x_2293_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2301_;
}
}
else
{
size_t v___x_2302_; size_t v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = lean_usize_of_nat(v___x_2294_);
v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2287_, v___x_2302_, v___x_2303_, v___x_2293_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* v___x_2305_, lean_object* v_decls_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(v___x_2305_, v_decls_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec_ref(v_decls_2306_);
lean_dec(v___x_2305_);
return v_res_2312_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = lean_unsigned_to_nat(2803462840u);
v___x_2376_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2377_ = l_Lean_Name_num___override(v___x_2376_, v___x_2375_);
return v___x_2377_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2379_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2380_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2381_ = l_Lean_Name_str___override(v___x_2380_, v___x_2379_);
return v___x_2381_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2384_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2385_ = l_Lean_Name_str___override(v___x_2384_, v___x_2383_);
return v___x_2385_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = lean_unsigned_to_nat(2u);
v___x_2387_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2388_ = l_Lean_Name_num___override(v___x_2387_, v___x_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2390_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_2391_ = 1;
v___x_2392_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2393_ = l_Lean_registerTraceClass(v___x_2390_, v___x_2391_, v___x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
return v_res_2395_;
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
