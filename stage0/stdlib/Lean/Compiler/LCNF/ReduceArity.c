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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_8_;
v_res_8_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_1_, v_x_2_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg___boxed(lean_object* v_a_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_9_, v_x_10_);
lean_dec(v_x_10_);
lean_dec(v_a_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
return v_x_13_;
}
else
{
lean_object* v_key_15_; lean_object* v_value_16_; lean_object* v_tail_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_40_; 
v_key_15_ = lean_ctor_get(v_x_14_, 0);
v_value_16_ = lean_ctor_get(v_x_14_, 1);
v_tail_17_ = lean_ctor_get(v_x_14_, 2);
v_isSharedCheck_40_ = !lean_is_exclusive(v_x_14_);
if (v_isSharedCheck_40_ == 0)
{
v___x_19_ = v_x_14_;
v_isShared_20_ = v_isSharedCheck_40_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_tail_17_);
lean_inc(v_value_16_);
lean_inc(v_key_15_);
lean_dec(v_x_14_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_40_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; uint64_t v___x_24_; uint64_t v_fold_25_; uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v___x_28_; size_t v___x_29_; size_t v___x_30_; size_t v___x_31_; size_t v___x_32_; size_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_21_ = lean_array_get_size(v_x_13_);
v___x_22_ = l_Lean_instHashableFVarId_hash(v_key_15_);
v___x_23_ = 32ULL;
v___x_24_ = lean_uint64_shift_right(v___x_22_, v___x_23_);
v_fold_25_ = lean_uint64_xor(v___x_22_, v___x_24_);
v___x_26_ = 16ULL;
v___x_27_ = lean_uint64_shift_right(v_fold_25_, v___x_26_);
v___x_28_ = lean_uint64_xor(v_fold_25_, v___x_27_);
v___x_29_ = lean_uint64_to_usize(v___x_28_);
v___x_30_ = lean_usize_of_nat(v___x_21_);
v___x_31_ = ((size_t)1ULL);
v___x_32_ = lean_usize_sub(v___x_30_, v___x_31_);
v___x_33_ = lean_usize_land(v___x_29_, v___x_32_);
v___x_34_ = lean_array_uget_borrowed(v_x_13_, v___x_33_);
lean_inc(v___x_34_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 2, v___x_34_);
v___x_36_ = v___x_19_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_key_15_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_value_16_);
lean_ctor_set(v_reuseFailAlloc_39_, 2, v___x_34_);
v___x_36_ = v_reuseFailAlloc_39_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_37_; 
v___x_37_ = lean_array_uset(v_x_13_, v___x_33_, v___x_36_);
v_x_13_ = v___x_37_;
v_x_14_ = v_tail_17_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(lean_object* v_i_41_, lean_object* v_source_42_, lean_object* v_target_43_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_array_get_size(v_source_42_);
v___x_45_ = lean_nat_dec_lt(v_i_41_, v___x_44_);
if (v___x_45_ == 0)
{
lean_dec_ref(v_source_42_);
lean_dec(v_i_41_);
return v_target_43_;
}
else
{
lean_object* v_es_46_; lean_object* v___x_47_; lean_object* v_source_48_; lean_object* v_target_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_es_46_ = lean_array_fget(v_source_42_, v_i_41_);
v___x_47_ = lean_box(0);
v_source_48_ = lean_array_fset(v_source_42_, v_i_41_, v___x_47_);
v_target_49_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(v_target_43_, v_es_46_);
v___x_50_ = lean_unsigned_to_nat(1u);
v___x_51_ = lean_nat_add(v_i_41_, v___x_50_);
lean_dec(v_i_41_);
v_i_41_ = v___x_51_;
v_source_42_ = v_source_48_;
v_target_43_ = v_target_49_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(lean_object* v_data_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v_nbuckets_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_54_ = lean_array_get_size(v_data_53_);
v___x_55_ = lean_unsigned_to_nat(2u);
v_nbuckets_56_ = lean_nat_mul(v___x_54_, v___x_55_);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_box(0);
v___x_59_ = lean_mk_array(v_nbuckets_56_, v___x_58_);
v___x_60_ = lean_array_propagate_mark(v_data_53_, v___x_59_);
v___x_61_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(v___x_57_, v_data_53_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(lean_object* v_m_62_, lean_object* v_a_63_, lean_object* v_b_64_){
_start:
{
lean_object* v_size_65_; lean_object* v_buckets_66_; lean_object* v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; uint64_t v_fold_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; lean_object* v_bkt_80_; uint8_t v___x_81_; 
v_size_65_ = lean_ctor_get(v_m_62_, 0);
v_buckets_66_ = lean_ctor_get(v_m_62_, 1);
v___x_67_ = lean_array_get_size(v_buckets_66_);
v___x_68_ = l_Lean_instHashableFVarId_hash(v_a_63_);
v___x_69_ = 32ULL;
v___x_70_ = lean_uint64_shift_right(v___x_68_, v___x_69_);
v_fold_71_ = lean_uint64_xor(v___x_68_, v___x_70_);
v___x_72_ = 16ULL;
v___x_73_ = lean_uint64_shift_right(v_fold_71_, v___x_72_);
v___x_74_ = lean_uint64_xor(v_fold_71_, v___x_73_);
v___x_75_ = lean_uint64_to_usize(v___x_74_);
v___x_76_ = lean_usize_of_nat(v___x_67_);
v___x_77_ = ((size_t)1ULL);
v___x_78_ = lean_usize_sub(v___x_76_, v___x_77_);
v___x_79_ = lean_usize_land(v___x_75_, v___x_78_);
v_bkt_80_ = lean_array_uget_borrowed(v_buckets_66_, v___x_79_);
v___x_81_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_63_, v_bkt_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_102_; 
lean_inc_ref(v_buckets_66_);
lean_inc(v_size_65_);
v_isSharedCheck_102_ = !lean_is_exclusive(v_m_62_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; lean_object* v_unused_104_; 
v_unused_103_ = lean_ctor_get(v_m_62_, 1);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_m_62_, 0);
lean_dec(v_unused_104_);
v___x_83_ = v_m_62_;
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_m_62_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v_size_x27_86_; lean_object* v___x_87_; lean_object* v_buckets_x27_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v_size_x27_86_ = lean_nat_add(v_size_65_, v___x_85_);
lean_dec(v_size_65_);
lean_inc(v_bkt_80_);
v___x_87_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_87_, 0, v_a_63_);
lean_ctor_set(v___x_87_, 1, v_b_64_);
lean_ctor_set(v___x_87_, 2, v_bkt_80_);
v_buckets_x27_88_ = lean_array_uset(v_buckets_66_, v___x_79_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(4u);
v___x_90_ = lean_nat_mul(v_size_x27_86_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(3u);
v___x_92_ = lean_nat_div(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_array_get_size(v_buckets_x27_88_);
v___x_94_ = lean_nat_dec_le(v___x_92_, v___x_93_);
lean_dec(v___x_92_);
if (v___x_94_ == 0)
{
lean_object* v_val_95_; lean_object* v___x_97_; 
v_val_95_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(v_buckets_x27_88_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_val_95_);
lean_ctor_set(v___x_83_, 0, v_size_x27_86_);
v___x_97_ = v___x_83_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_size_x27_86_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_val_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
else
{
lean_object* v___x_100_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_buckets_x27_88_);
lean_ctor_set(v___x_83_, 0, v_size_x27_86_);
v___x_100_ = v___x_83_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_size_x27_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_buckets_x27_88_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
else
{
lean_dec(v_b_64_);
lean_dec(v_a_63_);
return v_m_62_;
}
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(lean_object* v_k_105_, lean_object* v_t_106_){
_start:
{
if (lean_obj_tag(v_t_106_) == 0)
{
lean_object* v_k_107_; lean_object* v_l_108_; lean_object* v_r_109_; uint8_t v___x_110_; 
v_k_107_ = lean_ctor_get(v_t_106_, 1);
v_l_108_ = lean_ctor_get(v_t_106_, 3);
v_r_109_ = lean_ctor_get(v_t_106_, 4);
v___x_110_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_105_, v_k_107_);
switch(v___x_110_)
{
case 0:
{
v_t_106_ = v_l_108_;
goto _start;
}
case 1:
{
uint8_t v___x_112_; 
v___x_112_ = 1;
return v___x_112_;
}
default: 
{
v_t_106_ = v_r_109_;
goto _start;
}
}
}
else
{
uint8_t v___x_114_; 
v___x_114_ = 0;
return v___x_114_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_105_ = stack[0].m_obj;
lean_object* v_t_106_ = stack[1].m_obj;
uint8_t v_res_115_;
v_res_115_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_105_, v_t_106_);
stack->m_num = v_res_115_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg___boxed(lean_object* v_k_116_, lean_object* v_t_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_116_, v_t_117_);
lean_dec(v_t_117_);
lean_dec(v_k_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object* v_fvarId_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_params_124_; uint8_t v___x_125_; 
v_params_124_ = lean_ctor_get(v_a_121_, 1);
v___x_125_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_fvarId_120_, v_params_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec(v_fvarId_120_);
v___x_126_ = lean_box(0);
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_128_ = lean_st_ref_take(v_a_122_);
v___x_129_ = lean_box(0);
v___x_130_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v___x_128_, v_fvarId_120_, v___x_129_);
v___x_131_ = lean_st_ref_put(v_a_122_, v___x_130_);
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_129_);
return v___x_132_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_120_ = stack[0].m_obj;
lean_object* v_a_121_ = stack[1].m_obj;
lean_object* v_a_122_ = stack[2].m_obj;
lean_object* v_res_133_;
v_res_133_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_120_, v_a_121_, v_a_122_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object* v_fvarId_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
return v_res_138_;
}
}
lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object* v_fvarId_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_139_, v_a_140_, v_a_141_);
return v___x_147_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FindUsed_visitFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_139_ = stack[0].m_obj;
lean_object* v_a_140_ = stack[1].m_obj;
lean_object* v_a_141_ = stack[2].m_obj;
lean_object* v_a_142_ = stack[3].m_obj;
lean_object* v_a_143_ = stack[4].m_obj;
lean_object* v_a_144_ = stack[5].m_obj;
lean_object* v_a_145_ = stack[6].m_obj;
lean_object* v_res_148_;
v_res_148_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar(v_fvarId_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object* v_fvarId_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar(v_fvarId_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_157_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(lean_object* v_00_u03b2_158_, lean_object* v_k_159_, lean_object* v_t_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_159_, v_t_160_);
return v___x_161_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_159_ = stack[1].m_obj;
lean_object* v_t_160_ = stack[2].m_obj;
uint8_t v_res_162_;
v_res_162_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(lean_box(0), v_k_159_, v_t_160_);
stack->m_num = v_res_162_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___boxed(lean_object* v_00_u03b2_163_, lean_object* v_k_164_, lean_object* v_t_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(v_00_u03b2_163_, v_k_164_, v_t_165_);
lean_dec(v_t_165_);
lean_dec(v_k_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1(lean_object* v_00_u03b2_168_, lean_object* v_m_169_, lean_object* v_a_170_, lean_object* v_b_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v_m_169_, v_a_170_, v_b_171_);
return v___x_172_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(lean_object* v_00_u03b2_173_, lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_174_, v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_174_ = stack[1].m_obj;
lean_object* v_x_175_ = stack[2].m_obj;
uint8_t v_res_177_;
v_res_177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(lean_box(0), v_a_174_, v_x_175_);
stack->m_num = v_res_177_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___boxed(lean_object* v_00_u03b2_178_, lean_object* v_a_179_, lean_object* v_x_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(v_00_u03b2_178_, v_a_179_, v_x_180_);
lean_dec(v_x_180_);
lean_dec(v_a_179_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2(lean_object* v_00_u03b2_183_, lean_object* v_data_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(v_data_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_186_, lean_object* v_i_187_, lean_object* v_source_188_, lean_object* v_target_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(v_i_187_, v_source_188_, v_target_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(v_x_192_, v_x_193_);
return v___x_194_;
}
}
lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object* v_arg_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
if (lean_obj_tag(v_arg_195_) == 1)
{
lean_object* v_fvarId_199_; lean_object* v___x_200_; 
v_fvarId_199_ = lean_ctor_get(v_arg_195_, 0);
lean_inc(v_fvarId_199_);
lean_dec_ref_known(v_arg_195_, 1);
v___x_200_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_199_, v_a_196_, v_a_197_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_arg_195_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_195_ = stack[0].m_obj;
lean_object* v_a_196_ = stack[1].m_obj;
lean_object* v_a_197_ = stack[2].m_obj;
lean_object* v_res_203_;
v_res_203_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_195_, v_a_196_, v_a_197_);
stack->m_obj
 = v_res_203_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object* v_arg_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_204_, v_a_205_, v_a_206_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
return v_res_208_;
}
}
lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object* v_arg_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_209_, v_a_210_, v_a_211_);
return v___x_217_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FindUsed_visitArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_209_ = stack[0].m_obj;
lean_object* v_a_210_ = stack[1].m_obj;
lean_object* v_a_211_ = stack[2].m_obj;
lean_object* v_a_212_ = stack[3].m_obj;
lean_object* v_a_213_ = stack[4].m_obj;
lean_object* v_a_214_ = stack[5].m_obj;
lean_object* v_a_215_ = stack[6].m_obj;
lean_object* v_res_218_;
v_res_218_ = l_Lean_Compiler_LCNF_FindUsed_visitArg(v_arg_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object* v_arg_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Compiler_LCNF_FindUsed_visitArg(v_arg_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_227_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object* v_as_228_, size_t v_sz_229_, size_t v_i_230_, lean_object* v_b_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_a_236_; uint8_t v___x_240_; 
v___x_240_ = lean_usize_dec_lt(v_i_230_, v_sz_229_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v_b_231_);
return v___x_241_;
}
else
{
lean_object* v_array_242_; lean_object* v_start_243_; lean_object* v_stop_244_; uint8_t v___x_245_; 
v_array_242_ = lean_ctor_get(v_b_231_, 0);
v_start_243_ = lean_ctor_get(v_b_231_, 1);
v_stop_244_ = lean_ctor_get(v_b_231_, 2);
v___x_245_ = lean_nat_dec_lt(v_start_243_, v_stop_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v_b_231_);
return v___x_246_;
}
else
{
lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_269_; 
lean_inc(v_stop_244_);
lean_inc(v_start_243_);
lean_inc_ref(v_array_242_);
v_isSharedCheck_269_ = !lean_is_exclusive(v_b_231_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; 
v_unused_270_ = lean_ctor_get(v_b_231_, 2);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_b_231_, 1);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_b_231_, 0);
lean_dec(v_unused_272_);
v___x_248_ = v_b_231_;
v_isShared_249_ = v_isSharedCheck_269_;
goto v_resetjp_247_;
}
else
{
lean_dec(v_b_231_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_269_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_250_ = lean_array_fget(v_array_242_, v_start_243_);
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = lean_nat_add(v_start_243_, v___x_251_);
lean_dec(v_start_243_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v___x_252_);
v___x_254_ = v___x_248_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_array_242_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_stop_244_);
v___x_254_ = v_reuseFailAlloc_268_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
if (lean_obj_tag(v___x_250_) == 1)
{
lean_object* v_fvarId_255_; lean_object* v_a_256_; lean_object* v_fvarId_257_; uint8_t v___x_258_; 
v_fvarId_255_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_fvarId_255_);
lean_dec_ref_known(v___x_250_, 1);
v_a_256_ = lean_array_uget_borrowed(v_as_228_, v_i_230_);
v_fvarId_257_ = lean_ctor_get(v_a_256_, 0);
v___x_258_ = l_Lean_instBEqFVarId_beq(v_fvarId_255_, v_fvarId_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_255_, v___y_232_, v___y_233_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_dec_ref_known(v___x_259_, 1);
v_a_236_ = v___x_254_;
goto v___jp_235_;
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v___x_254_);
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
else
{
lean_dec(v_fvarId_255_);
v_a_236_ = v___x_254_;
goto v___jp_235_;
}
}
else
{
lean_dec(v___x_250_);
v_a_236_ = v___x_254_;
goto v___jp_235_;
}
}
}
}
}
v___jp_235_:
{
size_t v___x_237_; size_t v___x_238_; 
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_add(v_i_230_, v___x_237_);
v_i_230_ = v___x_238_;
v_b_231_ = v_a_236_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_228_ = stack[0].m_obj;
size_t v_sz_229_ = stack[1].m_num;
size_t v_i_230_ = stack[2].m_num;
lean_object* v_b_231_ = stack[3].m_obj;
lean_object* v___y_232_ = stack[4].m_obj;
lean_object* v___y_233_ = stack[5].m_obj;
lean_object* v_res_273_;
v_res_273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_228_, v_sz_229_, v_i_230_, v_b_231_, v___y_232_, v___y_233_);
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object* v_as_274_, lean_object* v_sz_275_, lean_object* v_i_276_, lean_object* v_b_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
size_t v_sz_boxed_281_; size_t v_i_boxed_282_; lean_object* v_res_283_; 
v_sz_boxed_281_ = lean_unbox_usize(v_sz_275_);
lean_dec(v_sz_275_);
v_i_boxed_282_ = lean_unbox_usize(v_i_276_);
lean_dec(v_i_276_);
v_res_283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_274_, v_sz_boxed_281_, v_i_boxed_282_, v_b_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec_ref(v_as_274_);
return v_res_283_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object* v_a_284_, lean_object* v_b_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_array_289_; lean_object* v_start_290_; lean_object* v_stop_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_307_; 
v_array_289_ = lean_ctor_get(v_a_284_, 0);
v_start_290_ = lean_ctor_get(v_a_284_, 1);
v_stop_291_ = lean_ctor_get(v_a_284_, 2);
v_isSharedCheck_307_ = !lean_is_exclusive(v_a_284_);
if (v_isSharedCheck_307_ == 0)
{
v___x_293_ = v_a_284_;
v_isShared_294_ = v_isSharedCheck_307_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_stop_291_);
lean_inc(v_start_290_);
lean_inc(v_array_289_);
lean_dec(v_a_284_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_307_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; 
v___x_295_ = lean_nat_dec_lt(v_start_290_, v_stop_291_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
lean_del_object(v___x_293_);
lean_dec(v_stop_291_);
lean_dec(v_start_290_);
lean_dec_ref(v_array_289_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v_b_285_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; lean_object* v_fvarId_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_297_ = lean_array_fget_borrowed(v_array_289_, v_start_290_);
v_fvarId_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_fvarId_298_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_start_290_, v___x_300_);
lean_dec(v_start_290_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_301_);
v___x_303_ = v___x_293_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_array_289_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_stop_291_);
v___x_303_ = v_reuseFailAlloc_306_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_298_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_dec_ref_known(v___x_304_, 1);
v_a_284_ = v___x_303_;
v_b_285_ = v___x_299_;
goto _start;
}
else
{
lean_dec_ref(v___x_303_);
return v___x_304_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_284_ = stack[0].m_obj;
lean_object* v_b_285_ = stack[1].m_obj;
lean_object* v___y_286_ = stack[2].m_obj;
lean_object* v___y_287_ = stack[3].m_obj;
lean_object* v_res_308_;
v_res_308_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_284_, v_b_285_, v___y_286_, v___y_287_);
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object* v_a_309_, lean_object* v_b_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_309_, v_b_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_314_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object* v_as_315_, size_t v_i_316_, size_t v_stop_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
uint8_t v___x_322_; 
v___x_322_ = lean_usize_dec_eq(v_i_316_, v_stop_317_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_array_uget_borrowed(v_as_315_, v_i_316_);
lean_inc(v___x_323_);
v___x_324_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v___x_323_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; size_t v___x_326_; size_t v___x_327_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_316_, v___x_326_);
v_i_316_ = v___x_327_;
v_b_318_ = v_a_325_;
goto _start;
}
else
{
return v___x_324_;
}
}
else
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v_b_318_);
return v___x_329_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_315_ = stack[0].m_obj;
size_t v_i_316_ = stack[1].m_num;
size_t v_stop_317_ = stack[2].m_num;
lean_object* v_b_318_ = stack[3].m_obj;
lean_object* v___y_319_ = stack[4].m_obj;
lean_object* v___y_320_ = stack[5].m_obj;
lean_object* v_res_330_;
v_res_330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_315_, v_i_316_, v_stop_317_, v_b_318_, v___y_319_, v___y_320_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object* v_as_331_, lean_object* v_i_332_, lean_object* v_stop_333_, lean_object* v_b_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
size_t v_i_boxed_338_; size_t v_stop_boxed_339_; lean_object* v_res_340_; 
v_i_boxed_338_ = lean_unbox_usize(v_i_332_);
lean_dec(v_i_332_);
v_stop_boxed_339_ = lean_unbox_usize(v_stop_333_);
lean_dec(v_stop_333_);
v_res_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_331_, v_i_boxed_338_, v_stop_boxed_339_, v_b_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec_ref(v_as_331_);
return v_res_340_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object* v_a_341_, lean_object* v_b_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_array_346_; lean_object* v_start_347_; lean_object* v_stop_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_363_; 
v_array_346_ = lean_ctor_get(v_a_341_, 0);
v_start_347_ = lean_ctor_get(v_a_341_, 1);
v_stop_348_ = lean_ctor_get(v_a_341_, 2);
v_isSharedCheck_363_ = !lean_is_exclusive(v_a_341_);
if (v_isSharedCheck_363_ == 0)
{
v___x_350_ = v_a_341_;
v_isShared_351_ = v_isSharedCheck_363_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_stop_348_);
lean_inc(v_start_347_);
lean_inc(v_array_346_);
lean_dec(v_a_341_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_363_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
uint8_t v___x_352_; 
v___x_352_ = lean_nat_dec_lt(v_start_347_, v_stop_348_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
lean_del_object(v___x_350_);
lean_dec(v_stop_348_);
lean_dec(v_start_347_);
lean_dec_ref(v_array_346_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v_b_342_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_354_ = lean_box(0);
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_start_347_, v___x_355_);
lean_inc_ref(v_array_346_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___x_356_);
v___x_358_ = v___x_350_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_array_346_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_stop_348_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_array_fget(v_array_346_, v_start_347_);
lean_dec(v_start_347_);
lean_dec_ref(v_array_346_);
v___x_360_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v___x_359_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_dec_ref_known(v___x_360_, 1);
v_a_341_ = v___x_358_;
v_b_342_ = v___x_354_;
goto _start;
}
else
{
lean_dec_ref(v___x_358_);
return v___x_360_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_341_ = stack[0].m_obj;
lean_object* v_b_342_ = stack[1].m_obj;
lean_object* v___y_343_ = stack[2].m_obj;
lean_object* v___y_344_ = stack[3].m_obj;
lean_object* v_res_364_;
v_res_364_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_341_, v_b_342_, v___y_343_, v___y_344_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object* v_a_365_, lean_object* v_b_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_365_, v_b_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_370_;
}
}
lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object* v_e_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
switch(lean_obj_tag(v_e_371_))
{
case 2:
{
lean_object* v_struct_379_; lean_object* v___x_380_; 
v_struct_379_ = lean_ctor_get(v_e_371_, 2);
lean_inc(v_struct_379_);
lean_dec_ref_known(v_e_371_, 3);
v___x_380_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_struct_379_, v_a_372_, v_a_373_);
return v___x_380_;
}
case 3:
{
lean_object* v_decl_381_; lean_object* v_toSignature_382_; lean_object* v_declName_383_; lean_object* v_args_384_; lean_object* v_name_385_; lean_object* v_params_386_; lean_object* v___y_388_; lean_object* v_lower_389_; lean_object* v_upper_390_; uint8_t v___x_401_; 
v_decl_381_ = lean_ctor_get(v_a_372_, 0);
v_toSignature_382_ = lean_ctor_get(v_decl_381_, 0);
v_declName_383_ = lean_ctor_get(v_e_371_, 0);
lean_inc(v_declName_383_);
v_args_384_ = lean_ctor_get(v_e_371_, 2);
lean_inc_ref(v_args_384_);
lean_dec_ref_known(v_e_371_, 3);
v_name_385_ = lean_ctor_get(v_toSignature_382_, 0);
v_params_386_ = lean_ctor_get(v_toSignature_382_, 3);
v___x_401_ = lean_name_eq(v_declName_383_, v_name_385_);
lean_dec(v_declName_383_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_array_get_size(v_args_384_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_nat_dec_lt(v___x_402_, v___x_403_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec_ref(v_args_384_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_404_);
return v___x_406_;
}
else
{
uint8_t v___x_407_; 
v___x_407_ = lean_nat_dec_le(v___x_403_, v___x_403_);
if (v___x_407_ == 0)
{
if (v___x_405_ == 0)
{
lean_object* v___x_408_; 
lean_dec_ref(v_args_384_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_404_);
return v___x_408_;
}
else
{
size_t v___x_409_; size_t v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((size_t)0ULL);
v___x_410_ = lean_usize_of_nat(v___x_403_);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_384_, v___x_409_, v___x_410_, v___x_404_, v_a_372_, v_a_373_);
lean_dec_ref(v_args_384_);
return v___x_411_;
}
}
else
{
size_t v___x_412_; size_t v___x_413_; lean_object* v___x_414_; 
v___x_412_ = ((size_t)0ULL);
v___x_413_ = lean_usize_of_nat(v___x_403_);
v___x_414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_384_, v___x_412_, v___x_413_, v___x_404_, v_a_372_, v_a_373_);
lean_dec_ref(v_args_384_);
return v___x_414_;
}
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; size_t v_sz_418_; size_t v___x_419_; lean_object* v___x_420_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_array_get_size(v_args_384_);
lean_inc_ref(v_args_384_);
v___x_417_ = l_Array_toSubarray___redArg(v_args_384_, v___x_415_, v___x_416_);
v_sz_418_ = lean_array_size(v_params_386_);
v___x_419_ = ((size_t)0ULL);
v___x_420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_params_386_, v_sz_418_, v___x_419_, v___x_417_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_lower_422_; lean_object* v_upper_423_; lean_object* v___x_429_; uint8_t v___x_430_; 
lean_dec_ref_known(v___x_420_, 1);
v___x_429_ = lean_array_get_size(v_params_386_);
v___x_430_ = lean_nat_dec_le(v___x_429_, v___x_415_);
if (v___x_430_ == 0)
{
v_lower_422_ = v___x_429_;
v_upper_423_ = v___x_416_;
goto v___jp_421_;
}
else
{
v_lower_422_ = v___x_415_;
v_upper_423_ = v___x_416_;
goto v___jp_421_;
}
v___jp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = l_Array_toSubarray___redArg(v_args_384_, v_lower_422_, v_upper_423_);
v___x_425_ = lean_box(0);
v___x_426_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v___x_424_, v___x_425_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v___x_427_; uint8_t v___x_428_; 
lean_dec_ref_known(v___x_426_, 1);
v___x_427_ = lean_array_get_size(v_params_386_);
v___x_428_ = lean_nat_dec_le(v___x_416_, v___x_415_);
if (v___x_428_ == 0)
{
v___y_388_ = v___x_425_;
v_lower_389_ = v___x_416_;
v_upper_390_ = v___x_427_;
goto v___jp_387_;
}
else
{
v___y_388_ = v___x_425_;
v_lower_389_ = v___x_415_;
v_upper_390_ = v___x_427_;
goto v___jp_387_;
}
}
else
{
return v___x_426_;
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_dec_ref(v_args_384_);
v_a_431_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_420_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_420_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
v___jp_387_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc_ref(v_params_386_);
v___x_391_ = l_Array_toSubarray___redArg(v_params_386_, v_lower_389_, v_upper_390_);
v___x_392_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v___x_391_, v___y_388_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_392_, 0);
lean_dec(v_unused_400_);
v___x_394_ = v___x_392_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_dec(v___x_392_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___y_388_);
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___y_388_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
else
{
return v___x_392_;
}
}
}
case 4:
{
lean_object* v_fvarId_439_; lean_object* v_args_440_; lean_object* v___x_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_462_; 
v_fvarId_439_ = lean_ctor_get(v_e_371_, 0);
lean_inc(v_fvarId_439_);
v_args_440_ = lean_ctor_get(v_e_371_, 1);
lean_inc_ref(v_args_440_);
lean_dec_ref_known(v_e_371_, 2);
v___x_441_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_439_, v_a_372_, v_a_373_);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v___x_441_, 0);
lean_dec(v_unused_463_);
v___x_443_ = v___x_441_;
v_isShared_444_ = v_isSharedCheck_462_;
goto v_resetjp_442_;
}
else
{
lean_dec(v___x_441_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_462_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_array_get_size(v_args_440_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_nat_dec_lt(v___x_445_, v___x_446_);
if (v___x_448_ == 0)
{
lean_object* v___x_450_; 
lean_dec_ref(v_args_440_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_447_);
v___x_450_ = v___x_443_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_447_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
else
{
uint8_t v___x_452_; 
v___x_452_ = lean_nat_dec_le(v___x_446_, v___x_446_);
if (v___x_452_ == 0)
{
if (v___x_448_ == 0)
{
lean_object* v___x_454_; 
lean_dec_ref(v_args_440_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_447_);
v___x_454_ = v___x_443_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_447_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
else
{
size_t v___x_456_; size_t v___x_457_; lean_object* v___x_458_; 
lean_del_object(v___x_443_);
v___x_456_ = ((size_t)0ULL);
v___x_457_ = lean_usize_of_nat(v___x_446_);
v___x_458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_440_, v___x_456_, v___x_457_, v___x_447_, v_a_372_, v_a_373_);
lean_dec_ref(v_args_440_);
return v___x_458_;
}
}
else
{
size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; 
lean_del_object(v___x_443_);
v___x_459_ = ((size_t)0ULL);
v___x_460_ = lean_usize_of_nat(v___x_446_);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_440_, v___x_459_, v___x_460_, v___x_447_, v_a_372_, v_a_373_);
lean_dec_ref(v_args_440_);
return v___x_461_;
}
}
}
}
default: 
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v_e_371_);
v___x_464_ = lean_box(0);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FindUsed_visitLetValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_371_ = stack[0].m_obj;
lean_object* v_a_372_ = stack[1].m_obj;
lean_object* v_a_373_ = stack[2].m_obj;
lean_object* v_a_374_ = stack[3].m_obj;
lean_object* v_a_375_ = stack[4].m_obj;
lean_object* v_a_376_ = stack[5].m_obj;
lean_object* v_a_377_ = stack[6].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_e_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_e_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec_ref(v_a_468_);
return v_res_475_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object* v_as_476_, size_t v_i_477_, size_t v_stop_478_, lean_object* v_b_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_476_, v_i_477_, v_stop_478_, v_b_479_, v___y_480_, v___y_481_);
return v___x_487_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_476_ = stack[0].m_obj;
size_t v_i_477_ = stack[1].m_num;
size_t v_stop_478_ = stack[2].m_num;
lean_object* v_b_479_ = stack[3].m_obj;
lean_object* v___y_480_ = stack[4].m_obj;
lean_object* v___y_481_ = stack[5].m_obj;
lean_object* v___y_482_ = stack[6].m_obj;
lean_object* v___y_483_ = stack[7].m_obj;
lean_object* v___y_484_ = stack[8].m_obj;
lean_object* v___y_485_ = stack[9].m_obj;
lean_object* v_res_488_;
v_res_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(v_as_476_, v_i_477_, v_stop_478_, v_b_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
stack->m_obj
 = v_res_488_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object* v_as_489_, lean_object* v_i_490_, lean_object* v_stop_491_, lean_object* v_b_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
size_t v_i_boxed_500_; size_t v_stop_boxed_501_; lean_object* v_res_502_; 
v_i_boxed_500_ = lean_unbox_usize(v_i_490_);
lean_dec(v_i_490_);
v_stop_boxed_501_ = lean_unbox_usize(v_stop_491_);
lean_dec(v_stop_491_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(v_as_489_, v_i_boxed_500_, v_stop_boxed_501_, v_b_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec_ref(v_as_489_);
return v_res_502_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object* v_as_503_, size_t v_sz_504_, size_t v_i_505_, lean_object* v_b_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_503_, v_sz_504_, v_i_505_, v_b_506_, v___y_507_, v___y_508_);
return v___x_514_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_503_ = stack[0].m_obj;
size_t v_sz_504_ = stack[1].m_num;
size_t v_i_505_ = stack[2].m_num;
lean_object* v_b_506_ = stack[3].m_obj;
lean_object* v___y_507_ = stack[4].m_obj;
lean_object* v___y_508_ = stack[5].m_obj;
lean_object* v___y_509_ = stack[6].m_obj;
lean_object* v___y_510_ = stack[7].m_obj;
lean_object* v___y_511_ = stack[8].m_obj;
lean_object* v___y_512_ = stack[9].m_obj;
lean_object* v_res_515_;
v_res_515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(v_as_503_, v_sz_504_, v_i_505_, v_b_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object* v_as_516_, lean_object* v_sz_517_, lean_object* v_i_518_, lean_object* v_b_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
size_t v_sz_boxed_527_; size_t v_i_boxed_528_; lean_object* v_res_529_; 
v_sz_boxed_527_ = lean_unbox_usize(v_sz_517_);
lean_dec(v_sz_517_);
v_i_boxed_528_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(v_as_516_, v_sz_boxed_527_, v_i_boxed_528_, v_b_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec_ref(v_as_516_);
return v_res_529_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object* v_inst_530_, lean_object* v_R_531_, lean_object* v_a_532_, lean_object* v_b_533_, lean_object* v_c_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_532_, v_b_533_, v___y_535_, v___y_536_);
return v___x_542_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_532_ = stack[2].m_obj;
lean_object* v_b_533_ = stack[3].m_obj;
lean_object* v___y_535_ = stack[5].m_obj;
lean_object* v___y_536_ = stack[6].m_obj;
lean_object* v___y_537_ = stack[7].m_obj;
lean_object* v___y_538_ = stack[8].m_obj;
lean_object* v___y_539_ = stack[9].m_obj;
lean_object* v___y_540_ = stack[10].m_obj;
lean_object* v_res_543_;
v_res_543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_box(0), lean_box(0), v_a_532_, v_b_533_, lean_box(0), v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object* v_inst_544_, lean_object* v_R_545_, lean_object* v_a_546_, lean_object* v_b_547_, lean_object* v_c_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(v_inst_544_, v_R_545_, v_a_546_, v_b_547_, v_c_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_556_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object* v_inst_557_, lean_object* v_R_558_, lean_object* v_a_559_, lean_object* v_b_560_, lean_object* v_c_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_559_, v_b_560_, v___y_562_, v___y_563_);
return v___x_569_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_559_ = stack[2].m_obj;
lean_object* v_b_560_ = stack[3].m_obj;
lean_object* v___y_562_ = stack[5].m_obj;
lean_object* v___y_563_ = stack[6].m_obj;
lean_object* v___y_564_ = stack[7].m_obj;
lean_object* v___y_565_ = stack[8].m_obj;
lean_object* v___y_566_ = stack[9].m_obj;
lean_object* v___y_567_ = stack[10].m_obj;
lean_object* v_res_570_;
v_res_570_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_box(0), lean_box(0), v_a_559_, v_b_560_, lean_box(0), v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object* v_inst_571_, lean_object* v_R_572_, lean_object* v_a_573_, lean_object* v_b_574_, lean_object* v_c_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(v_inst_571_, v_R_572_, v_a_573_, v_b_574_, v_c_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_583_;
}
}
lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object* v_code_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_decl_593_; lean_object* v_k_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; 
switch(lean_obj_tag(v_code_584_))
{
case 0:
{
lean_object* v_decl_604_; lean_object* v_k_605_; lean_object* v_value_606_; lean_object* v___x_607_; 
v_decl_604_ = lean_ctor_get(v_code_584_, 0);
lean_inc_ref(v_decl_604_);
v_k_605_ = lean_ctor_get(v_code_584_, 1);
lean_inc_ref(v_k_605_);
lean_dec_ref_known(v_code_584_, 2);
v_value_606_ = lean_ctor_get(v_decl_604_, 3);
lean_inc(v_value_606_);
lean_dec_ref(v_decl_604_);
v___x_607_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_value_606_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_dec_ref_known(v___x_607_, 1);
v_code_584_ = v_k_605_;
goto _start;
}
else
{
lean_dec_ref(v_k_605_);
return v___x_607_;
}
}
case 3:
{
lean_object* v_args_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_args_609_ = lean_ctor_get(v_code_584_, 1);
lean_inc_ref(v_args_609_);
lean_dec_ref_known(v_code_584_, 2);
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_array_get_size(v_args_609_);
v___x_612_ = lean_box(0);
v___x_613_ = lean_nat_dec_lt(v___x_610_, v___x_611_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
lean_dec_ref(v_args_609_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
return v___x_614_;
}
else
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_le(v___x_611_, v___x_611_);
if (v___x_615_ == 0)
{
if (v___x_613_ == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v_args_609_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_612_);
return v___x_616_;
}
else
{
size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; 
v___x_617_ = ((size_t)0ULL);
v___x_618_ = lean_usize_of_nat(v___x_611_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_609_, v___x_617_, v___x_618_, v___x_612_, v_a_585_, v_a_586_);
lean_dec_ref(v_args_609_);
return v___x_619_;
}
}
else
{
size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((size_t)0ULL);
v___x_621_ = lean_usize_of_nat(v___x_611_);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_609_, v___x_620_, v___x_621_, v___x_612_, v_a_585_, v_a_586_);
lean_dec_ref(v_args_609_);
return v___x_622_;
}
}
}
case 4:
{
lean_object* v_cases_623_; lean_object* v_discr_624_; lean_object* v_alts_625_; lean_object* v___x_626_; 
v_cases_623_ = lean_ctor_get(v_code_584_, 0);
lean_inc_ref(v_cases_623_);
lean_dec_ref_known(v_code_584_, 1);
v_discr_624_ = lean_ctor_get(v_cases_623_, 2);
lean_inc(v_discr_624_);
v_alts_625_ = lean_ctor_get(v_cases_623_, 3);
lean_inc_ref(v_alts_625_);
lean_dec_ref(v_cases_623_);
v___x_626_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_discr_624_, v_a_585_, v_a_586_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_647_; 
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v___x_626_, 0);
lean_dec(v_unused_648_);
v___x_628_ = v___x_626_;
v_isShared_629_ = v_isSharedCheck_647_;
goto v_resetjp_627_;
}
else
{
lean_dec(v___x_626_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_647_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_array_get_size(v_alts_625_);
v___x_632_ = lean_box(0);
v___x_633_ = lean_nat_dec_lt(v___x_630_, v___x_631_);
if (v___x_633_ == 0)
{
lean_object* v___x_635_; 
lean_dec_ref(v_alts_625_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_632_);
v___x_635_ = v___x_628_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_632_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
else
{
uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_le(v___x_631_, v___x_631_);
if (v___x_637_ == 0)
{
if (v___x_633_ == 0)
{
lean_object* v___x_639_; 
lean_dec_ref(v_alts_625_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_632_);
v___x_639_ = v___x_628_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_632_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
size_t v___x_641_; size_t v___x_642_; lean_object* v___x_643_; 
lean_del_object(v___x_628_);
v___x_641_ = ((size_t)0ULL);
v___x_642_ = lean_usize_of_nat(v___x_631_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_625_, v___x_641_, v___x_642_, v___x_632_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec_ref(v_alts_625_);
return v___x_643_;
}
}
else
{
size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; 
lean_del_object(v___x_628_);
v___x_644_ = ((size_t)0ULL);
v___x_645_ = lean_usize_of_nat(v___x_631_);
v___x_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_625_, v___x_644_, v___x_645_, v___x_632_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec_ref(v_alts_625_);
return v___x_646_;
}
}
}
}
else
{
lean_dec_ref(v_alts_625_);
return v___x_626_;
}
}
case 5:
{
lean_object* v_fvarId_649_; lean_object* v___x_650_; 
v_fvarId_649_ = lean_ctor_get(v_code_584_, 0);
lean_inc(v_fvarId_649_);
lean_dec_ref_known(v_code_584_, 1);
v___x_650_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_649_, v_a_585_, v_a_586_);
return v___x_650_;
}
case 6:
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_658_; 
v_isSharedCheck_658_ = !lean_is_exclusive(v_code_584_);
if (v_isSharedCheck_658_ == 0)
{
lean_object* v_unused_659_; 
v_unused_659_ = lean_ctor_get(v_code_584_, 0);
lean_dec(v_unused_659_);
v___x_652_ = v_code_584_;
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
else
{
lean_dec(v_code_584_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_658_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_box(0);
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 0);
lean_ctor_set(v___x_652_, 0, v___x_654_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
default: 
{
lean_object* v_decl_660_; lean_object* v_k_661_; 
v_decl_660_ = lean_ctor_get(v_code_584_, 0);
lean_inc_ref(v_decl_660_);
v_k_661_ = lean_ctor_get(v_code_584_, 1);
lean_inc_ref(v_k_661_);
lean_dec_ref(v_code_584_);
v_decl_593_ = v_decl_660_;
v_k_594_ = v_k_661_;
v___y_595_ = v_a_585_;
v___y_596_ = v_a_586_;
v___y_597_ = v_a_587_;
v___y_598_ = v_a_588_;
v___y_599_ = v_a_589_;
v___y_600_ = v_a_590_;
goto v___jp_592_;
}
}
v___jp_592_:
{
lean_object* v_value_601_; lean_object* v___x_602_; 
v_value_601_ = lean_ctor_get(v_decl_593_, 4);
lean_inc_ref(v_value_601_);
lean_dec_ref(v_decl_593_);
v___x_602_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_value_601_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_dec_ref_known(v___x_602_, 1);
v_code_584_ = v_k_594_;
v_a_585_ = v___y_595_;
v_a_586_ = v___y_596_;
v_a_587_ = v___y_597_;
v_a_588_ = v___y_598_;
v_a_589_ = v___y_599_;
v_a_590_ = v___y_600_;
goto _start;
}
else
{
lean_dec_ref(v_k_594_);
return v___x_602_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FindUsed_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_584_ = stack[0].m_obj;
lean_object* v_a_585_ = stack[1].m_obj;
lean_object* v_a_586_ = stack[2].m_obj;
lean_object* v_a_587_ = stack[3].m_obj;
lean_object* v_a_588_ = stack[4].m_obj;
lean_object* v_a_589_ = stack[5].m_obj;
lean_object* v_a_590_ = stack[6].m_obj;
lean_object* v_res_662_;
v_res_662_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_code_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
stack->m_obj
 = v_res_662_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object* v_as_663_, size_t v_i_664_, size_t v_stop_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___y_675_; uint8_t v___x_681_; 
v___x_681_ = lean_usize_dec_eq(v_i_664_, v_stop_665_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
v___x_682_ = lean_array_uget_borrowed(v_as_663_, v_i_664_);
switch(lean_obj_tag(v___x_682_))
{
case 0:
{
lean_object* v_code_683_; 
v_code_683_ = lean_ctor_get(v___x_682_, 2);
lean_inc_ref(v_code_683_);
v___y_675_ = v_code_683_;
goto v___jp_674_;
}
case 1:
{
lean_object* v_code_684_; 
v_code_684_ = lean_ctor_get(v___x_682_, 1);
lean_inc_ref(v_code_684_);
v___y_675_ = v_code_684_;
goto v___jp_674_;
}
default: 
{
lean_object* v_code_685_; 
v_code_685_ = lean_ctor_get(v___x_682_, 0);
lean_inc_ref(v_code_685_);
v___y_675_ = v_code_685_;
goto v___jp_674_;
}
}
}
else
{
lean_object* v___x_686_; 
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v_b_666_);
return v___x_686_;
}
v___jp_674_:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Compiler_LCNF_FindUsed_visit(v___y_675_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; size_t v___x_678_; size_t v___x_679_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = ((size_t)1ULL);
v___x_679_ = lean_usize_add(v_i_664_, v___x_678_);
v_i_664_ = v___x_679_;
v_b_666_ = v_a_677_;
goto _start;
}
else
{
return v___x_676_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_663_ = stack[0].m_obj;
size_t v_i_664_ = stack[1].m_num;
size_t v_stop_665_ = stack[2].m_num;
lean_object* v_b_666_ = stack[3].m_obj;
lean_object* v___y_667_ = stack[4].m_obj;
lean_object* v___y_668_ = stack[5].m_obj;
lean_object* v___y_669_ = stack[6].m_obj;
lean_object* v___y_670_ = stack[7].m_obj;
lean_object* v___y_671_ = stack[8].m_obj;
lean_object* v___y_672_ = stack[9].m_obj;
lean_object* v_res_687_;
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_as_663_, v_i_664_, v_stop_665_, v_b_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
stack->m_obj
 = v_res_687_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object* v_as_688_, lean_object* v_i_689_, lean_object* v_stop_690_, lean_object* v_b_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
size_t v_i_boxed_699_; size_t v_stop_boxed_700_; lean_object* v_res_701_; 
v_i_boxed_699_ = lean_unbox_usize(v_i_689_);
lean_dec(v_i_689_);
v_stop_boxed_700_ = lean_unbox_usize(v_stop_690_);
lean_dec(v_stop_690_);
v_res_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_as_688_, v_i_boxed_699_, v_stop_boxed_700_, v_b_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v_as_688_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object* v_code_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_code_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
return v_res_710_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(lean_object* v_f_711_, lean_object* v_v_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
if (lean_obj_tag(v_v_712_) == 0)
{
lean_object* v_code_720_; lean_object* v___x_721_; 
v_code_720_ = lean_ctor_get(v_v_712_, 0);
lean_inc_ref(v_code_720_);
lean_dec_ref_known(v_v_712_, 1);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
v___x_721_ = lean_apply_8(v_f_711_, v_code_720_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, lean_box(0));
return v___x_721_;
}
else
{
lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v_f_711_);
v_isSharedCheck_729_ = !lean_is_exclusive(v_v_712_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v_v_712_, 0);
lean_dec(v_unused_730_);
v___x_723_ = v_v_712_;
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
else
{
lean_dec(v_v_712_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_box(0);
if (v_isShared_724_ == 0)
{
lean_ctor_set_tag(v___x_723_, 0);
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_711_ = stack[0].m_obj;
lean_object* v_v_712_ = stack[1].m_obj;
lean_object* v___y_713_ = stack[2].m_obj;
lean_object* v___y_714_ = stack[3].m_obj;
lean_object* v___y_715_ = stack[4].m_obj;
lean_object* v___y_716_ = stack[5].m_obj;
lean_object* v___y_717_ = stack[6].m_obj;
lean_object* v___y_718_ = stack[7].m_obj;
lean_object* v_res_731_;
v_res_731_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_711_, v_v_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
stack->m_obj
 = v_res_731_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg___boxed(lean_object* v_f_732_, lean_object* v_v_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_732_, v_v_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_741_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(uint8_t v_pu_742_, lean_object* v_f_743_, lean_object* v_v_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_743_, v_v_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
return v___x_752_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_742_ = stack[0].m_num;
lean_object* v_f_743_ = stack[1].m_obj;
lean_object* v_v_744_ = stack[2].m_obj;
lean_object* v___y_745_ = stack[3].m_obj;
lean_object* v___y_746_ = stack[4].m_obj;
lean_object* v___y_747_ = stack[5].m_obj;
lean_object* v___y_748_ = stack[6].m_obj;
lean_object* v___y_749_ = stack[7].m_obj;
lean_object* v___y_750_ = stack[8].m_obj;
lean_object* v_res_753_;
v_res_753_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(v_pu_742_, v_f_743_, v_v_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___boxed(lean_object* v_pu_754_, lean_object* v_f_755_, lean_object* v_v_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v_pu_boxed_764_; lean_object* v_res_765_; 
v_pu_boxed_764_ = lean_unbox(v_pu_754_);
v_res_765_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(v_pu_boxed_764_, v_f_755_, v_v_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_765_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object* v_as_766_, size_t v_i_767_, size_t v_stop_768_, lean_object* v_b_769_){
_start:
{
uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_eq(v_i_767_, v_stop_768_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v_fvarId_772_; lean_object* v___x_773_; size_t v___x_774_; size_t v___x_775_; 
v___x_771_ = lean_array_uget_borrowed(v_as_766_, v_i_767_);
v_fvarId_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_fvarId_772_);
v___x_773_ = l_Lean_FVarIdSet_insert(v_b_769_, v_fvarId_772_);
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_767_, v___x_774_);
v_i_767_ = v___x_775_;
v_b_769_ = v___x_773_;
goto _start;
}
else
{
return v_b_769_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_766_ = stack[0].m_obj;
size_t v_i_767_ = stack[1].m_num;
size_t v_stop_768_ = stack[2].m_num;
lean_object* v_b_769_ = stack[3].m_obj;
lean_object* v_res_777_;
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_as_766_, v_i_767_, v_stop_768_, v_b_769_);
stack->m_obj
 = v_res_777_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_, lean_object* v_b_781_){
_start:
{
size_t v_i_boxed_782_; size_t v_stop_boxed_783_; lean_object* v_res_784_; 
v_i_boxed_782_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_783_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_as_778_, v_i_boxed_782_, v_stop_boxed_783_, v_b_781_);
lean_dec_ref(v_as_778_);
return v_res_784_;
}
}
lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object* v_decl_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_toSignature_792_; lean_object* v_value_793_; lean_object* v_params_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___y_798_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_toSignature_792_ = lean_ctor_get(v_decl_786_, 0);
v_value_793_ = lean_ctor_get(v_decl_786_, 1);
lean_inc_ref(v_value_793_);
v_params_794_ = lean_ctor_get(v_toSignature_792_, 3);
v___x_795_ = lean_box(1);
v___x_796_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_array_get_size(v_params_794_);
v___x_822_ = lean_nat_dec_lt(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
v___y_798_ = v___x_795_;
goto v___jp_797_;
}
else
{
uint8_t v___x_823_; 
v___x_823_ = lean_nat_dec_le(v___x_821_, v___x_821_);
if (v___x_823_ == 0)
{
if (v___x_822_ == 0)
{
v___y_798_ = v___x_795_;
goto v___jp_797_;
}
else
{
size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((size_t)0ULL);
v___x_825_ = lean_usize_of_nat(v___x_821_);
v___x_826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_794_, v___x_824_, v___x_825_, v___x_795_);
v___y_798_ = v___x_826_;
goto v___jp_797_;
}
}
else
{
size_t v___x_827_; size_t v___x_828_; lean_object* v___x_829_; 
v___x_827_ = ((size_t)0ULL);
v___x_828_ = lean_usize_of_nat(v___x_821_);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_794_, v___x_827_, v___x_828_, v___x_795_);
v___y_798_ = v___x_829_;
goto v___jp_797_;
}
}
v___jp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_799_ = ((lean_object*)(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0));
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_decl_786_);
lean_ctor_set(v___x_800_, 1, v___y_798_);
v___x_801_ = lean_st_mk_ref(v___x_796_);
v___x_802_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v___x_799_, v_value_793_, v___x_800_, v___x_801_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec_ref_known(v___x_800_, 2);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_810_; 
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v___x_802_, 0);
lean_dec(v_unused_811_);
v___x_804_ = v___x_802_;
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
else
{
lean_dec(v___x_802_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_st_ref_get(v___x_801_);
lean_dec(v___x_801_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v___x_801_);
v_a_812_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_802_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_802_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FindUsed_collectUsedParams_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_786_ = stack[0].m_obj;
lean_object* v_a_787_ = stack[1].m_obj;
lean_object* v_a_788_ = stack[2].m_obj;
lean_object* v_a_789_ = stack[3].m_obj;
lean_object* v_a_790_ = stack[4].m_obj;
lean_object* v_res_830_;
v_res_830_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
stack->m_obj
 = v_res_830_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(lean_object* v_decl_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
return v_res_837_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0(void){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object* v_msg_839_){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0);
v___x_841_ = lean_panic_fn_borrowed(v___x_840_, v_msg_839_);
return v___x_841_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(lean_object* v_args_842_, lean_object* v_upperBound_843_, lean_object* v___x_844_, lean_object* v_a_845_, lean_object* v_b_846_){
_start:
{
lean_object* v_a_849_; uint8_t v___x_856_; 
v___x_856_ = lean_nat_dec_lt(v_a_845_, v_upperBound_843_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_dec(v_a_845_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v_b_846_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_858_ = lean_array_get_size(v___x_844_);
v___x_859_ = lean_nat_dec_lt(v_a_845_, v___x_858_);
if (v___x_859_ == 0)
{
goto v___jp_853_;
}
else
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = lean_array_fget_borrowed(v___x_844_, v_a_845_);
v___x_861_ = lean_unbox(v___x_860_);
if (v___x_861_ == 0)
{
v_a_849_ = v_b_846_;
goto v___jp_848_;
}
else
{
goto v___jp_853_;
}
}
}
v___jp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_add(v_a_845_, v___x_850_);
lean_dec(v_a_845_);
v_a_845_ = v___x_851_;
v_b_846_ = v_a_849_;
goto _start;
}
v___jp_853_:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_array_fget_borrowed(v_args_842_, v_a_845_);
lean_inc(v___x_854_);
v___x_855_ = lean_array_push(v_b_846_, v___x_854_);
v_a_849_ = v___x_855_;
goto v___jp_848_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_842_ = stack[0].m_obj;
lean_object* v_upperBound_843_ = stack[1].m_obj;
lean_object* v___x_844_ = stack[2].m_obj;
lean_object* v_a_845_ = stack[3].m_obj;
lean_object* v_b_846_ = stack[4].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_842_, v_upperBound_843_, v___x_844_, v_a_845_, v_b_846_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(lean_object* v_args_863_, lean_object* v_upperBound_864_, lean_object* v___x_865_, lean_object* v_a_866_, lean_object* v_b_867_, lean_object* v___y_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_863_, v_upperBound_864_, v___x_865_, v_a_866_, v_b_867_);
lean_dec_ref(v___x_865_);
lean_dec(v_upperBound_864_);
lean_dec_ref(v_args_863_);
return v_res_869_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_873_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2));
v___x_874_ = lean_unsigned_to_nat(9u);
v___x_875_ = lean_unsigned_to_nat(650u);
v___x_876_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1));
v___x_877_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0));
v___x_878_ = l_mkPanicMessageWithDecl(v___x_877_, v___x_876_, v___x_875_, v___x_874_, v___x_873_);
return v___x_878_;
}
}
lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* v_code_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_decl_893_; lean_object* v_k_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; 
switch(lean_obj_tag(v_code_885_))
{
case 0:
{
lean_object* v_decl_1007_; lean_object* v_k_1008_; lean_object* v_argsNew_1010_; lean_object* v___y_1011_; lean_object* v_auxDeclName_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v_value_1069_; 
v_decl_1007_ = lean_ctor_get(v_code_885_, 0);
v_k_1008_ = lean_ctor_get(v_code_885_, 1);
v_value_1069_ = lean_ctor_get(v_decl_1007_, 3);
if (lean_obj_tag(v_value_1069_) == 3)
{
lean_object* v_declName_1070_; lean_object* v_args_1071_; lean_object* v_declName_1072_; lean_object* v_auxDeclName_1073_; lean_object* v_paramMask_1074_; uint8_t v_allUnused_1075_; uint8_t v___x_1076_; 
v_declName_1070_ = lean_ctor_get(v_value_1069_, 0);
v_args_1071_ = lean_ctor_get(v_value_1069_, 2);
v_declName_1072_ = lean_ctor_get(v_a_886_, 0);
v_auxDeclName_1073_ = lean_ctor_get(v_a_886_, 1);
v_paramMask_1074_ = lean_ctor_get(v_a_886_, 2);
v_allUnused_1075_ = lean_ctor_get_uint8(v_a_886_, sizeof(void*)*3);
v___x_1076_ = lean_name_eq(v_declName_1070_, v_declName_1072_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
lean_inc_ref(v_k_1008_);
v___x_1077_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_1008_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1114_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1114_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1114_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
size_t v___x_1082_; size_t v___x_1083_; uint8_t v___x_1084_; 
v___x_1082_ = lean_ptr_addr(v_k_1008_);
v___x_1083_ = lean_ptr_addr(v_a_1078_);
v___x_1084_ = lean_usize_dec_eq(v___x_1082_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1094_; 
lean_inc_ref(v_decl_1007_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; 
v_unused_1095_ = lean_ctor_get(v_code_885_, 1);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_1096_);
v___x_1086_ = v_code_885_;
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
else
{
lean_dec(v_code_885_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1094_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 1, v_a_1078_);
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_decl_1007_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_a_1078_);
v___x_1089_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1091_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1089_);
v___x_1091_ = v___x_1080_;
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
size_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_ptr_addr(v_decl_1007_);
v___x_1098_ = lean_usize_dec_eq(v___x_1097_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1108_; 
lean_inc_ref(v_decl_1007_);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; lean_object* v_unused_1110_; 
v_unused_1109_ = lean_ctor_get(v_code_885_, 1);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_1110_);
v___x_1100_ = v_code_885_;
v_isShared_1101_ = v_isSharedCheck_1108_;
goto v_resetjp_1099_;
}
else
{
lean_dec(v_code_885_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1108_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v_a_1078_);
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_decl_1007_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_a_1078_);
v___x_1103_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1105_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1103_);
v___x_1105_ = v___x_1080_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v___x_1112_; 
lean_dec(v_a_1078_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v_code_885_);
v___x_1112_ = v___x_1080_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_code_885_);
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
else
{
lean_dec_ref_known(v_code_885_, 2);
return v___x_1077_;
}
}
else
{
if (v_allUnused_1075_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1115_ = lean_array_get_size(v_args_1071_);
v___x_1116_ = lean_unsigned_to_nat(0u);
v___x_1117_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_1118_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1071_, v___x_1115_, v_paramMask_1074_, v___x_1116_, v___x_1117_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v_argsNew_1010_ = v_a_1119_;
v___y_1011_ = v_a_886_;
v_auxDeclName_1012_ = v_auxDeclName_1073_;
v___y_1013_ = v_a_887_;
v___y_1014_ = v_a_888_;
v___y_1015_ = v_a_889_;
v___y_1016_ = v_a_890_;
goto v___jp_1009_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref_known(v_code_885_, 2);
v_a_1120_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1128_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5));
v___x_1129_ = lean_array_get_size(v_paramMask_1074_);
v___x_1130_ = lean_array_get_size(v_args_1071_);
v___x_1131_ = l_Array_extract___redArg(v_args_1071_, v___x_1129_, v___x_1130_);
v___x_1132_ = l_Array_append___redArg(v___x_1128_, v___x_1131_);
lean_dec_ref(v___x_1131_);
v_argsNew_1010_ = v___x_1132_;
v___y_1011_ = v_a_886_;
v_auxDeclName_1012_ = v_auxDeclName_1073_;
v___y_1013_ = v_a_887_;
v___y_1014_ = v_a_888_;
v___y_1015_ = v_a_889_;
v___y_1016_ = v_a_890_;
goto v___jp_1009_;
}
}
}
else
{
lean_object* v___x_1133_; 
lean_inc_ref(v_k_1008_);
v___x_1133_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_1008_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1170_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1170_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1170_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
size_t v___x_1138_; size_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1138_ = lean_ptr_addr(v_k_1008_);
v___x_1139_ = lean_ptr_addr(v_a_1134_);
v___x_1140_ = lean_usize_dec_eq(v___x_1138_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1150_; 
lean_inc_ref(v_decl_1007_);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1151_ = lean_ctor_get(v_code_885_, 1);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_1152_);
v___x_1142_ = v_code_885_;
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
else
{
lean_dec(v_code_885_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1150_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_a_1134_);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_decl_1007_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_a_1134_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1145_);
v___x_1147_ = v___x_1136_;
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
size_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_ptr_addr(v_decl_1007_);
v___x_1154_ = lean_usize_dec_eq(v___x_1153_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1164_; 
lean_inc_ref(v_decl_1007_);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; lean_object* v_unused_1166_; 
v_unused_1165_ = lean_ctor_get(v_code_885_, 1);
lean_dec(v_unused_1165_);
v_unused_1166_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_1166_);
v___x_1156_ = v_code_885_;
v_isShared_1157_ = v_isSharedCheck_1164_;
goto v_resetjp_1155_;
}
else
{
lean_dec(v_code_885_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1164_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v_a_1134_);
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_decl_1007_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_a_1134_);
v___x_1159_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1161_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1159_);
v___x_1161_ = v___x_1136_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_object* v___x_1168_; 
lean_dec(v_a_1134_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v_code_885_);
v___x_1168_ = v___x_1136_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_code_885_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_885_, 2);
return v___x_1133_;
}
}
v___jp_1009_:
{
uint8_t v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1017_ = 0;
v___x_1018_ = lean_box(0);
lean_inc(v_auxDeclName_1012_);
v___x_1019_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1019_, 0, v_auxDeclName_1012_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
lean_ctor_set(v___x_1019_, 2, v_argsNew_1010_);
lean_inc_ref(v_decl_1007_);
v___x_1020_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1017_, v_decl_1007_, v___x_1019_, v___y_1014_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
lean_inc_ref(v_k_1008_);
v___x_1022_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_1008_, v___y_1011_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1060_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1060_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1060_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
size_t v___x_1027_; size_t v___x_1028_; uint8_t v___x_1029_; 
v___x_1027_ = lean_ptr_addr(v_k_1008_);
v___x_1028_ = lean_ptr_addr(v_a_1023_);
v___x_1029_ = lean_usize_dec_eq(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1039_; 
v_isSharedCheck_1039_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; lean_object* v_unused_1041_; 
v_unused_1040_ = lean_ctor_get(v_code_885_, 1);
lean_dec(v_unused_1040_);
v_unused_1041_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_1041_);
v___x_1031_ = v_code_885_;
v_isShared_1032_ = v_isSharedCheck_1039_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v_code_885_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1039_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v_a_1023_);
lean_ctor_set(v___x_1031_, 0, v_a_1021_);
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1021_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_a_1023_);
v___x_1034_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1034_);
v___x_1036_ = v___x_1025_;
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
size_t v___x_1042_; size_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1042_ = lean_ptr_addr(v_decl_1007_);
v___x_1043_ = lean_ptr_addr(v_a_1021_);
v___x_1044_ = lean_usize_dec_eq(v___x_1042_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1054_; 
v_isSharedCheck_1054_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; lean_object* v_unused_1056_; 
v_unused_1055_ = lean_ctor_get(v_code_885_, 1);
lean_dec(v_unused_1055_);
v_unused_1056_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_1056_);
v___x_1046_ = v_code_885_;
v_isShared_1047_ = v_isSharedCheck_1054_;
goto v_resetjp_1045_;
}
else
{
lean_dec(v_code_885_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1054_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v_a_1023_);
lean_ctor_set(v___x_1046_, 0, v_a_1021_);
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1021_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_a_1023_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1049_);
v___x_1051_ = v___x_1025_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
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
else
{
lean_object* v___x_1058_; 
lean_dec(v_a_1023_);
lean_dec(v_a_1021_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v_code_885_);
v___x_1058_ = v___x_1025_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_code_885_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
else
{
lean_dec(v_a_1021_);
lean_dec_ref_known(v_code_885_, 2);
return v___x_1022_;
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref_known(v_code_885_, 2);
v_a_1061_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1020_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1020_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1171_; lean_object* v_k_1172_; 
v_decl_1171_ = lean_ctor_get(v_code_885_, 0);
v_k_1172_ = lean_ctor_get(v_code_885_, 1);
lean_inc_ref(v_k_1172_);
lean_inc_ref(v_decl_1171_);
v_decl_893_ = v_decl_1171_;
v_k_894_ = v_k_1172_;
v___y_895_ = v_a_886_;
v___y_896_ = v_a_887_;
v___y_897_ = v_a_888_;
v___y_898_ = v_a_889_;
v___y_899_ = v_a_890_;
goto v___jp_892_;
}
case 2:
{
lean_object* v_decl_1173_; lean_object* v_k_1174_; 
v_decl_1173_ = lean_ctor_get(v_code_885_, 0);
v_k_1174_ = lean_ctor_get(v_code_885_, 1);
lean_inc_ref(v_k_1174_);
lean_inc_ref(v_decl_1173_);
v_decl_893_ = v_decl_1173_;
v_k_894_ = v_k_1174_;
v___y_895_ = v_a_886_;
v___y_896_ = v_a_887_;
v___y_897_ = v_a_888_;
v___y_898_ = v_a_889_;
v___y_899_ = v_a_890_;
goto v___jp_892_;
}
case 4:
{
lean_object* v_cases_1175_; lean_object* v_typeName_1176_; lean_object* v_resultType_1177_; lean_object* v_discr_1178_; lean_object* v_alts_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1218_; 
v_cases_1175_ = lean_ctor_get(v_code_885_, 0);
lean_inc_ref(v_cases_1175_);
v_typeName_1176_ = lean_ctor_get(v_cases_1175_, 0);
v_resultType_1177_ = lean_ctor_get(v_cases_1175_, 1);
v_discr_1178_ = lean_ctor_get(v_cases_1175_, 2);
v_alts_1179_ = lean_ctor_get(v_cases_1175_, 3);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_cases_1175_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1181_ = v_cases_1175_;
v_isShared_1182_ = v_isSharedCheck_1218_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_alts_1179_);
lean_inc(v_discr_1178_);
lean_inc(v_resultType_1177_);
lean_inc(v_typeName_1176_);
lean_dec(v_cases_1175_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1218_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1179_);
v___x_1184_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v___x_1183_, v_alts_1179_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1209_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1209_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1209_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
size_t v___x_1189_; size_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1189_ = lean_ptr_addr(v_alts_1179_);
lean_dec_ref(v_alts_1179_);
v___x_1190_ = lean_ptr_addr(v_a_1185_);
v___x_1191_ = lean_usize_dec_eq(v___x_1189_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1204_; 
v_isSharedCheck_1204_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; 
v_unused_1205_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_1205_);
v___x_1193_ = v_code_885_;
v_isShared_1194_ = v_isSharedCheck_1204_;
goto v_resetjp_1192_;
}
else
{
lean_dec(v_code_885_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1204_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 3, v_a_1185_);
v___x_1196_ = v___x_1181_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_typeName_1176_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_resultType_1177_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_discr_1178_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_a_1185_);
v___x_1196_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1196_);
v___x_1198_ = v___x_1193_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1198_);
v___x_1200_ = v___x_1187_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
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
else
{
lean_object* v___x_1207_; 
lean_dec(v_a_1185_);
lean_del_object(v___x_1181_);
lean_dec(v_discr_1178_);
lean_dec_ref(v_resultType_1177_);
lean_dec(v_typeName_1176_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v_code_885_);
v___x_1207_ = v___x_1187_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_code_885_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_del_object(v___x_1181_);
lean_dec_ref(v_alts_1179_);
lean_dec(v_discr_1178_);
lean_dec_ref(v_resultType_1177_);
lean_dec(v_typeName_1176_);
lean_dec_ref_known(v_code_885_, 1);
v_a_1210_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1184_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1184_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
default: 
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v_code_885_);
return v___x_1219_;
}
}
v___jp_892_:
{
lean_object* v_params_900_; lean_object* v_type_901_; lean_object* v_value_902_; uint8_t v___x_903_; lean_object* v___x_904_; 
v_params_900_ = lean_ctor_get(v_decl_893_, 2);
lean_inc_ref(v_params_900_);
v_type_901_ = lean_ctor_get(v_decl_893_, 3);
lean_inc_ref(v_type_901_);
v_value_902_ = lean_ctor_get(v_decl_893_, 4);
v___x_903_ = 0;
lean_inc_ref(v_value_902_);
v___x_904_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_value_902_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_903_, v_decl_893_, v_type_901_, v_params_900_, v_a_905_, v___y_897_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_908_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_906_, 1);
v___x_908_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_908_) == 0)
{
switch(lean_obj_tag(v_code_885_))
{
case 1:
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_948_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_948_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_948_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_948_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_decl_913_; lean_object* v_k_914_; size_t v___x_915_; size_t v___x_916_; uint8_t v___x_917_; 
v_decl_913_ = lean_ctor_get(v_code_885_, 0);
v_k_914_ = lean_ctor_get(v_code_885_, 1);
v___x_915_ = lean_ptr_addr(v_k_914_);
v___x_916_ = lean_ptr_addr(v_a_909_);
v___x_917_ = lean_usize_dec_eq(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_927_; 
v_isSharedCheck_927_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; lean_object* v_unused_929_; 
v_unused_928_ = lean_ctor_get(v_code_885_, 1);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_929_);
v___x_919_ = v_code_885_;
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
else
{
lean_dec(v_code_885_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 1, v_a_909_);
lean_ctor_set(v___x_919_, 0, v_a_907_);
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_907_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_a_909_);
v___x_922_ = v_reuseFailAlloc_926_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_922_);
v___x_924_ = v___x_911_;
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
size_t v___x_930_; size_t v___x_931_; uint8_t v___x_932_; 
v___x_930_ = lean_ptr_addr(v_decl_913_);
v___x_931_ = lean_ptr_addr(v_a_907_);
v___x_932_ = lean_usize_dec_eq(v___x_930_, v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_942_; 
v_isSharedCheck_942_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; 
v_unused_943_ = lean_ctor_get(v_code_885_, 1);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_944_);
v___x_934_ = v_code_885_;
v_isShared_935_ = v_isSharedCheck_942_;
goto v_resetjp_933_;
}
else
{
lean_dec(v_code_885_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_942_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 1, v_a_909_);
lean_ctor_set(v___x_934_, 0, v_a_907_);
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_907_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_a_909_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_937_);
v___x_939_ = v___x_911_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v___x_946_; 
lean_dec(v_a_909_);
lean_dec(v_a_907_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_code_885_);
v___x_946_ = v___x_911_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_code_885_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
case 2:
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_988_; 
v_a_949_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_988_ == 0)
{
v___x_951_ = v___x_908_;
v_isShared_952_ = v_isSharedCheck_988_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_908_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_988_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_decl_953_; lean_object* v_k_954_; size_t v___x_955_; size_t v___x_956_; uint8_t v___x_957_; 
v_decl_953_ = lean_ctor_get(v_code_885_, 0);
v_k_954_ = lean_ctor_get(v_code_885_, 1);
v___x_955_ = lean_ptr_addr(v_k_954_);
v___x_956_ = lean_ptr_addr(v_a_949_);
v___x_957_ = lean_usize_dec_eq(v___x_955_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_967_; 
v_isSharedCheck_967_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; lean_object* v_unused_969_; 
v_unused_968_ = lean_ctor_get(v_code_885_, 1);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_969_);
v___x_959_ = v_code_885_;
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
else
{
lean_dec(v_code_885_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v_a_949_);
lean_ctor_set(v___x_959_, 0, v_a_907_);
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_907_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_a_949_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_962_);
v___x_964_ = v___x_951_;
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
size_t v___x_970_; size_t v___x_971_; uint8_t v___x_972_; 
v___x_970_ = lean_ptr_addr(v_decl_953_);
v___x_971_ = lean_ptr_addr(v_a_907_);
v___x_972_ = lean_usize_dec_eq(v___x_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_982_; 
v_isSharedCheck_982_ = !lean_is_exclusive(v_code_885_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; lean_object* v_unused_984_; 
v_unused_983_ = lean_ctor_get(v_code_885_, 1);
lean_dec(v_unused_983_);
v_unused_984_ = lean_ctor_get(v_code_885_, 0);
lean_dec(v_unused_984_);
v___x_974_ = v_code_885_;
v_isShared_975_ = v_isSharedCheck_982_;
goto v_resetjp_973_;
}
else
{
lean_dec(v_code_885_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_982_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_a_949_);
lean_ctor_set(v___x_974_, 0, v_a_907_);
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_907_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_a_949_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_977_);
v___x_979_ = v___x_951_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v___x_986_; 
lean_dec(v_a_949_);
lean_dec(v_a_907_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v_code_885_);
v___x_986_ = v___x_951_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_code_885_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
default: 
{
lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_a_907_);
lean_dec_ref(v_code_885_);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v___x_908_, 0);
lean_dec(v_unused_998_);
v___x_990_ = v___x_908_;
v_isShared_991_ = v_isSharedCheck_997_;
goto v_resetjp_989_;
}
else
{
lean_dec(v___x_908_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_997_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_992_ = lean_obj_once(&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3, &l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once, _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3);
v___x_993_ = l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(v___x_992_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_993_);
v___x_995_ = v___x_990_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
else
{
lean_dec(v_a_907_);
lean_dec_ref(v_code_885_);
return v___x_908_;
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v_k_894_);
lean_dec_ref(v_code_885_);
v_a_999_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_906_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_906_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
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
lean_dec_ref(v_type_901_);
lean_dec_ref(v_params_900_);
lean_dec_ref(v_k_894_);
lean_dec_ref(v_decl_893_);
lean_dec_ref(v_code_885_);
return v___x_904_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ReduceArity_reduce_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_885_ = stack[0].m_obj;
lean_object* v_a_886_ = stack[1].m_obj;
lean_object* v_a_887_ = stack[2].m_obj;
lean_object* v_a_888_ = stack[3].m_obj;
lean_object* v_a_889_ = stack[4].m_obj;
lean_object* v_a_890_ = stack[5].m_obj;
lean_object* v_res_1220_;
v_res_1220_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_code_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
stack->m_obj
 = v_res_1220_;
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(lean_object* v_i_1221_, lean_object* v_as_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_array_get_size(v_as_1222_);
v___x_1230_ = lean_nat_dec_lt(v_i_1221_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; 
lean_dec(v_i_1221_);
v___x_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_as_1222_);
return v___x_1231_;
}
else
{
lean_object* v_a_1232_; lean_object* v___y_1234_; 
v_a_1232_ = lean_array_fget_borrowed(v_as_1222_, v_i_1221_);
switch(lean_obj_tag(v_a_1232_))
{
case 0:
{
lean_object* v_code_1256_; 
v_code_1256_ = lean_ctor_get(v_a_1232_, 2);
lean_inc_ref(v_code_1256_);
v___y_1234_ = v_code_1256_;
goto v___jp_1233_;
}
case 1:
{
lean_object* v_code_1257_; 
v_code_1257_ = lean_ctor_get(v_a_1232_, 1);
lean_inc_ref(v_code_1257_);
v___y_1234_ = v_code_1257_;
goto v___jp_1233_;
}
default: 
{
lean_object* v_code_1258_; 
v_code_1258_ = lean_ctor_get(v_a_1232_, 0);
lean_inc_ref(v_code_1258_);
v___y_1234_ = v_code_1258_;
goto v___jp_1233_;
}
}
v___jp_1233_:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v___y_1234_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; uint8_t v___x_1240_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref_known(v___x_1235_, 1);
lean_inc(v_a_1232_);
v___x_1237_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1232_, v_a_1236_);
v___x_1238_ = lean_ptr_addr(v_a_1232_);
v___x_1239_ = lean_ptr_addr(v___x_1237_);
v___x_1240_ = lean_usize_dec_eq(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_nat_add(v_i_1221_, v___x_1241_);
v___x_1243_ = lean_array_fset(v_as_1222_, v_i_1221_, v___x_1237_);
lean_dec(v_i_1221_);
v_i_1221_ = v___x_1242_;
v_as_1222_ = v___x_1243_;
goto _start;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec_ref(v___x_1237_);
v___x_1245_ = lean_unsigned_to_nat(1u);
v___x_1246_ = lean_nat_add(v_i_1221_, v___x_1245_);
lean_dec(v_i_1221_);
v_i_1221_ = v___x_1246_;
goto _start;
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_as_1222_);
lean_dec(v_i_1221_);
v_a_1248_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1235_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1235_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1221_ = stack[0].m_obj;
lean_object* v_as_1222_ = stack[1].m_obj;
lean_object* v___y_1223_ = stack[2].m_obj;
lean_object* v___y_1224_ = stack[3].m_obj;
lean_object* v___y_1225_ = stack[4].m_obj;
lean_object* v___y_1226_ = stack[5].m_obj;
lean_object* v___y_1227_ = stack[6].m_obj;
lean_object* v_res_1259_;
v_res_1259_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v_i_1221_, v_as_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
stack->m_obj
 = v_res_1259_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(lean_object* v_i_1260_, lean_object* v_as_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v_i_1260_, v_as_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec_ref(v___y_1262_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object* v_code_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_code_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec_ref(v_a_1270_);
return v_res_1276_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object* v_args_1277_, lean_object* v_upperBound_1278_, lean_object* v___x_1279_, lean_object* v_inst_1280_, lean_object* v_R_1281_, lean_object* v_a_1282_, lean_object* v_b_1283_, lean_object* v_c_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1277_, v_upperBound_1278_, v___x_1279_, v_a_1282_, v_b_1283_);
return v___x_1291_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_1277_ = stack[0].m_obj;
lean_object* v_upperBound_1278_ = stack[1].m_obj;
lean_object* v___x_1279_ = stack[2].m_obj;
lean_object* v_a_1282_ = stack[5].m_obj;
lean_object* v_b_1283_ = stack[6].m_obj;
lean_object* v___y_1285_ = stack[8].m_obj;
lean_object* v___y_1286_ = stack[9].m_obj;
lean_object* v___y_1287_ = stack[10].m_obj;
lean_object* v___y_1288_ = stack[11].m_obj;
lean_object* v___y_1289_ = stack[12].m_obj;
lean_object* v_res_1292_;
v_res_1292_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(v_args_1277_, v_upperBound_1278_, v___x_1279_, lean_box(0), lean_box(0), v_a_1282_, v_b_1283_, lean_box(0), v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
stack->m_obj
 = v_res_1292_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object* v_args_1293_, lean_object* v_upperBound_1294_, lean_object* v___x_1295_, lean_object* v_inst_1296_, lean_object* v_R_1297_, lean_object* v_a_1298_, lean_object* v_b_1299_, lean_object* v_c_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(v_args_1293_, v_upperBound_1294_, v___x_1295_, v_inst_1296_, v_R_1297_, v_a_1298_, v_b_1299_, v_c_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec_ref(v___x_1295_);
lean_dec(v_upperBound_1294_);
lean_dec_ref(v_args_1293_);
return v_res_1307_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object* v_f_1308_, lean_object* v_v_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
if (lean_obj_tag(v_v_1309_) == 0)
{
lean_object* v_code_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1340_; 
v_code_1316_ = lean_ctor_get(v_v_1309_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_v_1309_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1318_ = v_v_1309_;
v_isShared_1319_ = v_isSharedCheck_1340_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_code_1316_);
lean_dec(v_v_1309_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1340_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; 
lean_inc(v___y_1314_);
lean_inc_ref(v___y_1313_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc_ref(v___y_1310_);
v___x_1320_ = lean_apply_7(v_f_1308_, v_code_1316_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, lean_box(0));
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1331_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1331_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v_a_1321_);
v___x_1326_ = v___x_1318_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1326_);
v___x_1328_ = v___x_1323_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_del_object(v___x_1318_);
v_a_1332_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1320_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1320_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
else
{
lean_object* v___x_1341_; 
lean_dec_ref(v_f_1308_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_v_1309_);
return v___x_1341_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1308_ = stack[0].m_obj;
lean_object* v_v_1309_ = stack[1].m_obj;
lean_object* v___y_1310_ = stack[2].m_obj;
lean_object* v___y_1311_ = stack[3].m_obj;
lean_object* v___y_1312_ = stack[4].m_obj;
lean_object* v___y_1313_ = stack[5].m_obj;
lean_object* v___y_1314_ = stack[6].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1308_, v_v_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object* v_f_1343_, lean_object* v_v_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1343_, v_v_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1351_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(uint8_t v_pu_1352_, lean_object* v_f_1353_, lean_object* v_v_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1353_, v_v_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1352_ = stack[0].m_num;
lean_object* v_f_1353_ = stack[1].m_obj;
lean_object* v_v_1354_ = stack[2].m_obj;
lean_object* v___y_1355_ = stack[3].m_obj;
lean_object* v___y_1356_ = stack[4].m_obj;
lean_object* v___y_1357_ = stack[5].m_obj;
lean_object* v___y_1358_ = stack[6].m_obj;
lean_object* v___y_1359_ = stack[7].m_obj;
lean_object* v_res_1362_;
v_res_1362_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(v_pu_1352_, v_f_1353_, v_v_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
stack->m_obj
 = v_res_1362_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object* v_pu_1363_, lean_object* v_f_1364_, lean_object* v_v_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
uint8_t v_pu_boxed_1372_; lean_object* v_res_1373_; 
v_pu_boxed_1372_ = lean_unbox(v_pu_1363_);
v_res_1373_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(v_pu_boxed_1372_, v_f_1364_, v_v_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1373_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1374_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0);
v___x_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1375_);
return v___x_1376_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1377_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1378_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
lean_ctor_set(v___x_1380_, 2, v___x_1379_);
lean_ctor_set(v___x_1380_, 3, v___x_1379_);
lean_ctor_set(v___x_1380_, 4, v___x_1378_);
lean_ctor_set(v___x_1380_, 5, v___x_1378_);
lean_ctor_set(v___x_1380_, 6, v___x_1378_);
lean_ctor_set(v___x_1380_, 7, v___x_1378_);
lean_ctor_set(v___x_1380_, 8, v___x_1378_);
lean_ctor_set(v___x_1380_, 9, v___x_1378_);
lean_ctor_set(v___x_1380_, 10, v___x_1378_);
lean_ctor_set(v___x_1380_, 11, v___x_1377_);
return v___x_1380_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3(void){
_start:
{
lean_object* v___x_1381_; double v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_float_of_nat(v___x_1381_);
return v___x_1382_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* v_cls_1386_, lean_object* v_msg_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_ref_1393_; lean_object* v___x_1394_; lean_object* v_env_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_ref_1393_ = lean_ctor_get(v___y_1390_, 2);
v___x_1394_ = lean_st_ref_get(v___y_1391_);
v_env_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc_ref(v_env_1395_);
lean_dec(v___x_1394_);
v___x_1396_ = lean_st_ref_get(v___y_1389_);
v___x_1397_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1388_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1457_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1457_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1457_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v_lctx_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1455_; 
v_lctx_1402_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v___x_1396_, 1);
lean_dec(v_unused_1456_);
v___x_1404_ = v___x_1396_;
v_isShared_1405_ = v_isSharedCheck_1455_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_lctx_1402_);
lean_dec(v___x_1396_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1455_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1406_ = lean_unbox(v_a_1398_);
lean_dec(v_a_1398_);
v___x_1407_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1402_, v___x_1406_);
lean_dec_ref(v_lctx_1402_);
v___x_1408_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1390_);
v___x_1409_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2);
v___x_1410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1410_, 0, v_env_1395_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
lean_ctor_set(v___x_1410_, 2, v___x_1407_);
lean_ctor_set(v___x_1410_, 3, v___x_1408_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set_tag(v___x_1404_, 3);
lean_ctor_set(v___x_1404_, 1, v_msg_1387_);
lean_ctor_set(v___x_1404_, 0, v___x_1410_);
v___x_1412_ = v___x_1404_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_msg_1387_);
v___x_1412_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v_traceState_1414_; lean_object* v_env_1415_; lean_object* v_nextMacroScope_1416_; lean_object* v_ngen_1417_; lean_object* v_auxDeclNGen_1418_; lean_object* v_cache_1419_; lean_object* v_recordedDeps_1420_; lean_object* v_messages_1421_; lean_object* v_infoState_1422_; lean_object* v_snapshotTasks_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1453_; 
v___x_1413_ = lean_st_ref_take(v___y_1391_);
v_traceState_1414_ = lean_ctor_get(v___x_1413_, 4);
v_env_1415_ = lean_ctor_get(v___x_1413_, 0);
v_nextMacroScope_1416_ = lean_ctor_get(v___x_1413_, 1);
v_ngen_1417_ = lean_ctor_get(v___x_1413_, 2);
v_auxDeclNGen_1418_ = lean_ctor_get(v___x_1413_, 3);
v_cache_1419_ = lean_ctor_get(v___x_1413_, 5);
v_recordedDeps_1420_ = lean_ctor_get(v___x_1413_, 6);
v_messages_1421_ = lean_ctor_get(v___x_1413_, 7);
v_infoState_1422_ = lean_ctor_get(v___x_1413_, 8);
v_snapshotTasks_1423_ = lean_ctor_get(v___x_1413_, 9);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1425_ = v___x_1413_;
v_isShared_1426_ = v_isSharedCheck_1453_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_snapshotTasks_1423_);
lean_inc(v_infoState_1422_);
lean_inc(v_messages_1421_);
lean_inc(v_recordedDeps_1420_);
lean_inc(v_cache_1419_);
lean_inc(v_traceState_1414_);
lean_inc(v_auxDeclNGen_1418_);
lean_inc(v_ngen_1417_);
lean_inc(v_nextMacroScope_1416_);
lean_inc(v_env_1415_);
lean_dec(v___x_1413_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1453_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
uint64_t v_tid_1427_; lean_object* v_traces_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1452_; 
v_tid_1427_ = lean_ctor_get_uint64(v_traceState_1414_, sizeof(void*)*1);
v_traces_1428_ = lean_ctor_get(v_traceState_1414_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_traceState_1414_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1430_ = v_traceState_1414_;
v_isShared_1431_ = v_isSharedCheck_1452_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_traces_1428_);
lean_dec(v_traceState_1414_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1452_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; double v___x_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3);
v___x_1435_ = 0;
v___x_1436_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4));
v___x_1437_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1437_, 0, v_cls_1386_);
lean_ctor_set(v___x_1437_, 1, v___x_1433_);
lean_ctor_set(v___x_1437_, 2, v___x_1436_);
lean_ctor_set_float(v___x_1437_, sizeof(void*)*3, v___x_1434_);
lean_ctor_set_float(v___x_1437_, sizeof(void*)*3 + 8, v___x_1434_);
lean_ctor_set_uint8(v___x_1437_, sizeof(void*)*3 + 16, v___x_1435_);
v___x_1438_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5));
v___x_1439_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1412_);
lean_ctor_set(v___x_1439_, 2, v___x_1438_);
lean_inc(v_ref_1393_);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v_ref_1393_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
v___x_1441_ = l_Lean_PersistentArray_push___redArg(v_traces_1428_, v___x_1440_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1441_);
v___x_1443_ = v___x_1430_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1441_);
lean_ctor_set_uint64(v_reuseFailAlloc_1451_, sizeof(void*)*1, v_tid_1427_);
v___x_1443_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1445_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 4, v___x_1443_);
v___x_1445_ = v___x_1425_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_env_1415_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_nextMacroScope_1416_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_ngen_1417_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_auxDeclNGen_1418_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1450_, 5, v_cache_1419_);
lean_ctor_set(v_reuseFailAlloc_1450_, 6, v_recordedDeps_1420_);
lean_ctor_set(v_reuseFailAlloc_1450_, 7, v_messages_1421_);
lean_ctor_set(v_reuseFailAlloc_1450_, 8, v_infoState_1422_);
lean_ctor_set(v_reuseFailAlloc_1450_, 9, v_snapshotTasks_1423_);
v___x_1445_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = lean_st_ref_put(v___y_1391_, v___x_1445_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1432_);
v___x_1448_ = v___x_1400_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1432_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
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
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v___x_1396_);
lean_dec_ref(v_env_1395_);
lean_dec_ref(v_msg_1387_);
lean_dec(v_cls_1386_);
v_a_1458_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1397_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1397_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1386_ = stack[0].m_obj;
lean_object* v_msg_1387_ = stack[1].m_obj;
lean_object* v___y_1388_ = stack[2].m_obj;
lean_object* v___y_1389_ = stack[3].m_obj;
lean_object* v___y_1390_ = stack[4].m_obj;
lean_object* v___y_1391_ = stack[5].m_obj;
lean_object* v_res_1466_;
v_res_1466_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v_cls_1386_, v_msg_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
stack->m_obj
 = v_res_1466_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___boxed(lean_object* v_cls_1467_, lean_object* v_msg_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v_cls_1467_, v_msg_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
return v_res_1474_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(lean_object* v_name_1476_, lean_object* v___x_1477_, lean_object* v___x_1478_, uint8_t v___x_1479_, lean_object* v_value_1480_, lean_object* v_code_1481_, uint8_t v_safe_1482_, uint8_t v_recursive_1483_, lean_object* v_inlineAttr_x3f_1484_, lean_object* v_params_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_inc(v___x_1477_);
v___x_1491_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1491_, 0, v_name_1476_);
lean_ctor_set(v___x_1491_, 1, v___x_1477_);
lean_ctor_set(v___x_1491_, 2, v___x_1478_);
lean_ctor_set_uint8(v___x_1491_, sizeof(void*)*3, v___x_1479_);
v___x_1492_ = 0;
v___x_1493_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___closed__0));
v___x_1494_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v___x_1493_, v_value_1480_, v___x_1491_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec_ref_known(v___x_1491_, 3);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref_known(v___x_1494_, 1);
v___x_1496_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_1492_, v_code_1481_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
lean_inc_ref(v_params_1485_);
v___x_1498_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_1492_, v_params_1485_, v_a_1497_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v_a_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v___x_1498_, 1);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1501_, 0, v___x_1477_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
lean_ctor_set(v___x_1501_, 2, v_a_1499_);
lean_ctor_set(v___x_1501_, 3, v_params_1485_);
lean_ctor_set_uint8(v___x_1501_, sizeof(void*)*4, v_safe_1482_);
v___x_1502_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v_a_1495_);
lean_ctor_set(v___x_1502_, 2, v_inlineAttr_x3f_1484_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*3, v_recursive_1483_);
lean_inc_ref(v___x_1502_);
v___x_1503_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1502_, v___y_1489_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v___x_1503_, 0);
lean_dec(v_unused_1511_);
v___x_1505_ = v___x_1503_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_dec(v___x_1503_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1502_);
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1502_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec_ref_known(v___x_1502_, 3);
v_a_1512_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1503_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1503_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_a_1495_);
lean_dec_ref(v_params_1485_);
lean_dec(v_inlineAttr_x3f_1484_);
lean_dec(v___x_1477_);
v_a_1520_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1498_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1498_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_a_1495_);
lean_dec_ref(v_params_1485_);
lean_dec(v_inlineAttr_x3f_1484_);
lean_dec(v___x_1477_);
v_a_1528_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1496_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1496_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v_params_1485_);
lean_dec(v_inlineAttr_x3f_1484_);
lean_dec_ref(v_code_1481_);
lean_dec(v___x_1477_);
v_a_1536_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1494_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1494_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1476_ = stack[0].m_obj;
lean_object* v___x_1477_ = stack[1].m_obj;
lean_object* v___x_1478_ = stack[2].m_obj;
uint8_t v___x_1479_ = stack[3].m_num;
lean_object* v_value_1480_ = stack[4].m_obj;
lean_object* v_code_1481_ = stack[5].m_obj;
uint8_t v_safe_1482_ = stack[6].m_num;
uint8_t v_recursive_1483_ = stack[7].m_num;
lean_object* v_inlineAttr_x3f_1484_ = stack[8].m_obj;
lean_object* v_params_1485_ = stack[9].m_obj;
lean_object* v___y_1486_ = stack[10].m_obj;
lean_object* v___y_1487_ = stack[11].m_obj;
lean_object* v___y_1488_ = stack[12].m_obj;
lean_object* v___y_1489_ = stack[13].m_obj;
lean_object* v_res_1544_;
v_res_1544_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(v_name_1476_, v___x_1477_, v___x_1478_, v___x_1479_, v_value_1480_, v_code_1481_, v_safe_1482_, v_recursive_1483_, v_inlineAttr_x3f_1484_, v_params_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
stack->m_obj
 = v_res_1544_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed(lean_object* v_name_1545_, lean_object* v___x_1546_, lean_object* v___x_1547_, lean_object* v___x_1548_, lean_object* v_value_1549_, lean_object* v_code_1550_, lean_object* v_safe_1551_, lean_object* v_recursive_1552_, lean_object* v_inlineAttr_x3f_1553_, lean_object* v_params_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v___x_11941__boxed_1560_; uint8_t v_safe_boxed_1561_; uint8_t v_recursive_boxed_1562_; lean_object* v_res_1563_; 
v___x_11941__boxed_1560_ = lean_unbox(v___x_1548_);
v_safe_boxed_1561_ = lean_unbox(v_safe_1551_);
v_recursive_boxed_1562_ = lean_unbox(v_recursive_1552_);
v_res_1563_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(v_name_1545_, v___x_1546_, v___x_1547_, v___x_11941__boxed_1560_, v_value_1549_, v_code_1550_, v_safe_boxed_1561_, v_recursive_boxed_1562_, v_inlineAttr_x3f_1553_, v_params_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1563_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(lean_object* v___x_1570_, uint8_t v___x_1571_, lean_object* v_name_1572_, lean_object* v_levelParams_1573_, lean_object* v_type_1574_, lean_object* v_a_1575_, uint8_t v_safe_1576_, uint8_t v___x_1577_, lean_object* v_____r_1578_, lean_object* v_args_1579_, uint8_t v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1570_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
lean_ctor_set(v___x_1588_, 2, v_args_1579_);
v___x_1589_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__1));
v___x_1590_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1571_, v___x_1588_, v___x_1589_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v_fvarId_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v_fvarId_1592_ = lean_ctor_get(v_a_1591_, 0);
lean_inc(v_fvarId_1592_);
v___x_1593_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1593_, 0, v_fvarId_1592_);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v_a_1591_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
v___x_1596_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1596_, 0, v_name_1572_);
lean_ctor_set(v___x_1596_, 1, v_levelParams_1573_);
lean_ctor_set(v___x_1596_, 2, v_type_1574_);
lean_ctor_set(v___x_1596_, 3, v_a_1575_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*4, v_safe_1576_);
v___x_1597_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__2));
v___x_1598_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1595_);
lean_ctor_set(v___x_1598_, 2, v___x_1597_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*3, v___x_1577_);
lean_inc_ref(v___x_1598_);
v___x_1599_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1598_, v___y_1585_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v___x_1599_, 0);
lean_dec(v_unused_1607_);
v___x_1601_ = v___x_1599_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_dec(v___x_1599_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1598_);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1598_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec_ref_known(v___x_1598_, 3);
v_a_1608_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1599_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1599_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v_a_1575_);
lean_dec_ref(v_type_1574_);
lean_dec(v_levelParams_1573_);
lean_dec(v_name_1572_);
v_a_1616_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1590_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1590_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1570_ = stack[0].m_obj;
uint8_t v___x_1571_ = stack[1].m_num;
lean_object* v_name_1572_ = stack[2].m_obj;
lean_object* v_levelParams_1573_ = stack[3].m_obj;
lean_object* v_type_1574_ = stack[4].m_obj;
lean_object* v_a_1575_ = stack[5].m_obj;
uint8_t v_safe_1576_ = stack[6].m_num;
uint8_t v___x_1577_ = stack[7].m_num;
lean_object* v_____r_1578_ = stack[8].m_obj;
lean_object* v_args_1579_ = stack[9].m_obj;
uint8_t v___y_1580_ = stack[10].m_num;
lean_object* v___y_1581_ = stack[11].m_obj;
lean_object* v___y_1582_ = stack[12].m_obj;
lean_object* v___y_1583_ = stack[13].m_obj;
lean_object* v___y_1584_ = stack[14].m_obj;
lean_object* v___y_1585_ = stack[15].m_obj;
lean_object* v_res_1624_;
v_res_1624_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___x_1570_, v___x_1571_, v_name_1572_, v_levelParams_1573_, v_type_1574_, v_a_1575_, v_safe_1576_, v___x_1577_, v_____r_1578_, v_args_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
stack->m_obj
 = v_res_1624_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___boxed(lean_object** _args){
lean_object* v___x_1625_ = _args[0];
lean_object* v___x_1626_ = _args[1];
lean_object* v_name_1627_ = _args[2];
lean_object* v_levelParams_1628_ = _args[3];
lean_object* v_type_1629_ = _args[4];
lean_object* v_a_1630_ = _args[5];
lean_object* v_safe_1631_ = _args[6];
lean_object* v___x_1632_ = _args[7];
lean_object* v_____r_1633_ = _args[8];
lean_object* v_args_1634_ = _args[9];
lean_object* v___y_1635_ = _args[10];
lean_object* v___y_1636_ = _args[11];
lean_object* v___y_1637_ = _args[12];
lean_object* v___y_1638_ = _args[13];
lean_object* v___y_1639_ = _args[14];
lean_object* v___y_1640_ = _args[15];
lean_object* v___y_1641_ = _args[16];
_start:
{
uint8_t v___x_12157__boxed_1642_; uint8_t v_safe_boxed_1643_; uint8_t v___x_12159__boxed_1644_; uint8_t v___y_12161__boxed_1645_; lean_object* v_res_1646_; 
v___x_12157__boxed_1642_ = lean_unbox(v___x_1626_);
v_safe_boxed_1643_ = lean_unbox(v_safe_1631_);
v___x_12159__boxed_1644_ = lean_unbox(v___x_1632_);
v___y_12161__boxed_1645_ = lean_unbox(v___y_1635_);
v_res_1646_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___x_1625_, v___x_12157__boxed_1642_, v_name_1627_, v_levelParams_1628_, v_type_1629_, v_a_1630_, v_safe_boxed_1643_, v___x_12159__boxed_1644_, v_____r_1633_, v_args_1634_, v___y_12161__boxed_1645_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* v_x_1647_, lean_object* v_x_1648_){
_start:
{
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_inc(v_x_1647_);
return v_x_1647_;
}
else
{
lean_object* v_key_1649_; lean_object* v_tail_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_key_1649_ = lean_ctor_get(v_x_1648_, 0);
v_tail_1650_ = lean_ctor_get(v_x_1648_, 2);
v___x_1651_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1647_, v_tail_1650_);
lean_inc(v_key_1649_);
v___x_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1652_, 0, v_key_1649_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1653_, v_x_1654_);
lean_dec(v_x_1654_);
lean_dec(v_x_1653_);
return v_res_1655_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object* v_as_1656_, size_t v_i_1657_, size_t v_stop_1658_, lean_object* v_b_1659_){
_start:
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_usize_dec_eq(v_i_1657_, v_stop_1658_);
if (v___x_1660_ == 0)
{
size_t v___x_1661_; size_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1661_ = ((size_t)1ULL);
v___x_1662_ = lean_usize_sub(v_i_1657_, v___x_1661_);
v___x_1663_ = lean_array_uget_borrowed(v_as_1656_, v___x_1662_);
v___x_1664_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_b_1659_, v___x_1663_);
lean_dec(v_b_1659_);
v_i_1657_ = v___x_1662_;
v_b_1659_ = v___x_1664_;
goto _start;
}
else
{
return v_b_1659_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1656_ = stack[0].m_obj;
size_t v_i_1657_ = stack[1].m_num;
size_t v_stop_1658_ = stack[2].m_num;
lean_object* v_b_1659_ = stack[3].m_obj;
lean_object* v_res_1666_;
v_res_1666_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_as_1656_, v_i_1657_, v_stop_1658_, v_b_1659_);
stack->m_obj
 = v_res_1666_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object* v_as_1667_, lean_object* v_i_1668_, lean_object* v_stop_1669_, lean_object* v_b_1670_){
_start:
{
size_t v_i_boxed_1671_; size_t v_stop_boxed_1672_; lean_object* v_res_1673_; 
v_i_boxed_1671_ = lean_unbox_usize(v_i_1668_);
lean_dec(v_i_1668_);
v_stop_boxed_1672_ = lean_unbox_usize(v_stop_1669_);
lean_dec(v_stop_1669_);
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_as_1667_, v_i_boxed_1671_, v_stop_boxed_1672_, v_b_1670_);
lean_dec_ref(v_as_1667_);
return v_res_1673_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object* v_m_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_buckets_1676_; lean_object* v___x_1677_; uint64_t v___x_1678_; uint64_t v___x_1679_; uint64_t v___x_1680_; uint64_t v_fold_1681_; uint64_t v___x_1682_; uint64_t v___x_1683_; uint64_t v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; size_t v___x_1687_; size_t v___x_1688_; size_t v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v_buckets_1676_ = lean_ctor_get(v_m_1674_, 1);
v___x_1677_ = lean_array_get_size(v_buckets_1676_);
v___x_1678_ = l_Lean_instHashableFVarId_hash(v_a_1675_);
v___x_1679_ = 32ULL;
v___x_1680_ = lean_uint64_shift_right(v___x_1678_, v___x_1679_);
v_fold_1681_ = lean_uint64_xor(v___x_1678_, v___x_1680_);
v___x_1682_ = 16ULL;
v___x_1683_ = lean_uint64_shift_right(v_fold_1681_, v___x_1682_);
v___x_1684_ = lean_uint64_xor(v_fold_1681_, v___x_1683_);
v___x_1685_ = lean_uint64_to_usize(v___x_1684_);
v___x_1686_ = lean_usize_of_nat(v___x_1677_);
v___x_1687_ = ((size_t)1ULL);
v___x_1688_ = lean_usize_sub(v___x_1686_, v___x_1687_);
v___x_1689_ = lean_usize_land(v___x_1685_, v___x_1688_);
v___x_1690_ = lean_array_uget_borrowed(v_buckets_1676_, v___x_1689_);
v___x_1691_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_1675_, v___x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1674_ = stack[0].m_obj;
lean_object* v_a_1675_ = stack[1].m_obj;
uint8_t v_res_1692_;
v_res_1692_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1674_, v_a_1675_);
stack->m_num = v_res_1692_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object* v_m_1693_, lean_object* v_a_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1693_, v_a_1694_);
lean_dec(v_a_1694_);
lean_dec_ref(v_m_1693_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* v_a_1697_, lean_object* v_as_1698_, size_t v_i_1699_, size_t v_stop_1700_, lean_object* v_b_1701_){
_start:
{
lean_object* v___y_1703_; uint8_t v___x_1707_; 
v___x_1707_ = lean_usize_dec_eq(v_i_1699_, v_stop_1700_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v_fvarId_1709_; uint8_t v___x_1710_; 
v___x_1708_ = lean_array_uget_borrowed(v_as_1698_, v_i_1699_);
v_fvarId_1709_ = lean_ctor_get(v___x_1708_, 0);
v___x_1710_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1697_, v_fvarId_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_inc(v___x_1708_);
v___x_1711_ = lean_array_push(v_b_1701_, v___x_1708_);
v___y_1703_ = v___x_1711_;
goto v___jp_1702_;
}
else
{
v___y_1703_ = v_b_1701_;
goto v___jp_1702_;
}
}
else
{
return v_b_1701_;
}
v___jp_1702_:
{
size_t v___x_1704_; size_t v___x_1705_; 
v___x_1704_ = ((size_t)1ULL);
v___x_1705_ = lean_usize_add(v_i_1699_, v___x_1704_);
v_i_1699_ = v___x_1705_;
v_b_1701_ = v___y_1703_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1697_ = stack[0].m_obj;
lean_object* v_as_1698_ = stack[1].m_obj;
size_t v_i_1699_ = stack[2].m_num;
size_t v_stop_1700_ = stack[3].m_num;
lean_object* v_b_1701_ = stack[4].m_obj;
lean_object* v_res_1712_;
v_res_1712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1697_, v_as_1698_, v_i_1699_, v_stop_1700_, v_b_1701_);
stack->m_obj
 = v_res_1712_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* v_a_1713_, lean_object* v_as_1714_, lean_object* v_i_1715_, lean_object* v_stop_1716_, lean_object* v_b_1717_){
_start:
{
size_t v_i_boxed_1718_; size_t v_stop_boxed_1719_; lean_object* v_res_1720_; 
v_i_boxed_1718_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_stop_boxed_1719_ = lean_unbox_usize(v_stop_1716_);
lean_dec(v_stop_1716_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1713_, v_as_1714_, v_i_boxed_1718_, v_stop_boxed_1719_, v_b_1717_);
lean_dec_ref(v_as_1714_);
lean_dec_ref(v_a_1713_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
if (lean_obj_tag(v_a_1721_) == 0)
{
lean_object* v___x_1723_; 
v___x_1723_ = l_List_reverse___redArg(v_a_1722_);
return v___x_1723_;
}
else
{
lean_object* v_head_1724_; lean_object* v_tail_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1734_; 
v_head_1724_ = lean_ctor_get(v_a_1721_, 0);
v_tail_1725_ = lean_ctor_get(v_a_1721_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_a_1721_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1727_ = v_a_1721_;
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_tail_1725_);
lean_inc(v_head_1724_);
lean_dec(v_a_1721_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1734_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = l_Lean_MessageData_ofExpr(v_head_1724_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v_a_1722_);
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_a_1722_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
v_a_1721_ = v_tail_1725_;
v_a_1722_ = v___x_1731_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object* v_as_1735_, size_t v_sz_1736_, size_t v_i_1737_, lean_object* v_b_1738_){
_start:
{
lean_object* v_a_1741_; uint8_t v___x_1745_; 
v___x_1745_ = lean_usize_dec_lt(v_i_1737_, v_sz_1736_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_b_1738_);
return v___x_1746_;
}
else
{
lean_object* v_snd_1747_; lean_object* v_fst_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1783_; 
v_snd_1747_ = lean_ctor_get(v_b_1738_, 1);
v_fst_1748_ = lean_ctor_get(v_b_1738_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_b_1738_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1750_ = v_b_1738_;
v_isShared_1751_ = v_isSharedCheck_1783_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_snd_1747_);
lean_inc(v_fst_1748_);
lean_dec(v_b_1738_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1783_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v_array_1752_; lean_object* v_start_1753_; lean_object* v_stop_1754_; uint8_t v___x_1755_; 
v_array_1752_ = lean_ctor_get(v_snd_1747_, 0);
v_start_1753_ = lean_ctor_get(v_snd_1747_, 1);
v_stop_1754_ = lean_ctor_get(v_snd_1747_, 2);
v___x_1755_ = lean_nat_dec_lt(v_start_1753_, v_stop_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1757_; 
if (v_isShared_1751_ == 0)
{
v___x_1757_ = v___x_1750_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_fst_1748_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_snd_1747_);
v___x_1757_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
else
{
lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1779_; 
lean_inc(v_stop_1754_);
lean_inc(v_start_1753_);
lean_inc_ref(v_array_1752_);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_snd_1747_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; lean_object* v_unused_1781_; lean_object* v_unused_1782_; 
v_unused_1780_ = lean_ctor_get(v_snd_1747_, 2);
lean_dec(v_unused_1780_);
v_unused_1781_ = lean_ctor_get(v_snd_1747_, 1);
lean_dec(v_unused_1781_);
v_unused_1782_ = lean_ctor_get(v_snd_1747_, 0);
lean_dec(v_unused_1782_);
v___x_1761_ = v_snd_1747_;
v_isShared_1762_ = v_isSharedCheck_1779_;
goto v_resetjp_1760_;
}
else
{
lean_dec(v_snd_1747_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1779_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_a_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
v_a_1763_ = lean_array_uget_borrowed(v_as_1735_, v_i_1737_);
v___x_1764_ = lean_array_fget(v_array_1752_, v_start_1753_);
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = lean_nat_add(v_start_1753_, v___x_1765_);
lean_dec(v_start_1753_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___x_1766_);
v___x_1768_ = v___x_1761_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_array_1752_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_stop_1754_);
v___x_1768_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
uint8_t v___x_1769_; 
v___x_1769_ = lean_unbox(v_a_1763_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1771_; 
lean_dec(v___x_1764_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1768_);
v___x_1771_ = v___x_1750_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_fst_1748_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1768_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
v_a_1741_ = v___x_1771_;
goto v___jp_1740_;
}
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1773_ = l_Lean_Compiler_LCNF_Param_toArg___redArg(v___x_1764_);
lean_dec(v___x_1764_);
v___x_1774_ = lean_array_push(v_fst_1748_, v___x_1773_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1768_);
lean_ctor_set(v___x_1750_, 0, v___x_1774_);
v___x_1776_ = v___x_1750_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___x_1768_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
v_a_1741_ = v___x_1776_;
goto v___jp_1740_;
}
}
}
}
}
}
}
v___jp_1740_:
{
size_t v___x_1742_; size_t v___x_1743_; 
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_add(v_i_1737_, v___x_1742_);
v_i_1737_ = v___x_1743_;
v_b_1738_ = v_a_1741_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1735_ = stack[0].m_obj;
size_t v_sz_1736_ = stack[1].m_num;
size_t v_i_1737_ = stack[2].m_num;
lean_object* v_b_1738_ = stack[3].m_obj;
lean_object* v_res_1784_;
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_1735_, v_sz_1736_, v_i_1737_, v_b_1738_);
stack->m_obj
 = v_res_1784_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object* v_as_1785_, lean_object* v_sz_1786_, lean_object* v_i_1787_, lean_object* v_b_1788_, lean_object* v___y_1789_){
_start:
{
size_t v_sz_boxed_1790_; size_t v_i_boxed_1791_; lean_object* v_res_1792_; 
v_sz_boxed_1790_ = lean_unbox_usize(v_sz_1786_);
lean_dec(v_sz_1786_);
v_i_boxed_1791_ = lean_unbox_usize(v_i_1787_);
lean_dec(v_i_1787_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_1785_, v_sz_boxed_1790_, v_i_boxed_1791_, v_b_1788_);
lean_dec_ref(v_as_1785_);
return v_res_1792_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t v_sz_1793_, size_t v_i_1794_, lean_object* v_bs_1795_, uint8_t v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_usize_dec_lt(v_i_1794_, v_sz_1793_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_bs_1795_);
return v___x_1804_;
}
else
{
uint8_t v___x_1805_; lean_object* v_v_1806_; lean_object* v___x_1807_; lean_object* v_bs_x27_1808_; lean_object* v___x_1809_; 
v___x_1805_ = 0;
v_v_1806_ = lean_array_uget(v_bs_1795_, v_i_1794_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v_bs_x27_1808_ = lean_array_uset(v_bs_1795_, v_i_1794_, v___x_1807_);
v___x_1809_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_1805_, v_v_1806_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; size_t v___x_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = ((size_t)1ULL);
v___x_1812_ = lean_usize_add(v_i_1794_, v___x_1811_);
v___x_1813_ = lean_array_uset(v_bs_x27_1808_, v_i_1794_, v_a_1810_);
v_i_1794_ = v___x_1812_;
v_bs_1795_ = v___x_1813_;
goto _start;
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
lean_dec_ref(v_bs_x27_1808_);
v_a_1815_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1809_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1809_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1793_ = stack[0].m_num;
size_t v_i_1794_ = stack[1].m_num;
lean_object* v_bs_1795_ = stack[2].m_obj;
uint8_t v___y_1796_ = stack[3].m_num;
lean_object* v___y_1797_ = stack[4].m_obj;
lean_object* v___y_1798_ = stack[5].m_obj;
lean_object* v___y_1799_ = stack[6].m_obj;
lean_object* v___y_1800_ = stack[7].m_obj;
lean_object* v___y_1801_ = stack[8].m_obj;
lean_object* v_res_1823_;
v_res_1823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_1793_, v_i_1794_, v_bs_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
stack->m_obj
 = v_res_1823_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* v_sz_1824_, lean_object* v_i_1825_, lean_object* v_bs_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
size_t v_sz_boxed_1834_; size_t v_i_boxed_1835_; uint8_t v___y_12618__boxed_1836_; lean_object* v_res_1837_; 
v_sz_boxed_1834_ = lean_unbox_usize(v_sz_1824_);
lean_dec(v_sz_1824_);
v_i_boxed_1835_ = lean_unbox_usize(v_i_1825_);
lean_dec(v_i_1825_);
v___y_12618__boxed_1836_ = lean_unbox(v___y_1827_);
v_res_1837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_boxed_1834_, v_i_boxed_1835_, v_bs_1826_, v___y_12618__boxed_1836_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
if (lean_obj_tag(v_a_1838_) == 0)
{
lean_object* v___x_1840_; 
v___x_1840_ = l_List_reverse___redArg(v_a_1839_);
return v___x_1840_;
}
else
{
lean_object* v_head_1841_; lean_object* v_tail_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1851_; 
v_head_1841_ = lean_ctor_get(v_a_1838_, 0);
v_tail_1842_ = lean_ctor_get(v_a_1838_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_a_1838_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1844_ = v_a_1838_;
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_tail_1842_);
lean_inc(v_head_1841_);
lean_dec(v_a_1838_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1846_ = l_Lean_mkFVar(v_head_1841_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v_a_1839_);
lean_ctor_set(v___x_1844_, 0, v___x_1846_);
v___x_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_a_1839_);
v___x_1848_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
v_a_1838_ = v_tail_1842_;
v_a_1839_ = v___x_1848_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(lean_object* v_a_1852_, lean_object* v_as_1853_, size_t v_i_1854_, size_t v_stop_1855_, lean_object* v_b_1856_){
_start:
{
lean_object* v___y_1858_; uint8_t v___x_1862_; 
v___x_1862_ = lean_usize_dec_eq(v_i_1854_, v_stop_1855_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v_fvarId_1864_; uint8_t v___x_1865_; 
v___x_1863_ = lean_array_uget_borrowed(v_as_1853_, v_i_1854_);
v_fvarId_1864_ = lean_ctor_get(v___x_1863_, 0);
v___x_1865_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1852_, v_fvarId_1864_);
if (v___x_1865_ == 0)
{
v___y_1858_ = v_b_1856_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1866_; 
lean_inc(v___x_1863_);
v___x_1866_ = lean_array_push(v_b_1856_, v___x_1863_);
v___y_1858_ = v___x_1866_;
goto v___jp_1857_;
}
}
else
{
return v_b_1856_;
}
v___jp_1857_:
{
size_t v___x_1859_; size_t v___x_1860_; 
v___x_1859_ = ((size_t)1ULL);
v___x_1860_ = lean_usize_add(v_i_1854_, v___x_1859_);
v_i_1854_ = v___x_1860_;
v_b_1856_ = v___y_1858_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1852_ = stack[0].m_obj;
lean_object* v_as_1853_ = stack[1].m_obj;
size_t v_i_1854_ = stack[2].m_num;
size_t v_stop_1855_ = stack[3].m_num;
lean_object* v_b_1856_ = stack[4].m_obj;
lean_object* v_res_1867_;
v_res_1867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1852_, v_as_1853_, v_i_1854_, v_stop_1855_, v_b_1856_);
stack->m_obj
 = v_res_1867_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6___boxed(lean_object* v_a_1868_, lean_object* v_as_1869_, lean_object* v_i_1870_, lean_object* v_stop_1871_, lean_object* v_b_1872_){
_start:
{
size_t v_i_boxed_1873_; size_t v_stop_boxed_1874_; lean_object* v_res_1875_; 
v_i_boxed_1873_ = lean_unbox_usize(v_i_1870_);
lean_dec(v_i_1870_);
v_stop_boxed_1874_ = lean_unbox_usize(v_stop_1871_);
lean_dec(v_stop_1871_);
v_res_1875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1868_, v_as_1869_, v_i_boxed_1873_, v_stop_boxed_1874_, v_b_1872_);
lean_dec_ref(v_as_1869_);
lean_dec_ref(v_a_1868_);
return v_res_1875_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object* v_a_1876_, lean_object* v_as_1877_, size_t v_i_1878_, size_t v_stop_1879_, lean_object* v_b_1880_){
_start:
{
lean_object* v___y_1882_; uint8_t v___x_1886_; 
v___x_1886_ = lean_usize_dec_eq(v_i_1878_, v_stop_1879_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v_fvarId_1888_; uint8_t v___x_1889_; 
v___x_1887_ = lean_array_uget_borrowed(v_as_1877_, v_i_1878_);
v_fvarId_1888_ = lean_ctor_get(v___x_1887_, 0);
v___x_1889_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1876_, v_fvarId_1888_);
if (v___x_1889_ == 0)
{
v___y_1882_ = v_b_1880_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1890_; 
lean_inc(v___x_1887_);
v___x_1890_ = lean_array_push(v_b_1880_, v___x_1887_);
v___y_1882_ = v___x_1890_;
goto v___jp_1881_;
}
}
else
{
return v_b_1880_;
}
v___jp_1881_:
{
size_t v___x_1883_; size_t v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = ((size_t)1ULL);
v___x_1884_ = lean_usize_add(v_i_1878_, v___x_1883_);
v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1876_, v_as_1877_, v___x_1884_, v_stop_1879_, v___y_1882_);
return v___x_1885_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1876_ = stack[0].m_obj;
lean_object* v_as_1877_ = stack[1].m_obj;
size_t v_i_1878_ = stack[2].m_num;
size_t v_stop_1879_ = stack[3].m_num;
lean_object* v_b_1880_ = stack[4].m_obj;
lean_object* v_res_1891_;
v_res_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1876_, v_as_1877_, v_i_1878_, v_stop_1879_, v_b_1880_);
stack->m_obj
 = v_res_1891_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object* v_a_1892_, lean_object* v_as_1893_, lean_object* v_i_1894_, lean_object* v_stop_1895_, lean_object* v_b_1896_){
_start:
{
size_t v_i_boxed_1897_; size_t v_stop_boxed_1898_; lean_object* v_res_1899_; 
v_i_boxed_1897_ = lean_unbox_usize(v_i_1894_);
lean_dec(v_i_1894_);
v_stop_boxed_1898_ = lean_unbox_usize(v_stop_1895_);
lean_dec(v_stop_1895_);
v_res_1899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1892_, v_as_1893_, v_i_boxed_1897_, v_stop_boxed_1898_, v_b_1896_);
lean_dec_ref(v_as_1893_);
lean_dec_ref(v_a_1892_);
return v_res_1899_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object* v_a_1900_, size_t v_sz_1901_, size_t v_i_1902_, lean_object* v_bs_1903_){
_start:
{
uint8_t v___x_1904_; 
v___x_1904_ = lean_usize_dec_lt(v_i_1902_, v_sz_1901_);
if (v___x_1904_ == 0)
{
return v_bs_1903_;
}
else
{
lean_object* v_v_1905_; lean_object* v_fvarId_1906_; lean_object* v___x_1907_; lean_object* v_bs_x27_1908_; uint8_t v___x_1909_; size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_v_1905_ = lean_array_uget_borrowed(v_bs_1903_, v_i_1902_);
v_fvarId_1906_ = lean_ctor_get(v_v_1905_, 0);
lean_inc(v_fvarId_1906_);
v___x_1907_ = lean_unsigned_to_nat(0u);
v_bs_x27_1908_ = lean_array_uset(v_bs_1903_, v_i_1902_, v___x_1907_);
v___x_1909_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1900_, v_fvarId_1906_);
lean_dec(v_fvarId_1906_);
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1902_, v___x_1910_);
v___x_1912_ = lean_box(v___x_1909_);
v___x_1913_ = lean_array_uset(v_bs_x27_1908_, v_i_1902_, v___x_1912_);
v_i_1902_ = v___x_1911_;
v_bs_1903_ = v___x_1913_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1900_ = stack[0].m_obj;
size_t v_sz_1901_ = stack[1].m_num;
size_t v_i_1902_ = stack[2].m_num;
lean_object* v_bs_1903_ = stack[3].m_obj;
lean_object* v_res_1915_;
v_res_1915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1900_, v_sz_1901_, v_i_1902_, v_bs_1903_);
stack->m_obj
 = v_res_1915_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object* v_a_1916_, lean_object* v_sz_1917_, lean_object* v_i_1918_, lean_object* v_bs_1919_){
_start:
{
size_t v_sz_boxed_1920_; size_t v_i_boxed_1921_; lean_object* v_res_1922_; 
v_sz_boxed_1920_ = lean_unbox_usize(v_sz_1917_);
lean_dec(v_sz_1917_);
v_i_boxed_1921_ = lean_unbox_usize(v_i_1918_);
lean_dec(v_i_1918_);
v_res_1922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1916_, v_sz_boxed_1920_, v_i_boxed_1921_, v_bs_1919_);
lean_dec_ref(v_a_1916_);
return v_res_1922_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* v_a_1923_, size_t v_sz_1924_, size_t v_i_1925_, lean_object* v_bs_1926_){
_start:
{
uint8_t v___x_1927_; 
v___x_1927_ = lean_usize_dec_lt(v_i_1925_, v_sz_1924_);
if (v___x_1927_ == 0)
{
return v_bs_1926_;
}
else
{
lean_object* v_v_1928_; lean_object* v_fvarId_1929_; lean_object* v___x_1930_; lean_object* v_bs_x27_1931_; uint8_t v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_v_1928_ = lean_array_uget_borrowed(v_bs_1926_, v_i_1925_);
v_fvarId_1929_ = lean_ctor_get(v_v_1928_, 0);
lean_inc(v_fvarId_1929_);
v___x_1930_ = lean_unsigned_to_nat(0u);
v_bs_x27_1931_ = lean_array_uset(v_bs_1926_, v_i_1925_, v___x_1930_);
v___x_1932_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1923_, v_fvarId_1929_);
lean_dec(v_fvarId_1929_);
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = lean_usize_add(v_i_1925_, v___x_1933_);
v___x_1935_ = lean_box(v___x_1932_);
v___x_1936_ = lean_array_uset(v_bs_x27_1931_, v_i_1925_, v___x_1935_);
v___x_1937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1923_, v_sz_1924_, v___x_1934_, v___x_1936_);
return v___x_1937_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1923_ = stack[0].m_obj;
size_t v_sz_1924_ = stack[1].m_num;
size_t v_i_1925_ = stack[2].m_num;
lean_object* v_bs_1926_ = stack[3].m_obj;
lean_object* v_res_1938_;
v_res_1938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1923_, v_sz_1924_, v_i_1925_, v_bs_1926_);
stack->m_obj
 = v_res_1938_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object* v_a_1939_, lean_object* v_sz_1940_, lean_object* v_i_1941_, lean_object* v_bs_1942_){
_start:
{
size_t v_sz_boxed_1943_; size_t v_i_boxed_1944_; lean_object* v_res_1945_; 
v_sz_boxed_1943_ = lean_unbox_usize(v_sz_1940_);
lean_dec(v_sz_1940_);
v_i_boxed_1944_ = lean_unbox_usize(v_i_1941_);
lean_dec(v_i_1941_);
v_res_1945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1939_, v_sz_boxed_1943_, v_i_boxed_1944_, v_bs_1942_);
lean_dec_ref(v_a_1939_);
return v_res_1945_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_unsigned_to_nat(16u);
v___x_1948_ = lean_mk_array(v___x_1947_, v___x_1946_);
return v___x_1948_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1949_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0);
v___x_1950_ = lean_unsigned_to_nat(0u);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v___x_1949_);
return v___x_1951_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = lean_box(0);
v___x_1961_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6));
v___x_1962_ = l_Lean_Expr_const___override(v___x_1961_, v___x_1960_);
return v___x_1962_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_1975_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14));
v___x_1976_ = l_Lean_Name_append(v___x_1975_, v___x_1974_);
return v___x_1976_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16));
v___x_1979_ = l_Lean_stringToMessageData(v___x_1978_);
return v___x_1979_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* v_decl_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
uint8_t v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v_value_2024_; 
v_value_2024_ = lean_ctor_get(v_decl_1980_, 1);
lean_inc_ref(v_value_2024_);
if (lean_obj_tag(v_value_2024_) == 0)
{
lean_object* v_toSignature_2025_; uint8_t v_recursive_2026_; lean_object* v_inlineAttr_x3f_2027_; lean_object* v_code_2028_; lean_object* v_name_2029_; lean_object* v_levelParams_2030_; lean_object* v_type_2031_; lean_object* v_params_2032_; uint8_t v_safe_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v_toSignature_2025_ = lean_ctor_get(v_decl_1980_, 0);
v_recursive_2026_ = lean_ctor_get_uint8(v_decl_1980_, sizeof(void*)*3);
v_inlineAttr_x3f_2027_ = lean_ctor_get(v_decl_1980_, 2);
v_code_2028_ = lean_ctor_get(v_value_2024_, 0);
v_name_2029_ = lean_ctor_get(v_toSignature_2025_, 0);
v_levelParams_2030_ = lean_ctor_get(v_toSignature_2025_, 1);
v_type_2031_ = lean_ctor_get(v_toSignature_2025_, 2);
v_params_2032_ = lean_ctor_get(v_toSignature_2025_, 3);
v_safe_2033_ = lean_ctor_get_uint8(v_toSignature_2025_, sizeof(void*)*4);
v___x_2034_ = lean_array_get_size(v_params_2032_);
v___x_2035_ = lean_unsigned_to_nat(0u);
v___x_2036_ = lean_nat_dec_eq(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; 
lean_inc_ref(v_code_2028_);
lean_inc_ref(v_decl_1980_);
v___x_2037_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2212_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2212_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2212_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_size_2042_; lean_object* v_buckets_2043_; uint8_t v___x_2044_; 
v_size_2042_ = lean_ctor_get(v_a_2038_, 0);
v_buckets_2043_ = lean_ctor_get(v_a_2038_, 1);
v___x_2044_ = lean_nat_dec_eq(v_size_2042_, v___x_2034_);
if (v___x_2044_ == 0)
{
lean_object* v_toCold_2045_; lean_object* v_options_2046_; lean_object* v_inheritedTraceOptions_2047_; uint8_t v_hasTrace_2048_; uint8_t v___x_2049_; lean_object* v___y_2051_; uint8_t v___y_2052_; uint8_t v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; size_t v___y_2057_; lean_object* v___y_2058_; size_t v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2107_; uint8_t v___y_2108_; uint8_t v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; size_t v___y_2113_; size_t v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2122_; uint8_t v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; size_t v___y_2126_; lean_object* v___y_2127_; size_t v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; 
lean_inc_ref(v_params_2032_);
lean_inc_ref(v_type_2031_);
lean_inc(v_levelParams_2030_);
lean_inc(v_name_2029_);
lean_inc(v_inlineAttr_x3f_2027_);
lean_del_object(v___x_2040_);
lean_dec_ref(v_decl_1980_);
v_toCold_2045_ = lean_ctor_get(v_a_1983_, 0);
v_options_2046_ = lean_ctor_get(v_toCold_2045_, 2);
v_inheritedTraceOptions_2047_ = lean_ctor_get(v_toCold_2045_, 11);
v_hasTrace_2048_ = lean_ctor_get_uint8(v_options_2046_, sizeof(void*)*1);
v___x_2049_ = lean_nat_dec_eq(v_size_2042_, v___x_2035_);
if (v_hasTrace_2048_ == 0)
{
v___y_2157_ = v_a_1981_;
v___y_2158_ = v_a_1982_;
v___y_2159_ = v_a_1983_;
v___y_2160_ = v_a_1984_;
goto v___jp_2156_;
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2178_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_2179_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15);
v___x_2180_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2047_, v_options_2046_, v___x_2179_);
if (v___x_2180_ == 0)
{
v___y_2157_ = v_a_1981_;
v___y_2158_ = v_a_1982_;
v___y_2159_ = v_a_1983_;
v___y_2160_ = v_a_1984_;
goto v___jp_2156_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___y_2185_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
lean_inc(v_name_2029_);
v___x_2181_ = l_Lean_MessageData_ofName(v_name_2029_);
v___x_2182_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2200_ = lean_box(0);
v___x_2201_ = lean_array_get_size(v_buckets_2043_);
v___x_2202_ = lean_nat_dec_lt(v___x_2035_, v___x_2201_);
if (v___x_2202_ == 0)
{
v___y_2185_ = v___x_2200_;
goto v___jp_2184_;
}
else
{
size_t v___x_2203_; size_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_usize_of_nat(v___x_2201_);
v___x_2204_ = ((size_t)0ULL);
v___x_2205_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_buckets_2043_, v___x_2203_, v___x_2204_, v___x_2200_);
v___y_2185_ = v___x_2205_;
goto v___jp_2184_;
}
v___jp_2184_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2186_ = lean_box(0);
v___x_2187_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(v___y_2185_, v___x_2186_);
v___x_2188_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(v___x_2187_, v___x_2186_);
v___x_2189_ = l_Lean_MessageData_ofList(v___x_2188_);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2183_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v___x_2178_, v___x_2190_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_dec_ref_known(v___x_2191_, 1);
v___y_2157_ = v_a_1981_;
v___y_2158_ = v_a_1982_;
v___y_2159_ = v_a_1983_;
v___y_2160_ = v_a_1984_;
goto v___jp_2156_;
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_a_2038_);
lean_dec_ref(v_params_2032_);
lean_dec_ref(v_type_2031_);
lean_dec(v_levelParams_2030_);
lean_dec(v_name_2029_);
lean_dec_ref(v_code_2028_);
lean_dec(v_inlineAttr_x3f_2027_);
lean_dec_ref_known(v_value_2024_, 1);
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
v___jp_2050_:
{
if (lean_obj_tag(v___y_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_a_2063_ = lean_ctor_get(v___y_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___y_2062_, 1);
v___x_2064_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1);
v___x_2065_ = lean_st_mk_ref(v___x_2064_);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v___y_2059_, v___y_2057_, v_params_2032_, v___x_2044_, v___x_2065_, v___y_2054_, v___y_2061_, v___y_2056_, v___y_2058_);
if (lean_obj_tag(v___x_2066_) == 0)
{
if (v___x_2049_ == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; size_t v_sz_2072_; lean_object* v___x_2073_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc_n(v_a_2067_, 2);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2068_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_2069_ = lean_array_get_size(v_a_2067_);
v___x_2070_ = l_Array_toSubarray___redArg(v_a_2067_, v___x_2035_, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2068_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v_sz_2072_ = lean_array_size(v___y_2060_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v___y_2060_, v_sz_2072_, v___y_2057_, v___x_2071_);
lean_dec_ref(v___y_2060_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v_fst_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v_fst_2075_ = lean_ctor_get(v_a_2074_, 0);
lean_inc(v_fst_2075_);
lean_dec(v_a_2074_);
v___x_2076_ = lean_box(0);
v___x_2077_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___y_2051_, v___y_2052_, v_name_2029_, v_levelParams_2030_, v_type_2031_, v_a_2067_, v_safe_2033_, v___x_2044_, v___x_2076_, v_fst_2075_, v___x_2044_, v___x_2065_, v___y_2054_, v___y_2061_, v___y_2056_, v___y_2058_);
v___y_1987_ = v___y_2053_;
v___y_1988_ = v_a_2063_;
v___y_1989_ = v___y_2055_;
v___y_1990_ = v___x_2065_;
v___y_1991_ = v___y_2061_;
v___y_1992_ = v___x_2077_;
goto v___jp_1986_;
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_a_2067_);
lean_dec(v___x_2065_);
lean_dec(v_a_2063_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2051_);
lean_dec_ref(v_type_2031_);
lean_dec(v_levelParams_2030_);
lean_dec(v_name_2029_);
v_a_2078_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2073_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2073_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec_ref(v___y_2060_);
v_a_2086_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2087_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5));
v___x_2088_ = lean_box(0);
v___x_2089_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___y_2051_, v___y_2052_, v_name_2029_, v_levelParams_2030_, v_type_2031_, v_a_2086_, v_safe_2033_, v___x_2044_, v___x_2088_, v___x_2087_, v___x_2044_, v___x_2065_, v___y_2054_, v___y_2061_, v___y_2056_, v___y_2058_);
v___y_1987_ = v___y_2053_;
v___y_1988_ = v_a_2063_;
v___y_1989_ = v___y_2055_;
v___y_1990_ = v___x_2065_;
v___y_1991_ = v___y_2061_;
v___y_1992_ = v___x_2089_;
goto v___jp_1986_;
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec(v___x_2065_);
lean_dec(v_a_2063_);
lean_dec_ref(v___y_2060_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2051_);
lean_dec_ref(v_type_2031_);
lean_dec(v_levelParams_2030_);
lean_dec(v_name_2029_);
v_a_2090_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2066_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2066_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec_ref(v___y_2060_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2051_);
lean_dec_ref(v_params_2032_);
lean_dec_ref(v_type_2031_);
lean_dec(v_levelParams_2030_);
lean_dec(v_name_2029_);
v_a_2098_ = lean_ctor_get(v___y_2062_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___y_2062_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___y_2062_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___y_2062_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
v___jp_2106_:
{
lean_object* v___x_2120_; 
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2112_);
lean_inc(v___y_2118_);
lean_inc_ref(v___y_2111_);
v___x_2120_ = lean_apply_6(v___y_2116_, v___y_2119_, v___y_2111_, v___y_2118_, v___y_2112_, v___y_2115_, lean_box(0));
v___y_2051_ = v___y_2107_;
v___y_2052_ = v___y_2108_;
v___y_2053_ = v___y_2109_;
v___y_2054_ = v___y_2111_;
v___y_2055_ = v___y_2110_;
v___y_2056_ = v___y_2112_;
v___y_2057_ = v___y_2113_;
v___y_2058_ = v___y_2115_;
v___y_2059_ = v___y_2114_;
v___y_2060_ = v___y_2117_;
v___y_2061_ = v___y_2118_;
v___y_2062_ = v___x_2120_;
goto v___jp_2050_;
}
v___jp_2121_:
{
if (v___x_2049_ == 0)
{
lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_2134_ = lean_nat_dec_lt(v___x_2035_, v___x_2034_);
if (v___x_2134_ == 0)
{
lean_dec(v_a_2038_);
v___y_2107_ = v___y_2122_;
v___y_2108_ = v___y_2123_;
v___y_2109_ = v___y_2123_;
v___y_2110_ = v___y_2132_;
v___y_2111_ = v___y_2124_;
v___y_2112_ = v___y_2125_;
v___y_2113_ = v___y_2126_;
v___y_2114_ = v___y_2128_;
v___y_2115_ = v___y_2127_;
v___y_2116_ = v___y_2129_;
v___y_2117_ = v___y_2131_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___x_2133_;
goto v___jp_2106_;
}
else
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_nat_dec_le(v___x_2034_, v___x_2034_);
if (v___x_2135_ == 0)
{
if (v___x_2134_ == 0)
{
lean_dec(v_a_2038_);
v___y_2107_ = v___y_2122_;
v___y_2108_ = v___y_2123_;
v___y_2109_ = v___y_2123_;
v___y_2110_ = v___y_2132_;
v___y_2111_ = v___y_2124_;
v___y_2112_ = v___y_2125_;
v___y_2113_ = v___y_2126_;
v___y_2114_ = v___y_2128_;
v___y_2115_ = v___y_2127_;
v___y_2116_ = v___y_2129_;
v___y_2117_ = v___y_2131_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___x_2133_;
goto v___jp_2106_;
}
else
{
size_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = lean_usize_of_nat(v___x_2034_);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_2038_, v_params_2032_, v___y_2126_, v___x_2136_, v___x_2133_);
lean_dec(v_a_2038_);
v___y_2107_ = v___y_2122_;
v___y_2108_ = v___y_2123_;
v___y_2109_ = v___y_2123_;
v___y_2110_ = v___y_2132_;
v___y_2111_ = v___y_2124_;
v___y_2112_ = v___y_2125_;
v___y_2113_ = v___y_2126_;
v___y_2114_ = v___y_2128_;
v___y_2115_ = v___y_2127_;
v___y_2116_ = v___y_2129_;
v___y_2117_ = v___y_2131_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___x_2137_;
goto v___jp_2106_;
}
}
else
{
size_t v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_usize_of_nat(v___x_2034_);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_2038_, v_params_2032_, v___y_2126_, v___x_2138_, v___x_2133_);
lean_dec(v_a_2038_);
v___y_2107_ = v___y_2122_;
v___y_2108_ = v___y_2123_;
v___y_2109_ = v___y_2123_;
v___y_2110_ = v___y_2132_;
v___y_2111_ = v___y_2124_;
v___y_2112_ = v___y_2125_;
v___y_2113_ = v___y_2126_;
v___y_2114_ = v___y_2128_;
v___y_2115_ = v___y_2127_;
v___y_2116_ = v___y_2129_;
v___y_2117_ = v___y_2131_;
v___y_2118_ = v___y_2130_;
v___y_2119_ = v___x_2139_;
goto v___jp_2106_;
}
}
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v_a_2038_);
v___x_2140_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4));
v___x_2141_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7);
v___x_2142_ = l_Lean_Compiler_LCNF_mkParam(v___y_2123_, v___x_2140_, v___x_2141_, v___x_2044_, v___y_2124_, v___y_2130_, v___y_2125_, v___y_2127_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = lean_unsigned_to_nat(1u);
v___x_2145_ = lean_mk_empty_array_with_capacity(v___x_2144_);
v___x_2146_ = lean_array_push(v___x_2145_, v_a_2143_);
lean_inc(v___y_2127_);
lean_inc_ref(v___y_2125_);
lean_inc(v___y_2130_);
lean_inc_ref(v___y_2124_);
v___x_2147_ = lean_apply_6(v___y_2129_, v___x_2146_, v___y_2124_, v___y_2130_, v___y_2125_, v___y_2127_, lean_box(0));
v___y_2051_ = v___y_2122_;
v___y_2052_ = v___y_2123_;
v___y_2053_ = v___y_2123_;
v___y_2054_ = v___y_2124_;
v___y_2055_ = v___y_2132_;
v___y_2056_ = v___y_2125_;
v___y_2057_ = v___y_2126_;
v___y_2058_ = v___y_2127_;
v___y_2059_ = v___y_2128_;
v___y_2060_ = v___y_2131_;
v___y_2061_ = v___y_2130_;
v___y_2062_ = v___x_2147_;
goto v___jp_2050_;
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec_ref(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2122_);
lean_dec_ref(v_params_2032_);
lean_dec_ref(v_type_2031_);
lean_dec(v_levelParams_2030_);
lean_dec(v_name_2029_);
v_a_2148_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2142_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2142_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
v___jp_2156_:
{
size_t v_sz_2161_; size_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___f_2169_; uint8_t v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
v_sz_2161_ = lean_array_size(v_params_2032_);
v___x_2162_ = ((size_t)0ULL);
lean_inc_ref(v_params_2032_);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_2038_, v_sz_2161_, v___x_2162_, v_params_2032_);
v___x_2164_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9));
lean_inc_n(v_name_2029_, 2);
v___x_2165_ = l_Lean_Name_append(v_name_2029_, v___x_2164_);
v___x_2166_ = lean_box(v___x_2049_);
v___x_2167_ = lean_box(v_safe_2033_);
v___x_2168_ = lean_box(v_recursive_2026_);
lean_inc_ref(v___x_2163_);
lean_inc(v___x_2165_);
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2169_, 0, v_name_2029_);
lean_closure_set(v___f_2169_, 1, v___x_2165_);
lean_closure_set(v___f_2169_, 2, v___x_2163_);
lean_closure_set(v___f_2169_, 3, v___x_2166_);
lean_closure_set(v___f_2169_, 4, v_value_2024_);
lean_closure_set(v___f_2169_, 5, v_code_2028_);
lean_closure_set(v___f_2169_, 6, v___x_2167_);
lean_closure_set(v___f_2169_, 7, v___x_2168_);
lean_closure_set(v___f_2169_, 8, v_inlineAttr_x3f_2027_);
v___x_2170_ = 0;
v___x_2171_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_2172_ = lean_nat_dec_lt(v___x_2035_, v___x_2034_);
if (v___x_2172_ == 0)
{
v___y_2122_ = v___x_2165_;
v___y_2123_ = v___x_2170_;
v___y_2124_ = v___y_2157_;
v___y_2125_ = v___y_2159_;
v___y_2126_ = v___x_2162_;
v___y_2127_ = v___y_2160_;
v___y_2128_ = v_sz_2161_;
v___y_2129_ = v___f_2169_;
v___y_2130_ = v___y_2158_;
v___y_2131_ = v___x_2163_;
v___y_2132_ = v___x_2171_;
goto v___jp_2121_;
}
else
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_nat_dec_le(v___x_2034_, v___x_2034_);
if (v___x_2173_ == 0)
{
if (v___x_2172_ == 0)
{
v___y_2122_ = v___x_2165_;
v___y_2123_ = v___x_2170_;
v___y_2124_ = v___y_2157_;
v___y_2125_ = v___y_2159_;
v___y_2126_ = v___x_2162_;
v___y_2127_ = v___y_2160_;
v___y_2128_ = v_sz_2161_;
v___y_2129_ = v___f_2169_;
v___y_2130_ = v___y_2158_;
v___y_2131_ = v___x_2163_;
v___y_2132_ = v___x_2171_;
goto v___jp_2121_;
}
else
{
size_t v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_usize_of_nat(v___x_2034_);
v___x_2175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_2038_, v_params_2032_, v___x_2162_, v___x_2174_, v___x_2171_);
v___y_2122_ = v___x_2165_;
v___y_2123_ = v___x_2170_;
v___y_2124_ = v___y_2157_;
v___y_2125_ = v___y_2159_;
v___y_2126_ = v___x_2162_;
v___y_2127_ = v___y_2160_;
v___y_2128_ = v_sz_2161_;
v___y_2129_ = v___f_2169_;
v___y_2130_ = v___y_2158_;
v___y_2131_ = v___x_2163_;
v___y_2132_ = v___x_2175_;
goto v___jp_2121_;
}
}
else
{
size_t v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_usize_of_nat(v___x_2034_);
v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_2038_, v_params_2032_, v___x_2162_, v___x_2176_, v___x_2171_);
v___y_2122_ = v___x_2165_;
v___y_2123_ = v___x_2170_;
v___y_2124_ = v___y_2157_;
v___y_2125_ = v___y_2159_;
v___y_2126_ = v___x_2162_;
v___y_2127_ = v___y_2160_;
v___y_2128_ = v_sz_2161_;
v___y_2129_ = v___f_2169_;
v___y_2130_ = v___y_2158_;
v___y_2131_ = v___x_2163_;
v___y_2132_ = v___x_2177_;
goto v___jp_2121_;
}
}
}
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_dec(v_a_2038_);
lean_dec_ref(v_code_2028_);
lean_dec_ref_known(v_value_2024_, 1);
v___x_2206_ = lean_unsigned_to_nat(1u);
v___x_2207_ = lean_mk_empty_array_with_capacity(v___x_2206_);
v___x_2208_ = lean_array_push(v___x_2207_, v_decl_1980_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2208_);
v___x_2210_ = v___x_2040_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref(v_code_2028_);
lean_dec_ref_known(v_value_2024_, 1);
lean_dec_ref(v_decl_1980_);
v_a_2213_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2037_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2037_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2230_; 
v_isSharedCheck_2230_ = !lean_is_exclusive(v_value_2024_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v_value_2024_, 0);
lean_dec(v_unused_2231_);
v___x_2222_ = v_value_2024_;
v_isShared_2223_ = v_isSharedCheck_2230_;
goto v_resetjp_2221_;
}
else
{
lean_dec(v_value_2024_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2230_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2224_ = lean_unsigned_to_nat(1u);
v___x_2225_ = lean_mk_empty_array_with_capacity(v___x_2224_);
v___x_2226_ = lean_array_push(v___x_2225_, v_decl_1980_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2226_);
v___x_2228_ = v___x_2222_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2241_; 
v_isSharedCheck_2241_ = !lean_is_exclusive(v_value_2024_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; 
v_unused_2242_ = lean_ctor_get(v_value_2024_, 0);
lean_dec(v_unused_2242_);
v___x_2233_ = v_value_2024_;
v_isShared_2234_ = v_isSharedCheck_2241_;
goto v_resetjp_2232_;
}
else
{
lean_dec(v_value_2024_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2241_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2235_ = lean_unsigned_to_nat(1u);
v___x_2236_ = lean_mk_empty_array_with_capacity(v___x_2235_);
v___x_2237_ = lean_array_push(v___x_2236_, v_decl_1980_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set_tag(v___x_2233_, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2237_);
v___x_2239_ = v___x_2233_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
v___jp_1986_:
{
if (lean_obj_tag(v___y_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_a_1993_ = lean_ctor_get(v___y_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___y_1992_, 1);
v___x_1994_ = lean_st_ref_get(v___y_1990_);
lean_dec(v___y_1990_);
lean_dec(v___x_1994_);
v___x_1995_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___y_1987_, v___y_1989_, v___y_1991_);
lean_dec_ref(v___y_1989_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2006_; 
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v___x_1995_, 0);
lean_dec(v_unused_2007_);
v___x_1997_ = v___x_1995_;
v_isShared_1998_ = v_isSharedCheck_2006_;
goto v_resetjp_1996_;
}
else
{
lean_dec(v___x_1995_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2006_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
v___x_1999_ = lean_unsigned_to_nat(2u);
v___x_2000_ = lean_mk_empty_array_with_capacity(v___x_1999_);
v___x_2001_ = lean_array_push(v___x_2000_, v___y_1988_);
v___x_2002_ = lean_array_push(v___x_2001_, v_a_1993_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2002_);
v___x_2004_ = v___x_1997_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_a_1993_);
lean_dec_ref(v___y_1988_);
v_a_2008_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1995_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1995_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec_ref(v___y_1988_);
v_a_2016_ = lean_ctor_get(v___y_1992_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___y_1992_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___y_1992_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___y_1992_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_reduceArity_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1980_ = stack[0].m_obj;
lean_object* v_a_1981_ = stack[1].m_obj;
lean_object* v_a_1982_ = stack[2].m_obj;
lean_object* v_a_1983_ = stack[3].m_obj;
lean_object* v_a_1984_ = stack[4].m_obj;
lean_object* v_res_2243_;
v_res_2243_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v_decl_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
stack->m_obj
 = v_res_2243_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object* v_decl_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v_decl_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
return v_res_2250_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* v_00_u03b2_2251_, lean_object* v_m_2252_, lean_object* v_a_2253_){
_start:
{
uint8_t v___x_2254_; 
v___x_2254_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_2252_, v_a_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2252_ = stack[1].m_obj;
lean_object* v_a_2253_ = stack[2].m_obj;
uint8_t v_res_2255_;
v_res_2255_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_box(0), v_m_2252_, v_a_2253_);
stack->m_num = v_res_2255_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* v_00_u03b2_2256_, lean_object* v_m_2257_, lean_object* v_a_2258_){
_start:
{
uint8_t v_res_2259_; lean_object* v_r_2260_; 
v_res_2259_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(v_00_u03b2_2256_, v_m_2257_, v_a_2258_);
lean_dec(v_a_2258_);
lean_dec_ref(v_m_2257_);
v_r_2260_ = lean_box(v_res_2259_);
return v_r_2260_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* v_as_2261_, size_t v_sz_2262_, size_t v_i_2263_, lean_object* v_b_2264_, uint8_t v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_2261_, v_sz_2262_, v_i_2263_, v_b_2264_);
return v___x_2272_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2261_ = stack[0].m_obj;
size_t v_sz_2262_ = stack[1].m_num;
size_t v_i_2263_ = stack[2].m_num;
lean_object* v_b_2264_ = stack[3].m_obj;
uint8_t v___y_2265_ = stack[4].m_num;
lean_object* v___y_2266_ = stack[5].m_obj;
lean_object* v___y_2267_ = stack[6].m_obj;
lean_object* v___y_2268_ = stack[7].m_obj;
lean_object* v___y_2269_ = stack[8].m_obj;
lean_object* v___y_2270_ = stack[9].m_obj;
lean_object* v_res_2273_;
v_res_2273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_2261_, v_sz_2262_, v_i_2263_, v_b_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
stack->m_obj
 = v_res_2273_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* v_as_2274_, lean_object* v_sz_2275_, lean_object* v_i_2276_, lean_object* v_b_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
size_t v_sz_boxed_2285_; size_t v_i_boxed_2286_; uint8_t v___y_13758__boxed_2287_; lean_object* v_res_2288_; 
v_sz_boxed_2285_ = lean_unbox_usize(v_sz_2275_);
lean_dec(v_sz_2275_);
v_i_boxed_2286_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v___y_13758__boxed_2287_ = lean_unbox(v___y_2278_);
v_res_2288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_2274_, v_sz_boxed_2285_, v_i_boxed_2286_, v_b_2277_, v___y_13758__boxed_2287_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v_as_2274_);
return v_res_2288_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* v_as_2289_, size_t v_i_2290_, size_t v_stop_2291_, lean_object* v_b_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_a_2299_; uint8_t v___x_2303_; 
v___x_2303_ = lean_usize_dec_eq(v_i_2290_, v_stop_2291_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_array_uget_borrowed(v_as_2289_, v_i_2290_);
lean_inc(v___x_2304_);
v___x_2305_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v___x_2304_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = l_Array_append___redArg(v_b_2292_, v_a_2306_);
lean_dec(v_a_2306_);
v_a_2299_ = v___x_2307_;
goto v___jp_2298_;
}
else
{
lean_dec_ref(v_b_2292_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2308_; 
v_a_2308_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2305_, 1);
v_a_2299_ = v_a_2308_;
goto v___jp_2298_;
}
else
{
return v___x_2305_;
}
}
}
else
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_b_2292_);
return v___x_2309_;
}
v___jp_2298_:
{
size_t v___x_2300_; size_t v___x_2301_; 
v___x_2300_ = ((size_t)1ULL);
v___x_2301_ = lean_usize_add(v_i_2290_, v___x_2300_);
v_i_2290_ = v___x_2301_;
v_b_2292_ = v_a_2299_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2289_ = stack[0].m_obj;
size_t v_i_2290_ = stack[1].m_num;
size_t v_stop_2291_ = stack[2].m_num;
lean_object* v_b_2292_ = stack[3].m_obj;
lean_object* v___y_2293_ = stack[4].m_obj;
lean_object* v___y_2294_ = stack[5].m_obj;
lean_object* v___y_2295_ = stack[6].m_obj;
lean_object* v___y_2296_ = stack[7].m_obj;
lean_object* v_res_2310_;
v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_2289_, v_i_2290_, v_stop_2291_, v_b_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
stack->m_obj
 = v_res_2310_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* v_as_2311_, lean_object* v_i_2312_, lean_object* v_stop_2313_, lean_object* v_b_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
size_t v_i_boxed_2320_; size_t v_stop_boxed_2321_; lean_object* v_res_2322_; 
v_i_boxed_2320_ = lean_unbox_usize(v_i_2312_);
lean_dec(v_i_2312_);
v_stop_boxed_2321_ = lean_unbox_usize(v_stop_2313_);
lean_dec(v_stop_2313_);
v_res_2322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_2311_, v_i_boxed_2320_, v_stop_boxed_2321_, v_b_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec_ref(v_as_2311_);
return v_res_2322_;
}
}
lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* v___x_2323_, lean_object* v_decls_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2330_ = lean_mk_empty_array_with_capacity(v___x_2323_);
v___x_2331_ = lean_array_get_size(v_decls_2324_);
v___x_2332_ = lean_nat_dec_lt(v___x_2323_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2330_);
return v___x_2333_;
}
else
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_nat_dec_le(v___x_2331_, v___x_2331_);
if (v___x_2334_ == 0)
{
if (v___x_2332_ == 0)
{
lean_object* v___x_2335_; 
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2330_);
return v___x_2335_;
}
else
{
size_t v___x_2336_; size_t v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = ((size_t)0ULL);
v___x_2337_ = lean_usize_of_nat(v___x_2331_);
v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2324_, v___x_2336_, v___x_2337_, v___x_2330_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
return v___x_2338_;
}
}
else
{
size_t v___x_2339_; size_t v___x_2340_; lean_object* v___x_2341_; 
v___x_2339_ = ((size_t)0ULL);
v___x_2340_ = lean_usize_of_nat(v___x_2331_);
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2324_, v___x_2339_, v___x_2340_, v___x_2330_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
return v___x_2341_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_reduceArity___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2323_ = stack[0].m_obj;
lean_object* v_decls_2324_ = stack[1].m_obj;
lean_object* v___y_2325_ = stack[2].m_obj;
lean_object* v___y_2326_ = stack[3].m_obj;
lean_object* v___y_2327_ = stack[4].m_obj;
lean_object* v___y_2328_ = stack[5].m_obj;
lean_object* v_res_2342_;
v_res_2342_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(v___x_2323_, v_decls_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
stack->m_obj
 = v_res_2342_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* v___x_2343_, lean_object* v_decls_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(v___x_2343_, v_decls_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec_ref(v_decls_2344_);
lean_dec(v___x_2343_);
return v_res_2350_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = lean_unsigned_to_nat(2803462840u);
v___x_2414_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2415_ = l_Lean_Name_num___override(v___x_2414_, v___x_2413_);
return v___x_2415_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2418_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2419_ = l_Lean_Name_str___override(v___x_2418_, v___x_2417_);
return v___x_2419_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2422_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2423_ = l_Lean_Name_str___override(v___x_2422_, v___x_2421_);
return v___x_2423_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2424_ = lean_unsigned_to_nat(2u);
v___x_2425_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2426_ = l_Lean_Name_num___override(v___x_2425_, v___x_2424_);
return v___x_2426_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2428_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_2429_ = 1;
v___x_2430_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2431_ = l_Lean_registerTraceClass(v___x_2428_, v___x_2429_, v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2432_;
v_res_2432_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2432_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
return v_res_2434_;
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
