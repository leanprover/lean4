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
case 2:
{
lean_object* v_struct_367_; lean_object* v___x_368_; 
v_struct_367_ = lean_ctor_get(v_e_359_, 2);
lean_inc(v_struct_367_);
lean_dec_ref_known(v_e_359_, 3);
v___x_368_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_struct_367_, v_a_360_, v_a_361_);
return v___x_368_;
}
case 3:
{
lean_object* v_decl_369_; lean_object* v_toSignature_370_; lean_object* v_declName_371_; lean_object* v_args_372_; lean_object* v_name_373_; lean_object* v_params_374_; lean_object* v___y_376_; lean_object* v_lower_377_; lean_object* v_upper_378_; uint8_t v___x_389_; 
v_decl_369_ = lean_ctor_get(v_a_360_, 0);
v_toSignature_370_ = lean_ctor_get(v_decl_369_, 0);
v_declName_371_ = lean_ctor_get(v_e_359_, 0);
lean_inc(v_declName_371_);
v_args_372_ = lean_ctor_get(v_e_359_, 2);
lean_inc_ref(v_args_372_);
lean_dec_ref_known(v_e_359_, 3);
v_name_373_ = lean_ctor_get(v_toSignature_370_, 0);
v_params_374_ = lean_ctor_get(v_toSignature_370_, 3);
v___x_389_ = lean_name_eq(v_declName_371_, v_name_373_);
lean_dec(v_declName_371_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_array_get_size(v_args_372_);
v___x_392_ = lean_box(0);
v___x_393_ = lean_nat_dec_lt(v___x_390_, v___x_391_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec_ref(v_args_372_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = lean_nat_dec_le(v___x_391_, v___x_391_);
if (v___x_395_ == 0)
{
if (v___x_393_ == 0)
{
lean_object* v___x_396_; 
lean_dec_ref(v_args_372_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_392_);
return v___x_396_;
}
else
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_391_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_372_, v___x_397_, v___x_398_, v___x_392_, v_a_360_, v_a_361_);
lean_dec_ref(v_args_372_);
return v___x_399_;
}
}
else
{
size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_400_ = ((size_t)0ULL);
v___x_401_ = lean_usize_of_nat(v___x_391_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_372_, v___x_400_, v___x_401_, v___x_392_, v_a_360_, v_a_361_);
lean_dec_ref(v_args_372_);
return v___x_402_;
}
}
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; size_t v_sz_406_; size_t v___x_407_; lean_object* v___x_408_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_array_get_size(v_args_372_);
lean_inc_ref(v_args_372_);
v___x_405_ = l_Array_toSubarray___redArg(v_args_372_, v___x_403_, v___x_404_);
v_sz_406_ = lean_array_size(v_params_374_);
v___x_407_ = ((size_t)0ULL);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_params_374_, v_sz_406_, v___x_407_, v___x_405_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_lower_410_; lean_object* v_upper_411_; lean_object* v___x_417_; uint8_t v___x_418_; 
lean_dec_ref_known(v___x_408_, 1);
v___x_417_ = lean_array_get_size(v_params_374_);
v___x_418_ = lean_nat_dec_le(v___x_417_, v___x_403_);
if (v___x_418_ == 0)
{
v_lower_410_ = v___x_417_;
v_upper_411_ = v___x_404_;
goto v___jp_409_;
}
else
{
v_lower_410_ = v___x_403_;
v_upper_411_ = v___x_404_;
goto v___jp_409_;
}
v___jp_409_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = l_Array_toSubarray___redArg(v_args_372_, v_lower_410_, v_upper_411_);
v___x_413_ = lean_box(0);
v___x_414_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v___x_412_, v___x_413_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v___x_415_; uint8_t v___x_416_; 
lean_dec_ref_known(v___x_414_, 1);
v___x_415_ = lean_array_get_size(v_params_374_);
v___x_416_ = lean_nat_dec_le(v___x_404_, v___x_403_);
if (v___x_416_ == 0)
{
v___y_376_ = v___x_413_;
v_lower_377_ = v___x_404_;
v_upper_378_ = v___x_415_;
goto v___jp_375_;
}
else
{
v___y_376_ = v___x_413_;
v_lower_377_ = v___x_403_;
v_upper_378_ = v___x_415_;
goto v___jp_375_;
}
}
else
{
return v___x_414_;
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_args_372_);
v_a_419_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_408_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_408_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
v___jp_375_:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
lean_inc_ref(v_params_374_);
v___x_379_ = l_Array_toSubarray___redArg(v_params_374_, v_lower_377_, v_upper_378_);
v___x_380_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v___x_379_, v___y_376_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v___x_380_, 0);
lean_dec(v_unused_388_);
v___x_382_ = v___x_380_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_dec(v___x_380_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___y_376_);
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___y_376_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
else
{
return v___x_380_;
}
}
}
case 4:
{
lean_object* v_fvarId_427_; lean_object* v_args_428_; lean_object* v___x_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_450_; 
v_fvarId_427_ = lean_ctor_get(v_e_359_, 0);
lean_inc(v_fvarId_427_);
v_args_428_ = lean_ctor_get(v_e_359_, 1);
lean_inc_ref(v_args_428_);
lean_dec_ref_known(v_e_359_, 2);
v___x_429_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_427_, v_a_360_, v_a_361_);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v___x_429_, 0);
lean_dec(v_unused_451_);
v___x_431_ = v___x_429_;
v_isShared_432_ = v_isSharedCheck_450_;
goto v_resetjp_430_;
}
else
{
lean_dec(v___x_429_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_450_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_array_get_size(v_args_428_);
v___x_435_ = lean_box(0);
v___x_436_ = lean_nat_dec_lt(v___x_433_, v___x_434_);
if (v___x_436_ == 0)
{
lean_object* v___x_438_; 
lean_dec_ref(v_args_428_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_435_);
v___x_438_ = v___x_431_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_435_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
else
{
uint8_t v___x_440_; 
v___x_440_ = lean_nat_dec_le(v___x_434_, v___x_434_);
if (v___x_440_ == 0)
{
if (v___x_436_ == 0)
{
lean_object* v___x_442_; 
lean_dec_ref(v_args_428_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_435_);
v___x_442_ = v___x_431_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_435_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
size_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; 
lean_del_object(v___x_431_);
v___x_444_ = ((size_t)0ULL);
v___x_445_ = lean_usize_of_nat(v___x_434_);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_428_, v___x_444_, v___x_445_, v___x_435_, v_a_360_, v_a_361_);
lean_dec_ref(v_args_428_);
return v___x_446_;
}
}
else
{
size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
lean_del_object(v___x_431_);
v___x_447_ = ((size_t)0ULL);
v___x_448_ = lean_usize_of_nat(v___x_434_);
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_428_, v___x_447_, v___x_448_, v___x_435_, v_a_360_, v_a_361_);
lean_dec_ref(v_args_428_);
return v___x_449_;
}
}
}
}
default: 
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec(v_e_359_);
v___x_452_ = lean_box(0);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object* v_e_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_e_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object* v_as_463_, size_t v_i_464_, size_t v_stop_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_463_, v_i_464_, v_stop_465_, v_b_466_, v___y_467_, v___y_468_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object* v_as_475_, lean_object* v_i_476_, lean_object* v_stop_477_, lean_object* v_b_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
size_t v_i_boxed_486_; size_t v_stop_boxed_487_; lean_object* v_res_488_; 
v_i_boxed_486_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_stop_boxed_487_ = lean_unbox_usize(v_stop_477_);
lean_dec(v_stop_477_);
v_res_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(v_as_475_, v_i_boxed_486_, v_stop_boxed_487_, v_b_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v_as_475_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object* v_as_489_, size_t v_sz_490_, size_t v_i_491_, lean_object* v_b_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_489_, v_sz_490_, v_i_491_, v_b_492_, v___y_493_, v___y_494_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object* v_as_501_, lean_object* v_sz_502_, lean_object* v_i_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
size_t v_sz_boxed_512_; size_t v_i_boxed_513_; lean_object* v_res_514_; 
v_sz_boxed_512_ = lean_unbox_usize(v_sz_502_);
lean_dec(v_sz_502_);
v_i_boxed_513_ = lean_unbox_usize(v_i_503_);
lean_dec(v_i_503_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(v_as_501_, v_sz_boxed_512_, v_i_boxed_513_, v_b_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec_ref(v_as_501_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object* v_inst_515_, lean_object* v_R_516_, lean_object* v_a_517_, lean_object* v_b_518_, lean_object* v_c_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_517_, v_b_518_, v___y_520_, v___y_521_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object* v_inst_528_, lean_object* v_R_529_, lean_object* v_a_530_, lean_object* v_b_531_, lean_object* v_c_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(v_inst_528_, v_R_529_, v_a_530_, v_b_531_, v_c_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object* v_inst_541_, lean_object* v_R_542_, lean_object* v_a_543_, lean_object* v_b_544_, lean_object* v_c_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_543_, v_b_544_, v___y_546_, v___y_547_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object* v_inst_554_, lean_object* v_R_555_, lean_object* v_a_556_, lean_object* v_b_557_, lean_object* v_c_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(v_inst_554_, v_R_555_, v_a_556_, v_b_557_, v_c_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object* v_code_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_decl_576_; lean_object* v_k_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; 
switch(lean_obj_tag(v_code_567_))
{
case 0:
{
lean_object* v_decl_587_; lean_object* v_k_588_; lean_object* v_value_589_; lean_object* v___x_590_; 
v_decl_587_ = lean_ctor_get(v_code_567_, 0);
lean_inc_ref(v_decl_587_);
v_k_588_ = lean_ctor_get(v_code_567_, 1);
lean_inc_ref(v_k_588_);
lean_dec_ref_known(v_code_567_, 2);
v_value_589_ = lean_ctor_get(v_decl_587_, 3);
lean_inc(v_value_589_);
lean_dec_ref(v_decl_587_);
v___x_590_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_value_589_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_dec_ref_known(v___x_590_, 1);
v_code_567_ = v_k_588_;
goto _start;
}
else
{
lean_dec_ref(v_k_588_);
return v___x_590_;
}
}
case 3:
{
lean_object* v_args_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_args_592_ = lean_ctor_get(v_code_567_, 1);
lean_inc_ref(v_args_592_);
lean_dec_ref_known(v_code_567_, 2);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = lean_array_get_size(v_args_592_);
v___x_595_ = lean_box(0);
v___x_596_ = lean_nat_dec_lt(v___x_593_, v___x_594_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
lean_dec_ref(v_args_592_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
return v___x_597_;
}
else
{
uint8_t v___x_598_; 
v___x_598_ = lean_nat_dec_le(v___x_594_, v___x_594_);
if (v___x_598_ == 0)
{
if (v___x_596_ == 0)
{
lean_object* v___x_599_; 
lean_dec_ref(v_args_592_);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_595_);
return v___x_599_;
}
else
{
size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v___x_600_ = ((size_t)0ULL);
v___x_601_ = lean_usize_of_nat(v___x_594_);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_592_, v___x_600_, v___x_601_, v___x_595_, v_a_568_, v_a_569_);
lean_dec_ref(v_args_592_);
return v___x_602_;
}
}
else
{
size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; 
v___x_603_ = ((size_t)0ULL);
v___x_604_ = lean_usize_of_nat(v___x_594_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_592_, v___x_603_, v___x_604_, v___x_595_, v_a_568_, v_a_569_);
lean_dec_ref(v_args_592_);
return v___x_605_;
}
}
}
case 4:
{
lean_object* v_cases_606_; lean_object* v_discr_607_; lean_object* v_alts_608_; lean_object* v___x_609_; 
v_cases_606_ = lean_ctor_get(v_code_567_, 0);
lean_inc_ref(v_cases_606_);
lean_dec_ref_known(v_code_567_, 1);
v_discr_607_ = lean_ctor_get(v_cases_606_, 2);
lean_inc(v_discr_607_);
v_alts_608_ = lean_ctor_get(v_cases_606_, 3);
lean_inc_ref(v_alts_608_);
lean_dec_ref(v_cases_606_);
v___x_609_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_discr_607_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_630_; 
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; 
v_unused_631_ = lean_ctor_get(v___x_609_, 0);
lean_dec(v_unused_631_);
v___x_611_ = v___x_609_;
v_isShared_612_ = v_isSharedCheck_630_;
goto v_resetjp_610_;
}
else
{
lean_dec(v___x_609_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_630_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_array_get_size(v_alts_608_);
v___x_615_ = lean_box(0);
v___x_616_ = lean_nat_dec_lt(v___x_613_, v___x_614_);
if (v___x_616_ == 0)
{
lean_object* v___x_618_; 
lean_dec_ref(v_alts_608_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_615_);
v___x_618_ = v___x_611_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_615_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
uint8_t v___x_620_; 
v___x_620_ = lean_nat_dec_le(v___x_614_, v___x_614_);
if (v___x_620_ == 0)
{
if (v___x_616_ == 0)
{
lean_object* v___x_622_; 
lean_dec_ref(v_alts_608_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_615_);
v___x_622_ = v___x_611_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_615_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
else
{
size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; 
lean_del_object(v___x_611_);
v___x_624_ = ((size_t)0ULL);
v___x_625_ = lean_usize_of_nat(v___x_614_);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_608_, v___x_624_, v___x_625_, v___x_615_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
lean_dec_ref(v_alts_608_);
return v___x_626_;
}
}
else
{
size_t v___x_627_; size_t v___x_628_; lean_object* v___x_629_; 
lean_del_object(v___x_611_);
v___x_627_ = ((size_t)0ULL);
v___x_628_ = lean_usize_of_nat(v___x_614_);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_608_, v___x_627_, v___x_628_, v___x_615_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
lean_dec_ref(v_alts_608_);
return v___x_629_;
}
}
}
}
else
{
lean_dec_ref(v_alts_608_);
return v___x_609_;
}
}
case 5:
{
lean_object* v_fvarId_632_; lean_object* v___x_633_; 
v_fvarId_632_ = lean_ctor_get(v_code_567_, 0);
lean_inc(v_fvarId_632_);
lean_dec_ref_known(v_code_567_, 1);
v___x_633_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_632_, v_a_568_, v_a_569_);
return v___x_633_;
}
case 6:
{
lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_641_; 
v_isSharedCheck_641_ = !lean_is_exclusive(v_code_567_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v_code_567_, 0);
lean_dec(v_unused_642_);
v___x_635_ = v_code_567_;
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
else
{
lean_dec(v_code_567_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_641_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_box(0);
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 0);
lean_ctor_set(v___x_635_, 0, v___x_637_);
v___x_639_ = v___x_635_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
default: 
{
lean_object* v_decl_643_; lean_object* v_k_644_; 
v_decl_643_ = lean_ctor_get(v_code_567_, 0);
lean_inc_ref(v_decl_643_);
v_k_644_ = lean_ctor_get(v_code_567_, 1);
lean_inc_ref(v_k_644_);
lean_dec_ref(v_code_567_);
v_decl_576_ = v_decl_643_;
v_k_577_ = v_k_644_;
v___y_578_ = v_a_568_;
v___y_579_ = v_a_569_;
v___y_580_ = v_a_570_;
v___y_581_ = v_a_571_;
v___y_582_ = v_a_572_;
v___y_583_ = v_a_573_;
goto v___jp_575_;
}
}
v___jp_575_:
{
lean_object* v_value_584_; lean_object* v___x_585_; 
v_value_584_ = lean_ctor_get(v_decl_576_, 4);
lean_inc_ref(v_value_584_);
lean_dec_ref(v_decl_576_);
v___x_585_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_value_584_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_dec_ref_known(v___x_585_, 1);
v_code_567_ = v_k_577_;
v_a_568_ = v___y_578_;
v_a_569_ = v___y_579_;
v_a_570_ = v___y_580_;
v_a_571_ = v___y_581_;
v_a_572_ = v___y_582_;
v_a_573_ = v___y_583_;
goto _start;
}
else
{
lean_dec_ref(v_k_577_);
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object* v_as_645_, size_t v_i_646_, size_t v_stop_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___y_657_; uint8_t v___x_663_; 
v___x_663_ = lean_usize_dec_eq(v_i_646_, v_stop_647_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = lean_array_uget_borrowed(v_as_645_, v_i_646_);
switch(lean_obj_tag(v___x_664_))
{
case 0:
{
lean_object* v_code_665_; 
v_code_665_ = lean_ctor_get(v___x_664_, 2);
lean_inc_ref(v_code_665_);
v___y_657_ = v_code_665_;
goto v___jp_656_;
}
case 1:
{
lean_object* v_code_666_; 
v_code_666_ = lean_ctor_get(v___x_664_, 1);
lean_inc_ref(v_code_666_);
v___y_657_ = v_code_666_;
goto v___jp_656_;
}
default: 
{
lean_object* v_code_667_; 
v_code_667_ = lean_ctor_get(v___x_664_, 0);
lean_inc_ref(v_code_667_);
v___y_657_ = v_code_667_;
goto v___jp_656_;
}
}
}
else
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v_b_648_);
return v___x_668_;
}
v___jp_656_:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Compiler_LCNF_FindUsed_visit(v___y_657_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; size_t v___x_660_; size_t v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = ((size_t)1ULL);
v___x_661_ = lean_usize_add(v_i_646_, v___x_660_);
v_i_646_ = v___x_661_;
v_b_648_ = v_a_659_;
goto _start;
}
else
{
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object* v_as_669_, lean_object* v_i_670_, lean_object* v_stop_671_, lean_object* v_b_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
size_t v_i_boxed_680_; size_t v_stop_boxed_681_; lean_object* v_res_682_; 
v_i_boxed_680_ = lean_unbox_usize(v_i_670_);
lean_dec(v_i_670_);
v_stop_boxed_681_ = lean_unbox_usize(v_stop_671_);
lean_dec(v_stop_671_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_as_669_, v_i_boxed_680_, v_stop_boxed_681_, v_b_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec_ref(v_as_669_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object* v_code_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_code_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(lean_object* v_f_692_, lean_object* v_v_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
if (lean_obj_tag(v_v_693_) == 0)
{
lean_object* v_code_701_; lean_object* v___x_702_; 
v_code_701_ = lean_ctor_get(v_v_693_, 0);
lean_inc_ref(v_code_701_);
lean_dec_ref_known(v_v_693_, 1);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v___y_697_);
lean_inc_ref(v___y_696_);
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
v___x_702_ = lean_apply_8(v_f_692_, v_code_701_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, lean_box(0));
return v___x_702_;
}
else
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v_f_692_);
v_isSharedCheck_710_ = !lean_is_exclusive(v_v_693_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v_v_693_, 0);
lean_dec(v_unused_711_);
v___x_704_ = v_v_693_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_v_693_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = lean_box(0);
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 0);
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg___boxed(lean_object* v_f_712_, lean_object* v_v_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_712_, v_v_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(uint8_t v_pu_722_, lean_object* v_f_723_, lean_object* v_v_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_723_, v_v_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___boxed(lean_object* v_pu_733_, lean_object* v_f_734_, lean_object* v_v_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
uint8_t v_pu_boxed_743_; lean_object* v_res_744_; 
v_pu_boxed_743_ = lean_unbox(v_pu_733_);
v_res_744_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(v_pu_boxed_743_, v_f_734_, v_v_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object* v_as_745_, size_t v_i_746_, size_t v_stop_747_, lean_object* v_b_748_){
_start:
{
uint8_t v___x_749_; 
v___x_749_ = lean_usize_dec_eq(v_i_746_, v_stop_747_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v_fvarId_751_; lean_object* v___x_752_; size_t v___x_753_; size_t v___x_754_; 
v___x_750_ = lean_array_uget_borrowed(v_as_745_, v_i_746_);
v_fvarId_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_fvarId_751_);
v___x_752_ = l_Lean_FVarIdSet_insert(v_b_748_, v_fvarId_751_);
v___x_753_ = ((size_t)1ULL);
v___x_754_ = lean_usize_add(v_i_746_, v___x_753_);
v_i_746_ = v___x_754_;
v_b_748_ = v___x_752_;
goto _start;
}
else
{
return v_b_748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object* v_as_756_, lean_object* v_i_757_, lean_object* v_stop_758_, lean_object* v_b_759_){
_start:
{
size_t v_i_boxed_760_; size_t v_stop_boxed_761_; lean_object* v_res_762_; 
v_i_boxed_760_ = lean_unbox_usize(v_i_757_);
lean_dec(v_i_757_);
v_stop_boxed_761_ = lean_unbox_usize(v_stop_758_);
lean_dec(v_stop_758_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_as_756_, v_i_boxed_760_, v_stop_boxed_761_, v_b_759_);
lean_dec_ref(v_as_756_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object* v_decl_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_toSignature_770_; lean_object* v_value_771_; lean_object* v_params_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___y_776_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v_toSignature_770_ = lean_ctor_get(v_decl_764_, 0);
v_value_771_ = lean_ctor_get(v_decl_764_, 1);
lean_inc_ref(v_value_771_);
v_params_772_ = lean_ctor_get(v_toSignature_770_, 3);
v___x_773_ = lean_box(1);
v___x_774_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_array_get_size(v_params_772_);
v___x_800_ = lean_nat_dec_lt(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
v___y_776_ = v___x_773_;
goto v___jp_775_;
}
else
{
uint8_t v___x_801_; 
v___x_801_ = lean_nat_dec_le(v___x_799_, v___x_799_);
if (v___x_801_ == 0)
{
if (v___x_800_ == 0)
{
v___y_776_ = v___x_773_;
goto v___jp_775_;
}
else
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v___x_802_ = ((size_t)0ULL);
v___x_803_ = lean_usize_of_nat(v___x_799_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_772_, v___x_802_, v___x_803_, v___x_773_);
v___y_776_ = v___x_804_;
goto v___jp_775_;
}
}
else
{
size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
v___x_805_ = ((size_t)0ULL);
v___x_806_ = lean_usize_of_nat(v___x_799_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_772_, v___x_805_, v___x_806_, v___x_773_);
v___y_776_ = v___x_807_;
goto v___jp_775_;
}
}
v___jp_775_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_777_ = ((lean_object*)(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0));
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_decl_764_);
lean_ctor_set(v___x_778_, 1, v___y_776_);
v___x_779_ = lean_st_mk_ref(v___x_774_);
v___x_780_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v___x_777_, v_value_771_, v___x_778_, v___x_779_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
lean_dec_ref_known(v___x_778_, 2);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_780_, 0);
lean_dec(v_unused_789_);
v___x_782_ = v___x_780_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_dec(v___x_780_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_st_ref_get(v___x_779_);
lean_dec(v___x_779_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v___x_779_);
v_a_790_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_780_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_780_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(lean_object* v_decl_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
return v_res_814_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0(void){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object* v_msg_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0);
v___x_818_ = lean_panic_fn_borrowed(v___x_817_, v_msg_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(lean_object* v_args_819_, lean_object* v_upperBound_820_, lean_object* v___x_821_, lean_object* v_a_822_, lean_object* v_b_823_){
_start:
{
lean_object* v_a_826_; uint8_t v___x_833_; 
v___x_833_ = lean_nat_dec_lt(v_a_822_, v_upperBound_820_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v_a_822_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v_b_823_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_array_get_size(v___x_821_);
v___x_836_ = lean_nat_dec_lt(v_a_822_, v___x_835_);
if (v___x_836_ == 0)
{
goto v___jp_830_;
}
else
{
lean_object* v___x_837_; uint8_t v___x_838_; 
v___x_837_ = lean_array_fget_borrowed(v___x_821_, v_a_822_);
v___x_838_ = lean_unbox(v___x_837_);
if (v___x_838_ == 0)
{
v_a_826_ = v_b_823_;
goto v___jp_825_;
}
else
{
goto v___jp_830_;
}
}
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_nat_add(v_a_822_, v___x_827_);
lean_dec(v_a_822_);
v_a_822_ = v___x_828_;
v_b_823_ = v_a_826_;
goto _start;
}
v___jp_830_:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_array_fget_borrowed(v_args_819_, v_a_822_);
lean_inc(v___x_831_);
v___x_832_ = lean_array_push(v_b_823_, v___x_831_);
v_a_826_ = v___x_832_;
goto v___jp_825_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(lean_object* v_args_839_, lean_object* v_upperBound_840_, lean_object* v___x_841_, lean_object* v_a_842_, lean_object* v_b_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_839_, v_upperBound_840_, v___x_841_, v_a_842_, v_b_843_);
lean_dec_ref(v___x_841_);
lean_dec(v_upperBound_840_);
lean_dec_ref(v_args_839_);
return v_res_845_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_849_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2));
v___x_850_ = lean_unsigned_to_nat(9u);
v___x_851_ = lean_unsigned_to_nat(650u);
v___x_852_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1));
v___x_853_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0));
v___x_854_ = l_mkPanicMessageWithDecl(v___x_853_, v___x_852_, v___x_851_, v___x_850_, v___x_849_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* v_code_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_decl_869_; lean_object* v_k_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; 
switch(lean_obj_tag(v_code_861_))
{
case 0:
{
lean_object* v_decl_983_; lean_object* v_k_984_; lean_object* v_argsNew_986_; lean_object* v___y_987_; lean_object* v_auxDeclName_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v_value_1045_; 
v_decl_983_ = lean_ctor_get(v_code_861_, 0);
v_k_984_ = lean_ctor_get(v_code_861_, 1);
v_value_1045_ = lean_ctor_get(v_decl_983_, 3);
if (lean_obj_tag(v_value_1045_) == 3)
{
lean_object* v_declName_1046_; lean_object* v_args_1047_; lean_object* v_declName_1048_; lean_object* v_auxDeclName_1049_; lean_object* v_paramMask_1050_; uint8_t v_allUnused_1051_; uint8_t v___x_1052_; 
v_declName_1046_ = lean_ctor_get(v_value_1045_, 0);
v_args_1047_ = lean_ctor_get(v_value_1045_, 2);
v_declName_1048_ = lean_ctor_get(v_a_862_, 0);
v_auxDeclName_1049_ = lean_ctor_get(v_a_862_, 1);
v_paramMask_1050_ = lean_ctor_get(v_a_862_, 2);
v_allUnused_1051_ = lean_ctor_get_uint8(v_a_862_, sizeof(void*)*3);
v___x_1052_ = lean_name_eq(v_declName_1046_, v_declName_1048_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_inc_ref(v_k_984_);
v___x_1053_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_984_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1090_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1090_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1090_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
size_t v___x_1058_; size_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1058_ = lean_ptr_addr(v_k_984_);
v___x_1059_ = lean_ptr_addr(v_a_1054_);
v___x_1060_ = lean_usize_dec_eq(v___x_1058_, v___x_1059_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1070_; 
lean_inc_ref(v_decl_983_);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; lean_object* v_unused_1072_; 
v_unused_1071_ = lean_ctor_get(v_code_861_, 1);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_1072_);
v___x_1062_ = v_code_861_;
v_isShared_1063_ = v_isSharedCheck_1070_;
goto v_resetjp_1061_;
}
else
{
lean_dec(v_code_861_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1070_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v_a_1054_);
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_decl_983_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_a_1054_);
v___x_1065_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1065_);
v___x_1067_ = v___x_1056_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
size_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = lean_ptr_addr(v_decl_983_);
v___x_1074_ = lean_usize_dec_eq(v___x_1073_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1084_; 
lean_inc_ref(v_decl_983_);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; lean_object* v_unused_1086_; 
v_unused_1085_ = lean_ctor_get(v_code_861_, 1);
lean_dec(v_unused_1085_);
v_unused_1086_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_1086_);
v___x_1076_ = v_code_861_;
v_isShared_1077_ = v_isSharedCheck_1084_;
goto v_resetjp_1075_;
}
else
{
lean_dec(v_code_861_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1084_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v_a_1054_);
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_decl_983_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_a_1054_);
v___x_1079_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1081_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1079_);
v___x_1081_ = v___x_1056_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v___x_1088_; 
lean_dec(v_a_1054_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v_code_861_);
v___x_1088_ = v___x_1056_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_code_861_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_861_, 2);
return v___x_1053_;
}
}
else
{
if (v_allUnused_1051_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1091_ = lean_array_get_size(v_args_1047_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_1094_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1047_, v___x_1091_, v_paramMask_1050_, v___x_1092_, v___x_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v_argsNew_986_ = v_a_1095_;
v___y_987_ = v_a_862_;
v_auxDeclName_988_ = v_auxDeclName_1049_;
v___y_989_ = v_a_863_;
v___y_990_ = v_a_864_;
v___y_991_ = v_a_865_;
v___y_992_ = v_a_866_;
goto v___jp_985_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref_known(v_code_861_, 2);
v_a_1096_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1094_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1094_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1104_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5));
v___x_1105_ = lean_array_get_size(v_paramMask_1050_);
v___x_1106_ = lean_array_get_size(v_args_1047_);
v___x_1107_ = l_Array_extract___redArg(v_args_1047_, v___x_1105_, v___x_1106_);
v___x_1108_ = l_Array_append___redArg(v___x_1104_, v___x_1107_);
lean_dec_ref(v___x_1107_);
v_argsNew_986_ = v___x_1108_;
v___y_987_ = v_a_862_;
v_auxDeclName_988_ = v_auxDeclName_1049_;
v___y_989_ = v_a_863_;
v___y_990_ = v_a_864_;
v___y_991_ = v_a_865_;
v___y_992_ = v_a_866_;
goto v___jp_985_;
}
}
}
else
{
lean_object* v___x_1109_; 
lean_inc_ref(v_k_984_);
v___x_1109_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_984_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1146_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1146_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1146_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
size_t v___x_1114_; size_t v___x_1115_; uint8_t v___x_1116_; 
v___x_1114_ = lean_ptr_addr(v_k_984_);
v___x_1115_ = lean_ptr_addr(v_a_1110_);
v___x_1116_ = lean_usize_dec_eq(v___x_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1126_; 
lean_inc_ref(v_decl_983_);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; lean_object* v_unused_1128_; 
v_unused_1127_ = lean_ctor_get(v_code_861_, 1);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_1128_);
v___x_1118_ = v_code_861_;
v_isShared_1119_ = v_isSharedCheck_1126_;
goto v_resetjp_1117_;
}
else
{
lean_dec(v_code_861_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1126_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v_a_1110_);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_decl_983_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_a_1110_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1121_);
v___x_1123_ = v___x_1112_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
size_t v___x_1129_; uint8_t v___x_1130_; 
v___x_1129_ = lean_ptr_addr(v_decl_983_);
v___x_1130_ = lean_usize_dec_eq(v___x_1129_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1140_; 
lean_inc_ref(v_decl_983_);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; lean_object* v_unused_1142_; 
v_unused_1141_ = lean_ctor_get(v_code_861_, 1);
lean_dec(v_unused_1141_);
v_unused_1142_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_1142_);
v___x_1132_ = v_code_861_;
v_isShared_1133_ = v_isSharedCheck_1140_;
goto v_resetjp_1131_;
}
else
{
lean_dec(v_code_861_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1140_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 1, v_a_1110_);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_decl_983_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_a_1110_);
v___x_1135_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1135_);
v___x_1137_ = v___x_1112_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v___x_1144_; 
lean_dec(v_a_1110_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v_code_861_);
v___x_1144_ = v___x_1112_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_code_861_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_861_, 2);
return v___x_1109_;
}
}
v___jp_985_:
{
uint8_t v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_993_ = 0;
v___x_994_ = lean_box(0);
lean_inc(v_auxDeclName_988_);
v___x_995_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_995_, 0, v_auxDeclName_988_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
lean_ctor_set(v___x_995_, 2, v_argsNew_986_);
lean_inc_ref(v_decl_983_);
v___x_996_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_993_, v_decl_983_, v___x_995_, v___y_990_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
lean_inc_ref(v_k_984_);
v___x_998_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_984_, v___y_987_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1036_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1036_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1036_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
size_t v___x_1003_; size_t v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_ptr_addr(v_k_984_);
v___x_1004_ = lean_ptr_addr(v_a_999_);
v___x_1005_ = lean_usize_dec_eq(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1015_; 
v_isSharedCheck_1015_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; lean_object* v_unused_1017_; 
v_unused_1016_ = lean_ctor_get(v_code_861_, 1);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_1017_);
v___x_1007_ = v_code_861_;
v_isShared_1008_ = v_isSharedCheck_1015_;
goto v_resetjp_1006_;
}
else
{
lean_dec(v_code_861_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1015_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v_a_999_);
lean_ctor_set(v___x_1007_, 0, v_a_997_);
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_997_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_a_999_);
v___x_1010_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1010_);
v___x_1012_ = v___x_1001_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
size_t v___x_1018_; size_t v___x_1019_; uint8_t v___x_1020_; 
v___x_1018_ = lean_ptr_addr(v_decl_983_);
v___x_1019_ = lean_ptr_addr(v_a_997_);
v___x_1020_ = lean_usize_dec_eq(v___x_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1030_; 
v_isSharedCheck_1030_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; lean_object* v_unused_1032_; 
v_unused_1031_ = lean_ctor_get(v_code_861_, 1);
lean_dec(v_unused_1031_);
v_unused_1032_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_1032_);
v___x_1022_ = v_code_861_;
v_isShared_1023_ = v_isSharedCheck_1030_;
goto v_resetjp_1021_;
}
else
{
lean_dec(v_code_861_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1030_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v_a_999_);
lean_ctor_set(v___x_1022_, 0, v_a_997_);
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_997_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_a_999_);
v___x_1025_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1027_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1025_);
v___x_1027_ = v___x_1001_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v___x_1034_; 
lean_dec(v_a_999_);
lean_dec(v_a_997_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_code_861_);
v___x_1034_ = v___x_1001_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_code_861_);
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
else
{
lean_dec(v_a_997_);
lean_dec_ref_known(v_code_861_, 2);
return v___x_998_;
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref_known(v_code_861_, 2);
v_a_1037_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_996_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_996_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1147_; lean_object* v_k_1148_; 
v_decl_1147_ = lean_ctor_get(v_code_861_, 0);
v_k_1148_ = lean_ctor_get(v_code_861_, 1);
lean_inc_ref(v_k_1148_);
lean_inc_ref(v_decl_1147_);
v_decl_869_ = v_decl_1147_;
v_k_870_ = v_k_1148_;
v___y_871_ = v_a_862_;
v___y_872_ = v_a_863_;
v___y_873_ = v_a_864_;
v___y_874_ = v_a_865_;
v___y_875_ = v_a_866_;
goto v___jp_868_;
}
case 2:
{
lean_object* v_decl_1149_; lean_object* v_k_1150_; 
v_decl_1149_ = lean_ctor_get(v_code_861_, 0);
v_k_1150_ = lean_ctor_get(v_code_861_, 1);
lean_inc_ref(v_k_1150_);
lean_inc_ref(v_decl_1149_);
v_decl_869_ = v_decl_1149_;
v_k_870_ = v_k_1150_;
v___y_871_ = v_a_862_;
v___y_872_ = v_a_863_;
v___y_873_ = v_a_864_;
v___y_874_ = v_a_865_;
v___y_875_ = v_a_866_;
goto v___jp_868_;
}
case 4:
{
lean_object* v_cases_1151_; lean_object* v_typeName_1152_; lean_object* v_resultType_1153_; lean_object* v_discr_1154_; lean_object* v_alts_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1194_; 
v_cases_1151_ = lean_ctor_get(v_code_861_, 0);
lean_inc_ref(v_cases_1151_);
v_typeName_1152_ = lean_ctor_get(v_cases_1151_, 0);
v_resultType_1153_ = lean_ctor_get(v_cases_1151_, 1);
v_discr_1154_ = lean_ctor_get(v_cases_1151_, 2);
v_alts_1155_ = lean_ctor_get(v_cases_1151_, 3);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_cases_1151_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1157_ = v_cases_1151_;
v_isShared_1158_ = v_isSharedCheck_1194_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_alts_1155_);
lean_inc(v_discr_1154_);
lean_inc(v_resultType_1153_);
lean_inc(v_typeName_1152_);
lean_dec(v_cases_1151_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1194_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1155_);
v___x_1160_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v___x_1159_, v_alts_1155_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1185_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1185_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1185_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
size_t v___x_1165_; size_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1165_ = lean_ptr_addr(v_alts_1155_);
lean_dec_ref(v_alts_1155_);
v___x_1166_ = lean_ptr_addr(v_a_1161_);
v___x_1167_ = lean_usize_dec_eq(v___x_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1180_; 
v_isSharedCheck_1180_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_1181_);
v___x_1169_ = v_code_861_;
v_isShared_1170_ = v_isSharedCheck_1180_;
goto v_resetjp_1168_;
}
else
{
lean_dec(v_code_861_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1180_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 3, v_a_1161_);
v___x_1172_ = v___x_1157_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_typeName_1152_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_resultType_1153_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_discr_1154_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_a_1161_);
v___x_1172_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1174_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1172_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1176_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1174_);
v___x_1176_ = v___x_1163_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
else
{
lean_object* v___x_1183_; 
lean_dec(v_a_1161_);
lean_del_object(v___x_1157_);
lean_dec(v_discr_1154_);
lean_dec_ref(v_resultType_1153_);
lean_dec(v_typeName_1152_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v_code_861_);
v___x_1183_ = v___x_1163_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_code_861_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_del_object(v___x_1157_);
lean_dec_ref(v_alts_1155_);
lean_dec(v_discr_1154_);
lean_dec_ref(v_resultType_1153_);
lean_dec(v_typeName_1152_);
lean_dec_ref_known(v_code_861_, 1);
v_a_1186_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1160_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1160_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
default: 
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_code_861_);
return v___x_1195_;
}
}
v___jp_868_:
{
lean_object* v_params_876_; lean_object* v_type_877_; lean_object* v_value_878_; uint8_t v___x_879_; lean_object* v___x_880_; 
v_params_876_ = lean_ctor_get(v_decl_869_, 2);
lean_inc_ref(v_params_876_);
v_type_877_ = lean_ctor_get(v_decl_869_, 3);
lean_inc_ref(v_type_877_);
v_value_878_ = lean_ctor_get(v_decl_869_, 4);
v___x_879_ = 0;
lean_inc_ref(v_value_878_);
v___x_880_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_value_878_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_879_, v_decl_869_, v_type_877_, v_params_876_, v_a_881_, v___y_873_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_884_) == 0)
{
switch(lean_obj_tag(v_code_861_))
{
case 1:
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_924_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_924_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_924_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_924_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_decl_889_; lean_object* v_k_890_; size_t v___x_891_; size_t v___x_892_; uint8_t v___x_893_; 
v_decl_889_ = lean_ctor_get(v_code_861_, 0);
v_k_890_ = lean_ctor_get(v_code_861_, 1);
v___x_891_ = lean_ptr_addr(v_k_890_);
v___x_892_ = lean_ptr_addr(v_a_885_);
v___x_893_ = lean_usize_dec_eq(v___x_891_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_903_; 
v_isSharedCheck_903_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; lean_object* v_unused_905_; 
v_unused_904_ = lean_ctor_get(v_code_861_, 1);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_905_);
v___x_895_ = v_code_861_;
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
else
{
lean_dec(v_code_861_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_903_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v_a_885_);
lean_ctor_set(v___x_895_, 0, v_a_883_);
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_883_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_a_885_);
v___x_898_ = v_reuseFailAlloc_902_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_898_);
v___x_900_ = v___x_887_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
size_t v___x_906_; size_t v___x_907_; uint8_t v___x_908_; 
v___x_906_ = lean_ptr_addr(v_decl_889_);
v___x_907_ = lean_ptr_addr(v_a_883_);
v___x_908_ = lean_usize_dec_eq(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_918_; 
v_isSharedCheck_918_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; lean_object* v_unused_920_; 
v_unused_919_ = lean_ctor_get(v_code_861_, 1);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_920_);
v___x_910_ = v_code_861_;
v_isShared_911_ = v_isSharedCheck_918_;
goto v_resetjp_909_;
}
else
{
lean_dec(v_code_861_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_918_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v_a_885_);
lean_ctor_set(v___x_910_, 0, v_a_883_);
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_883_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_a_885_);
v___x_913_ = v_reuseFailAlloc_917_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_915_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_913_);
v___x_915_ = v___x_887_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
else
{
lean_object* v___x_922_; 
lean_dec(v_a_885_);
lean_dec(v_a_883_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v_code_861_);
v___x_922_ = v___x_887_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_code_861_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
case 2:
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_964_; 
v_a_925_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_964_ == 0)
{
v___x_927_ = v___x_884_;
v_isShared_928_ = v_isSharedCheck_964_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_884_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_964_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_decl_929_; lean_object* v_k_930_; size_t v___x_931_; size_t v___x_932_; uint8_t v___x_933_; 
v_decl_929_ = lean_ctor_get(v_code_861_, 0);
v_k_930_ = lean_ctor_get(v_code_861_, 1);
v___x_931_ = lean_ptr_addr(v_k_930_);
v___x_932_ = lean_ptr_addr(v_a_925_);
v___x_933_ = lean_usize_dec_eq(v___x_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; lean_object* v_unused_945_; 
v_unused_944_ = lean_ctor_get(v_code_861_, 1);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_945_);
v___x_935_ = v_code_861_;
v_isShared_936_ = v_isSharedCheck_943_;
goto v_resetjp_934_;
}
else
{
lean_dec(v_code_861_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_943_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 1, v_a_925_);
lean_ctor_set(v___x_935_, 0, v_a_883_);
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_883_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_a_925_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_938_);
v___x_940_ = v___x_927_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
size_t v___x_946_; size_t v___x_947_; uint8_t v___x_948_; 
v___x_946_ = lean_ptr_addr(v_decl_929_);
v___x_947_ = lean_ptr_addr(v_a_883_);
v___x_948_ = lean_usize_dec_eq(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_958_; 
v_isSharedCheck_958_ = !lean_is_exclusive(v_code_861_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; lean_object* v_unused_960_; 
v_unused_959_ = lean_ctor_get(v_code_861_, 1);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_code_861_, 0);
lean_dec(v_unused_960_);
v___x_950_ = v_code_861_;
v_isShared_951_ = v_isSharedCheck_958_;
goto v_resetjp_949_;
}
else
{
lean_dec(v_code_861_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_958_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v_a_925_);
lean_ctor_set(v___x_950_, 0, v_a_883_);
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_883_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_a_925_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_953_);
v___x_955_ = v___x_927_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
else
{
lean_object* v___x_962_; 
lean_dec(v_a_925_);
lean_dec(v_a_883_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v_code_861_);
v___x_962_ = v___x_927_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_code_861_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
default: 
{
lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_a_883_);
lean_dec_ref(v_code_861_);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v___x_884_, 0);
lean_dec(v_unused_974_);
v___x_966_ = v___x_884_;
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
else
{
lean_dec(v___x_884_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_968_ = lean_obj_once(&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3, &l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once, _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3);
v___x_969_ = l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(v___x_968_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_969_);
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
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
else
{
lean_dec(v_a_883_);
lean_dec_ref(v_code_861_);
return v___x_884_;
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v_k_870_);
lean_dec_ref(v_code_861_);
v_a_975_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_882_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_882_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
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
else
{
lean_dec_ref(v_type_877_);
lean_dec_ref(v_params_876_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
lean_dec_ref(v_code_861_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(lean_object* v_i_1196_, lean_object* v_as_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_array_get_size(v_as_1197_);
v___x_1205_ = lean_nat_dec_lt(v_i_1196_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; 
lean_dec(v_i_1196_);
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_as_1197_);
return v___x_1206_;
}
else
{
lean_object* v_a_1207_; lean_object* v___y_1209_; 
v_a_1207_ = lean_array_fget_borrowed(v_as_1197_, v_i_1196_);
switch(lean_obj_tag(v_a_1207_))
{
case 0:
{
lean_object* v_code_1231_; 
v_code_1231_ = lean_ctor_get(v_a_1207_, 2);
lean_inc_ref(v_code_1231_);
v___y_1209_ = v_code_1231_;
goto v___jp_1208_;
}
case 1:
{
lean_object* v_code_1232_; 
v_code_1232_ = lean_ctor_get(v_a_1207_, 1);
lean_inc_ref(v_code_1232_);
v___y_1209_ = v_code_1232_;
goto v___jp_1208_;
}
default: 
{
lean_object* v_code_1233_; 
v_code_1233_ = lean_ctor_get(v_a_1207_, 0);
lean_inc_ref(v_code_1233_);
v___y_1209_ = v_code_1233_;
goto v___jp_1208_;
}
}
v___jp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v___y_1209_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; size_t v___x_1213_; size_t v___x_1214_; uint8_t v___x_1215_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
lean_inc(v_a_1207_);
v___x_1212_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1207_, v_a_1211_);
v___x_1213_ = lean_ptr_addr(v_a_1207_);
v___x_1214_ = lean_ptr_addr(v___x_1212_);
v___x_1215_ = lean_usize_dec_eq(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_unsigned_to_nat(1u);
v___x_1217_ = lean_nat_add(v_i_1196_, v___x_1216_);
v___x_1218_ = lean_array_fset(v_as_1197_, v_i_1196_, v___x_1212_);
lean_dec(v_i_1196_);
v_i_1196_ = v___x_1217_;
v_as_1197_ = v___x_1218_;
goto _start;
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref(v___x_1212_);
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = lean_nat_add(v_i_1196_, v___x_1220_);
lean_dec(v_i_1196_);
v_i_1196_ = v___x_1221_;
goto _start;
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v_as_1197_);
lean_dec(v_i_1196_);
v_a_1223_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1210_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1210_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(lean_object* v_i_1234_, lean_object* v_as_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v_i_1234_, v_as_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1236_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object* v_code_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_code_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec_ref(v_a_1244_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object* v_args_1251_, lean_object* v_upperBound_1252_, lean_object* v___x_1253_, lean_object* v_inst_1254_, lean_object* v_R_1255_, lean_object* v_a_1256_, lean_object* v_b_1257_, lean_object* v_c_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1251_, v_upperBound_1252_, v___x_1253_, v_a_1256_, v_b_1257_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object* v_args_1266_, lean_object* v_upperBound_1267_, lean_object* v___x_1268_, lean_object* v_inst_1269_, lean_object* v_R_1270_, lean_object* v_a_1271_, lean_object* v_b_1272_, lean_object* v_c_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(v_args_1266_, v_upperBound_1267_, v___x_1268_, v_inst_1269_, v_R_1270_, v_a_1271_, v_b_1272_, v_c_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___x_1268_);
lean_dec(v_upperBound_1267_);
lean_dec_ref(v_args_1266_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object* v_f_1281_, lean_object* v_v_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
if (lean_obj_tag(v_v_1282_) == 0)
{
lean_object* v_code_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1313_; 
v_code_1289_ = lean_ctor_get(v_v_1282_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_v_1282_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1291_ = v_v_1282_;
v_isShared_1292_ = v_isSharedCheck_1313_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_code_1289_);
lean_dec(v_v_1282_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1313_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; 
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc_ref(v___y_1283_);
v___x_1293_ = lean_apply_7(v_f_1281_, v_code_1289_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1304_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1304_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1304_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v_a_1294_);
v___x_1299_ = v___x_1291_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1299_);
v___x_1301_ = v___x_1296_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_del_object(v___x_1291_);
v_a_1305_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1293_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1293_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
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
}
else
{
lean_object* v___x_1314_; 
lean_dec_ref(v_f_1281_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_v_1282_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object* v_f_1315_, lean_object* v_v_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1315_, v_v_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(uint8_t v_pu_1324_, lean_object* v_f_1325_, lean_object* v_v_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1325_, v_v_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object* v_pu_1334_, lean_object* v_f_1335_, lean_object* v_v_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
uint8_t v_pu_boxed_1343_; lean_object* v_res_1344_; 
v_pu_boxed_1343_ = lean_unbox(v_pu_1334_);
v_res_1344_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(v_pu_boxed_1343_, v_f_1335_, v_v_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___y_1337_);
return v_res_1344_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1345_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1348_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1349_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
lean_ctor_set(v___x_1351_, 2, v___x_1350_);
lean_ctor_set(v___x_1351_, 3, v___x_1350_);
lean_ctor_set(v___x_1351_, 4, v___x_1349_);
lean_ctor_set(v___x_1351_, 5, v___x_1349_);
lean_ctor_set(v___x_1351_, 6, v___x_1349_);
lean_ctor_set(v___x_1351_, 7, v___x_1349_);
lean_ctor_set(v___x_1351_, 8, v___x_1349_);
lean_ctor_set(v___x_1351_, 9, v___x_1349_);
lean_ctor_set(v___x_1351_, 10, v___x_1349_);
lean_ctor_set(v___x_1351_, 11, v___x_1348_);
return v___x_1351_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3(void){
_start:
{
lean_object* v___x_1352_; double v___x_1353_; 
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = lean_float_of_nat(v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* v_cls_1357_, lean_object* v_msg_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_ref_1364_; lean_object* v___x_1365_; lean_object* v_env_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v_ref_1364_ = lean_ctor_get(v___y_1361_, 2);
v___x_1365_ = lean_st_ref_get(v___y_1362_);
v_env_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc_ref(v_env_1366_);
lean_dec(v___x_1365_);
v___x_1367_ = lean_st_ref_get(v___y_1360_);
v___x_1368_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1359_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1428_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1428_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1428_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_lctx_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1426_; 
v_lctx_1373_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v___x_1367_, 1);
lean_dec(v_unused_1427_);
v___x_1375_ = v___x_1367_;
v_isShared_1376_ = v_isSharedCheck_1426_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_lctx_1373_);
lean_dec(v___x_1367_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1426_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1377_ = lean_unbox(v_a_1369_);
lean_dec(v_a_1369_);
v___x_1378_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1373_, v___x_1377_);
lean_dec_ref(v_lctx_1373_);
v___x_1379_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1361_);
v___x_1380_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2);
v___x_1381_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1381_, 0, v_env_1366_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
lean_ctor_set(v___x_1381_, 2, v___x_1378_);
lean_ctor_set(v___x_1381_, 3, v___x_1379_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 3);
lean_ctor_set(v___x_1375_, 1, v_msg_1358_);
lean_ctor_set(v___x_1375_, 0, v___x_1381_);
v___x_1383_ = v___x_1375_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_msg_1358_);
v___x_1383_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; lean_object* v_traceState_1385_; lean_object* v_env_1386_; lean_object* v_nextMacroScope_1387_; lean_object* v_ngen_1388_; lean_object* v_auxDeclNGen_1389_; lean_object* v_cache_1390_; lean_object* v_recordedDeps_1391_; lean_object* v_messages_1392_; lean_object* v_infoState_1393_; lean_object* v_snapshotTasks_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1424_; 
v___x_1384_ = lean_st_ref_take(v___y_1362_);
v_traceState_1385_ = lean_ctor_get(v___x_1384_, 4);
v_env_1386_ = lean_ctor_get(v___x_1384_, 0);
v_nextMacroScope_1387_ = lean_ctor_get(v___x_1384_, 1);
v_ngen_1388_ = lean_ctor_get(v___x_1384_, 2);
v_auxDeclNGen_1389_ = lean_ctor_get(v___x_1384_, 3);
v_cache_1390_ = lean_ctor_get(v___x_1384_, 5);
v_recordedDeps_1391_ = lean_ctor_get(v___x_1384_, 6);
v_messages_1392_ = lean_ctor_get(v___x_1384_, 7);
v_infoState_1393_ = lean_ctor_get(v___x_1384_, 8);
v_snapshotTasks_1394_ = lean_ctor_get(v___x_1384_, 9);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1396_ = v___x_1384_;
v_isShared_1397_ = v_isSharedCheck_1424_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_snapshotTasks_1394_);
lean_inc(v_infoState_1393_);
lean_inc(v_messages_1392_);
lean_inc(v_recordedDeps_1391_);
lean_inc(v_cache_1390_);
lean_inc(v_traceState_1385_);
lean_inc(v_auxDeclNGen_1389_);
lean_inc(v_ngen_1388_);
lean_inc(v_nextMacroScope_1387_);
lean_inc(v_env_1386_);
lean_dec(v___x_1384_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1424_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
uint64_t v_tid_1398_; lean_object* v_traces_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1423_; 
v_tid_1398_ = lean_ctor_get_uint64(v_traceState_1385_, sizeof(void*)*1);
v_traces_1399_ = lean_ctor_get(v_traceState_1385_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_traceState_1385_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1401_ = v_traceState_1385_;
v_isShared_1402_ = v_isSharedCheck_1423_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_traces_1399_);
lean_dec(v_traceState_1385_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1423_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; double v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1403_ = lean_box(0);
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3);
v___x_1406_ = 0;
v___x_1407_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4));
v___x_1408_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1408_, 0, v_cls_1357_);
lean_ctor_set(v___x_1408_, 1, v___x_1404_);
lean_ctor_set(v___x_1408_, 2, v___x_1407_);
lean_ctor_set_float(v___x_1408_, sizeof(void*)*3, v___x_1405_);
lean_ctor_set_float(v___x_1408_, sizeof(void*)*3 + 8, v___x_1405_);
lean_ctor_set_uint8(v___x_1408_, sizeof(void*)*3 + 16, v___x_1406_);
v___x_1409_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5));
v___x_1410_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1383_);
lean_ctor_set(v___x_1410_, 2, v___x_1409_);
lean_inc(v_ref_1364_);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_ref_1364_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_Lean_PersistentArray_push___redArg(v_traces_1399_, v___x_1411_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1412_);
v___x_1414_ = v___x_1401_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1412_);
lean_ctor_set_uint64(v_reuseFailAlloc_1422_, sizeof(void*)*1, v_tid_1398_);
v___x_1414_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v___x_1414_);
v___x_1416_ = v___x_1396_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_env_1386_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_nextMacroScope_1387_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_ngen_1388_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_auxDeclNGen_1389_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1421_, 5, v_cache_1390_);
lean_ctor_set(v_reuseFailAlloc_1421_, 6, v_recordedDeps_1391_);
lean_ctor_set(v_reuseFailAlloc_1421_, 7, v_messages_1392_);
lean_ctor_set(v_reuseFailAlloc_1421_, 8, v_infoState_1393_);
lean_ctor_set(v_reuseFailAlloc_1421_, 9, v_snapshotTasks_1394_);
v___x_1416_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_st_ref_put(v___y_1362_, v___x_1416_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1403_);
v___x_1419_ = v___x_1371_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1403_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
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
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v___x_1367_);
lean_dec_ref(v_env_1366_);
lean_dec_ref(v_msg_1358_);
lean_dec(v_cls_1357_);
v_a_1429_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1368_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1368_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___boxed(lean_object* v_cls_1437_, lean_object* v_msg_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v_cls_1437_, v_msg_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(lean_object* v_name_1446_, lean_object* v___x_1447_, lean_object* v___x_1448_, uint8_t v___x_1449_, lean_object* v_value_1450_, lean_object* v_code_1451_, uint8_t v_safe_1452_, uint8_t v_recursive_1453_, lean_object* v_inlineAttr_x3f_1454_, lean_object* v_params_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_inc(v___x_1447_);
v___x_1461_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1461_, 0, v_name_1446_);
lean_ctor_set(v___x_1461_, 1, v___x_1447_);
lean_ctor_set(v___x_1461_, 2, v___x_1448_);
lean_ctor_set_uint8(v___x_1461_, sizeof(void*)*3, v___x_1449_);
v___x_1462_ = 0;
v___x_1463_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___closed__0));
v___x_1464_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v___x_1463_, v_value_1450_, v___x_1461_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec_ref_known(v___x_1461_, 3);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1466_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1464_, 1);
v___x_1466_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_1462_, v_code_1451_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1466_, 1);
lean_inc_ref(v_params_1455_);
v___x_1468_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_1462_, v_params_1455_, v_a_1467_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v_a_1467_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1471_, 0, v___x_1447_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
lean_ctor_set(v___x_1471_, 2, v_a_1469_);
lean_ctor_set(v___x_1471_, 3, v_params_1455_);
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*4, v_safe_1452_);
v___x_1472_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v_a_1465_);
lean_ctor_set(v___x_1472_, 2, v_inlineAttr_x3f_1454_);
lean_ctor_set_uint8(v___x_1472_, sizeof(void*)*3, v_recursive_1453_);
lean_inc_ref(v___x_1472_);
v___x_1473_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1472_, v___y_1459_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v___x_1473_, 0);
lean_dec(v_unused_1481_);
v___x_1475_ = v___x_1473_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v___x_1473_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1472_);
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1472_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref_known(v___x_1472_, 3);
v_a_1482_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1473_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1473_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_a_1465_);
lean_dec_ref(v_params_1455_);
lean_dec(v_inlineAttr_x3f_1454_);
lean_dec(v___x_1447_);
v_a_1490_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1468_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1468_);
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
lean_dec(v_a_1465_);
lean_dec_ref(v_params_1455_);
lean_dec(v_inlineAttr_x3f_1454_);
lean_dec(v___x_1447_);
v_a_1498_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1466_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1466_);
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
lean_dec_ref(v_params_1455_);
lean_dec(v_inlineAttr_x3f_1454_);
lean_dec_ref(v_code_1451_);
lean_dec(v___x_1447_);
v_a_1506_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1464_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1464_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed(lean_object* v_name_1514_, lean_object* v___x_1515_, lean_object* v___x_1516_, lean_object* v___x_1517_, lean_object* v_value_1518_, lean_object* v_code_1519_, lean_object* v_safe_1520_, lean_object* v_recursive_1521_, lean_object* v_inlineAttr_x3f_1522_, lean_object* v_params_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
uint8_t v___x_11810__boxed_1529_; uint8_t v_safe_boxed_1530_; uint8_t v_recursive_boxed_1531_; lean_object* v_res_1532_; 
v___x_11810__boxed_1529_ = lean_unbox(v___x_1517_);
v_safe_boxed_1530_ = lean_unbox(v_safe_1520_);
v_recursive_boxed_1531_ = lean_unbox(v_recursive_1521_);
v_res_1532_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(v_name_1514_, v___x_1515_, v___x_1516_, v___x_11810__boxed_1529_, v_value_1518_, v_code_1519_, v_safe_boxed_1530_, v_recursive_boxed_1531_, v_inlineAttr_x3f_1522_, v_params_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(lean_object* v___x_1539_, uint8_t v___x_1540_, lean_object* v_name_1541_, lean_object* v_levelParams_1542_, lean_object* v_type_1543_, lean_object* v_a_1544_, uint8_t v_safe_1545_, uint8_t v___x_1546_, lean_object* v_____r_1547_, lean_object* v_args_1548_, uint8_t v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1539_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
lean_ctor_set(v___x_1557_, 2, v_args_1548_);
v___x_1558_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__1));
v___x_1559_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1540_, v___x_1557_, v___x_1558_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v_fvarId_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
v_fvarId_1561_ = lean_ctor_get(v_a_1560_, 0);
lean_inc(v_fvarId_1561_);
v___x_1562_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1562_, 0, v_fvarId_1561_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v_a_1560_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1565_, 0, v_name_1541_);
lean_ctor_set(v___x_1565_, 1, v_levelParams_1542_);
lean_ctor_set(v___x_1565_, 2, v_type_1543_);
lean_ctor_set(v___x_1565_, 3, v_a_1544_);
lean_ctor_set_uint8(v___x_1565_, sizeof(void*)*4, v_safe_1545_);
v___x_1566_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__2));
v___x_1567_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1564_);
lean_ctor_set(v___x_1567_, 2, v___x_1566_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*3, v___x_1546_);
lean_inc_ref(v___x_1567_);
v___x_1568_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1567_, v___y_1554_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v___x_1568_, 0);
lean_dec(v_unused_1576_);
v___x_1570_ = v___x_1568_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_dec(v___x_1568_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1567_);
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1567_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref_known(v___x_1567_, 3);
v_a_1577_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1568_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1568_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_a_1544_);
lean_dec_ref(v_type_1543_);
lean_dec(v_levelParams_1542_);
lean_dec(v_name_1541_);
v_a_1585_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1559_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1559_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___boxed(lean_object** _args){
lean_object* v___x_1593_ = _args[0];
lean_object* v___x_1594_ = _args[1];
lean_object* v_name_1595_ = _args[2];
lean_object* v_levelParams_1596_ = _args[3];
lean_object* v_type_1597_ = _args[4];
lean_object* v_a_1598_ = _args[5];
lean_object* v_safe_1599_ = _args[6];
lean_object* v___x_1600_ = _args[7];
lean_object* v_____r_1601_ = _args[8];
lean_object* v_args_1602_ = _args[9];
lean_object* v___y_1603_ = _args[10];
lean_object* v___y_1604_ = _args[11];
lean_object* v___y_1605_ = _args[12];
lean_object* v___y_1606_ = _args[13];
lean_object* v___y_1607_ = _args[14];
lean_object* v___y_1608_ = _args[15];
lean_object* v___y_1609_ = _args[16];
_start:
{
uint8_t v___x_11954__boxed_1610_; uint8_t v_safe_boxed_1611_; uint8_t v___x_11956__boxed_1612_; uint8_t v___y_11958__boxed_1613_; lean_object* v_res_1614_; 
v___x_11954__boxed_1610_ = lean_unbox(v___x_1594_);
v_safe_boxed_1611_ = lean_unbox(v_safe_1599_);
v___x_11956__boxed_1612_ = lean_unbox(v___x_1600_);
v___y_11958__boxed_1613_ = lean_unbox(v___y_1603_);
v_res_1614_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___x_1593_, v___x_11954__boxed_1610_, v_name_1595_, v_levelParams_1596_, v_type_1597_, v_a_1598_, v_safe_boxed_1611_, v___x_11956__boxed_1612_, v_____r_1601_, v_args_1602_, v___y_11958__boxed_1613_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
if (lean_obj_tag(v_x_1616_) == 0)
{
lean_inc(v_x_1615_);
return v_x_1615_;
}
else
{
lean_object* v_key_1617_; lean_object* v_tail_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_key_1617_ = lean_ctor_get(v_x_1616_, 0);
v_tail_1618_ = lean_ctor_get(v_x_1616_, 2);
v___x_1619_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1615_, v_tail_1618_);
lean_inc(v_key_1617_);
v___x_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1620_, 0, v_key_1617_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object* v_x_1621_, lean_object* v_x_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1621_, v_x_1622_);
lean_dec(v_x_1622_);
lean_dec(v_x_1621_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object* v_as_1624_, size_t v_i_1625_, size_t v_stop_1626_, lean_object* v_b_1627_){
_start:
{
uint8_t v___x_1628_; 
v___x_1628_ = lean_usize_dec_eq(v_i_1625_, v_stop_1626_);
if (v___x_1628_ == 0)
{
size_t v___x_1629_; size_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1629_ = ((size_t)1ULL);
v___x_1630_ = lean_usize_sub(v_i_1625_, v___x_1629_);
v___x_1631_ = lean_array_uget_borrowed(v_as_1624_, v___x_1630_);
v___x_1632_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_b_1627_, v___x_1631_);
lean_dec(v_b_1627_);
v_i_1625_ = v___x_1630_;
v_b_1627_ = v___x_1632_;
goto _start;
}
else
{
return v_b_1627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object* v_as_1634_, lean_object* v_i_1635_, lean_object* v_stop_1636_, lean_object* v_b_1637_){
_start:
{
size_t v_i_boxed_1638_; size_t v_stop_boxed_1639_; lean_object* v_res_1640_; 
v_i_boxed_1638_ = lean_unbox_usize(v_i_1635_);
lean_dec(v_i_1635_);
v_stop_boxed_1639_ = lean_unbox_usize(v_stop_1636_);
lean_dec(v_stop_1636_);
v_res_1640_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_as_1634_, v_i_boxed_1638_, v_stop_boxed_1639_, v_b_1637_);
lean_dec_ref(v_as_1634_);
return v_res_1640_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object* v_m_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_buckets_1643_; lean_object* v___x_1644_; uint64_t v___x_1645_; uint64_t v___x_1646_; uint64_t v___x_1647_; uint64_t v_fold_1648_; uint64_t v___x_1649_; uint64_t v___x_1650_; uint64_t v___x_1651_; size_t v___x_1652_; size_t v___x_1653_; size_t v___x_1654_; size_t v___x_1655_; size_t v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v_buckets_1643_ = lean_ctor_get(v_m_1641_, 1);
v___x_1644_ = lean_array_get_size(v_buckets_1643_);
v___x_1645_ = l_Lean_instHashableFVarId_hash(v_a_1642_);
v___x_1646_ = 32ULL;
v___x_1647_ = lean_uint64_shift_right(v___x_1645_, v___x_1646_);
v_fold_1648_ = lean_uint64_xor(v___x_1645_, v___x_1647_);
v___x_1649_ = 16ULL;
v___x_1650_ = lean_uint64_shift_right(v_fold_1648_, v___x_1649_);
v___x_1651_ = lean_uint64_xor(v_fold_1648_, v___x_1650_);
v___x_1652_ = lean_uint64_to_usize(v___x_1651_);
v___x_1653_ = lean_usize_of_nat(v___x_1644_);
v___x_1654_ = ((size_t)1ULL);
v___x_1655_ = lean_usize_sub(v___x_1653_, v___x_1654_);
v___x_1656_ = lean_usize_land(v___x_1652_, v___x_1655_);
v___x_1657_ = lean_array_uget_borrowed(v_buckets_1643_, v___x_1656_);
v___x_1658_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_1642_, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object* v_m_1659_, lean_object* v_a_1660_){
_start:
{
uint8_t v_res_1661_; lean_object* v_r_1662_; 
v_res_1661_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1659_, v_a_1660_);
lean_dec(v_a_1660_);
lean_dec_ref(v_m_1659_);
v_r_1662_ = lean_box(v_res_1661_);
return v_r_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* v_a_1663_, lean_object* v_as_1664_, size_t v_i_1665_, size_t v_stop_1666_, lean_object* v_b_1667_){
_start:
{
lean_object* v___y_1669_; uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_eq(v_i_1665_, v_stop_1666_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v_fvarId_1675_; uint8_t v___x_1676_; 
v___x_1674_ = lean_array_uget_borrowed(v_as_1664_, v_i_1665_);
v_fvarId_1675_ = lean_ctor_get(v___x_1674_, 0);
v___x_1676_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1663_, v_fvarId_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
lean_inc(v___x_1674_);
v___x_1677_ = lean_array_push(v_b_1667_, v___x_1674_);
v___y_1669_ = v___x_1677_;
goto v___jp_1668_;
}
else
{
v___y_1669_ = v_b_1667_;
goto v___jp_1668_;
}
}
else
{
return v_b_1667_;
}
v___jp_1668_:
{
size_t v___x_1670_; size_t v___x_1671_; 
v___x_1670_ = ((size_t)1ULL);
v___x_1671_ = lean_usize_add(v_i_1665_, v___x_1670_);
v_i_1665_ = v___x_1671_;
v_b_1667_ = v___y_1669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* v_a_1678_, lean_object* v_as_1679_, lean_object* v_i_1680_, lean_object* v_stop_1681_, lean_object* v_b_1682_){
_start:
{
size_t v_i_boxed_1683_; size_t v_stop_boxed_1684_; lean_object* v_res_1685_; 
v_i_boxed_1683_ = lean_unbox_usize(v_i_1680_);
lean_dec(v_i_1680_);
v_stop_boxed_1684_ = lean_unbox_usize(v_stop_1681_);
lean_dec(v_stop_1681_);
v_res_1685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1678_, v_as_1679_, v_i_boxed_1683_, v_stop_boxed_1684_, v_b_1682_);
lean_dec_ref(v_as_1679_);
lean_dec_ref(v_a_1678_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
if (lean_obj_tag(v_a_1686_) == 0)
{
lean_object* v___x_1688_; 
v___x_1688_ = l_List_reverse___redArg(v_a_1687_);
return v___x_1688_;
}
else
{
lean_object* v_head_1689_; lean_object* v_tail_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1699_; 
v_head_1689_ = lean_ctor_get(v_a_1686_, 0);
v_tail_1690_ = lean_ctor_get(v_a_1686_, 1);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_a_1686_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1692_ = v_a_1686_;
v_isShared_1693_ = v_isSharedCheck_1699_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_tail_1690_);
lean_inc(v_head_1689_);
lean_dec(v_a_1686_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1699_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = l_Lean_MessageData_ofExpr(v_head_1689_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v_a_1687_);
lean_ctor_set(v___x_1692_, 0, v___x_1694_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_a_1687_);
v___x_1696_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
v_a_1686_ = v_tail_1690_;
v_a_1687_ = v___x_1696_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object* v_as_1700_, size_t v_sz_1701_, size_t v_i_1702_, lean_object* v_b_1703_){
_start:
{
lean_object* v_a_1706_; uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_lt(v_i_1702_, v_sz_1701_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_b_1703_);
return v___x_1711_;
}
else
{
lean_object* v_snd_1712_; lean_object* v_fst_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1748_; 
v_snd_1712_ = lean_ctor_get(v_b_1703_, 1);
v_fst_1713_ = lean_ctor_get(v_b_1703_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_b_1703_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1715_ = v_b_1703_;
v_isShared_1716_ = v_isSharedCheck_1748_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_snd_1712_);
lean_inc(v_fst_1713_);
lean_dec(v_b_1703_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1748_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v_array_1717_; lean_object* v_start_1718_; lean_object* v_stop_1719_; uint8_t v___x_1720_; 
v_array_1717_ = lean_ctor_get(v_snd_1712_, 0);
v_start_1718_ = lean_ctor_get(v_snd_1712_, 1);
v_stop_1719_ = lean_ctor_get(v_snd_1712_, 2);
v___x_1720_ = lean_nat_dec_lt(v_start_1718_, v_stop_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1722_; 
if (v_isShared_1716_ == 0)
{
v___x_1722_ = v___x_1715_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_fst_1713_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_snd_1712_);
v___x_1722_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
else
{
lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1744_; 
lean_inc(v_stop_1719_);
lean_inc(v_start_1718_);
lean_inc_ref(v_array_1717_);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_snd_1712_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; lean_object* v_unused_1746_; lean_object* v_unused_1747_; 
v_unused_1745_ = lean_ctor_get(v_snd_1712_, 2);
lean_dec(v_unused_1745_);
v_unused_1746_ = lean_ctor_get(v_snd_1712_, 1);
lean_dec(v_unused_1746_);
v_unused_1747_ = lean_ctor_get(v_snd_1712_, 0);
lean_dec(v_unused_1747_);
v___x_1726_ = v_snd_1712_;
v_isShared_1727_ = v_isSharedCheck_1744_;
goto v_resetjp_1725_;
}
else
{
lean_dec(v_snd_1712_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1744_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v_a_1728_ = lean_array_uget_borrowed(v_as_1700_, v_i_1702_);
v___x_1729_ = lean_array_fget(v_array_1717_, v_start_1718_);
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = lean_nat_add(v_start_1718_, v___x_1730_);
lean_dec(v_start_1718_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v___x_1731_);
v___x_1733_ = v___x_1726_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_array_1717_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_stop_1719_);
v___x_1733_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_unbox(v_a_1728_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1736_; 
lean_dec(v___x_1729_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1733_);
v___x_1736_ = v___x_1715_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_fst_1713_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1733_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
v_a_1706_ = v___x_1736_;
goto v___jp_1705_;
}
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1738_ = l_Lean_Compiler_LCNF_Param_toArg___redArg(v___x_1729_);
lean_dec(v___x_1729_);
v___x_1739_ = lean_array_push(v_fst_1713_, v___x_1738_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1733_);
lean_ctor_set(v___x_1715_, 0, v___x_1739_);
v___x_1741_ = v___x_1715_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___x_1733_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
v_a_1706_ = v___x_1741_;
goto v___jp_1705_;
}
}
}
}
}
}
}
v___jp_1705_:
{
size_t v___x_1707_; size_t v___x_1708_; 
v___x_1707_ = ((size_t)1ULL);
v___x_1708_ = lean_usize_add(v_i_1702_, v___x_1707_);
v_i_1702_ = v___x_1708_;
v_b_1703_ = v_a_1706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object* v_as_1749_, lean_object* v_sz_1750_, lean_object* v_i_1751_, lean_object* v_b_1752_, lean_object* v___y_1753_){
_start:
{
size_t v_sz_boxed_1754_; size_t v_i_boxed_1755_; lean_object* v_res_1756_; 
v_sz_boxed_1754_ = lean_unbox_usize(v_sz_1750_);
lean_dec(v_sz_1750_);
v_i_boxed_1755_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_1749_, v_sz_boxed_1754_, v_i_boxed_1755_, v_b_1752_);
lean_dec_ref(v_as_1749_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t v_sz_1757_, size_t v_i_1758_, lean_object* v_bs_1759_, uint8_t v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_usize_dec_lt(v_i_1758_, v_sz_1757_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_bs_1759_);
return v___x_1768_;
}
else
{
uint8_t v___x_1769_; lean_object* v_v_1770_; lean_object* v___x_1771_; lean_object* v_bs_x27_1772_; lean_object* v___x_1773_; 
v___x_1769_ = 0;
v_v_1770_ = lean_array_uget(v_bs_1759_, v_i_1758_);
v___x_1771_ = lean_unsigned_to_nat(0u);
v_bs_x27_1772_ = lean_array_uset(v_bs_1759_, v_i_1758_, v___x_1771_);
v___x_1773_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_1769_, v_v_1770_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref_known(v___x_1773_, 1);
v___x_1775_ = ((size_t)1ULL);
v___x_1776_ = lean_usize_add(v_i_1758_, v___x_1775_);
v___x_1777_ = lean_array_uset(v_bs_x27_1772_, v_i_1758_, v_a_1774_);
v_i_1758_ = v___x_1776_;
v_bs_1759_ = v___x_1777_;
goto _start;
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v_bs_x27_1772_);
v_a_1779_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1773_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1773_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* v_sz_1787_, lean_object* v_i_1788_, lean_object* v_bs_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
size_t v_sz_boxed_1797_; size_t v_i_boxed_1798_; uint8_t v___y_12255__boxed_1799_; lean_object* v_res_1800_; 
v_sz_boxed_1797_ = lean_unbox_usize(v_sz_1787_);
lean_dec(v_sz_1787_);
v_i_boxed_1798_ = lean_unbox_usize(v_i_1788_);
lean_dec(v_i_1788_);
v___y_12255__boxed_1799_ = lean_unbox(v___y_1790_);
v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_boxed_1797_, v_i_boxed_1798_, v_bs_1789_, v___y_12255__boxed_1799_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
if (lean_obj_tag(v_a_1801_) == 0)
{
lean_object* v___x_1803_; 
v___x_1803_ = l_List_reverse___redArg(v_a_1802_);
return v___x_1803_;
}
else
{
lean_object* v_head_1804_; lean_object* v_tail_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1814_; 
v_head_1804_ = lean_ctor_get(v_a_1801_, 0);
v_tail_1805_ = lean_ctor_get(v_a_1801_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_a_1801_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1807_ = v_a_1801_;
v_isShared_1808_ = v_isSharedCheck_1814_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_tail_1805_);
lean_inc(v_head_1804_);
lean_dec(v_a_1801_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1814_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = l_Lean_mkFVar(v_head_1804_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v_a_1802_);
lean_ctor_set(v___x_1807_, 0, v___x_1809_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_a_1802_);
v___x_1811_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
v_a_1801_ = v_tail_1805_;
v_a_1802_ = v___x_1811_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(lean_object* v_a_1815_, lean_object* v_as_1816_, size_t v_i_1817_, size_t v_stop_1818_, lean_object* v_b_1819_){
_start:
{
lean_object* v___y_1821_; uint8_t v___x_1825_; 
v___x_1825_ = lean_usize_dec_eq(v_i_1817_, v_stop_1818_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v_fvarId_1827_; uint8_t v___x_1828_; 
v___x_1826_ = lean_array_uget_borrowed(v_as_1816_, v_i_1817_);
v_fvarId_1827_ = lean_ctor_get(v___x_1826_, 0);
v___x_1828_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1815_, v_fvarId_1827_);
if (v___x_1828_ == 0)
{
v___y_1821_ = v_b_1819_;
goto v___jp_1820_;
}
else
{
lean_object* v___x_1829_; 
lean_inc(v___x_1826_);
v___x_1829_ = lean_array_push(v_b_1819_, v___x_1826_);
v___y_1821_ = v___x_1829_;
goto v___jp_1820_;
}
}
else
{
return v_b_1819_;
}
v___jp_1820_:
{
size_t v___x_1822_; size_t v___x_1823_; 
v___x_1822_ = ((size_t)1ULL);
v___x_1823_ = lean_usize_add(v_i_1817_, v___x_1822_);
v_i_1817_ = v___x_1823_;
v_b_1819_ = v___y_1821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6___boxed(lean_object* v_a_1830_, lean_object* v_as_1831_, lean_object* v_i_1832_, lean_object* v_stop_1833_, lean_object* v_b_1834_){
_start:
{
size_t v_i_boxed_1835_; size_t v_stop_boxed_1836_; lean_object* v_res_1837_; 
v_i_boxed_1835_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_stop_boxed_1836_ = lean_unbox_usize(v_stop_1833_);
lean_dec(v_stop_1833_);
v_res_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1830_, v_as_1831_, v_i_boxed_1835_, v_stop_boxed_1836_, v_b_1834_);
lean_dec_ref(v_as_1831_);
lean_dec_ref(v_a_1830_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object* v_a_1838_, lean_object* v_as_1839_, size_t v_i_1840_, size_t v_stop_1841_, lean_object* v_b_1842_){
_start:
{
lean_object* v___y_1844_; uint8_t v___x_1848_; 
v___x_1848_ = lean_usize_dec_eq(v_i_1840_, v_stop_1841_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v_fvarId_1850_; uint8_t v___x_1851_; 
v___x_1849_ = lean_array_uget_borrowed(v_as_1839_, v_i_1840_);
v_fvarId_1850_ = lean_ctor_get(v___x_1849_, 0);
v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1838_, v_fvarId_1850_);
if (v___x_1851_ == 0)
{
v___y_1844_ = v_b_1842_;
goto v___jp_1843_;
}
else
{
lean_object* v___x_1852_; 
lean_inc(v___x_1849_);
v___x_1852_ = lean_array_push(v_b_1842_, v___x_1849_);
v___y_1844_ = v___x_1852_;
goto v___jp_1843_;
}
}
else
{
return v_b_1842_;
}
v___jp_1843_:
{
size_t v___x_1845_; size_t v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1840_, v___x_1845_);
v___x_1847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1838_, v_as_1839_, v___x_1846_, v_stop_1841_, v___y_1844_);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object* v_a_1853_, lean_object* v_as_1854_, lean_object* v_i_1855_, lean_object* v_stop_1856_, lean_object* v_b_1857_){
_start:
{
size_t v_i_boxed_1858_; size_t v_stop_boxed_1859_; lean_object* v_res_1860_; 
v_i_boxed_1858_ = lean_unbox_usize(v_i_1855_);
lean_dec(v_i_1855_);
v_stop_boxed_1859_ = lean_unbox_usize(v_stop_1856_);
lean_dec(v_stop_1856_);
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1853_, v_as_1854_, v_i_boxed_1858_, v_stop_boxed_1859_, v_b_1857_);
lean_dec_ref(v_as_1854_);
lean_dec_ref(v_a_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object* v_a_1861_, size_t v_sz_1862_, size_t v_i_1863_, lean_object* v_bs_1864_){
_start:
{
uint8_t v___x_1865_; 
v___x_1865_ = lean_usize_dec_lt(v_i_1863_, v_sz_1862_);
if (v___x_1865_ == 0)
{
return v_bs_1864_;
}
else
{
lean_object* v_v_1866_; lean_object* v_fvarId_1867_; lean_object* v___x_1868_; lean_object* v_bs_x27_1869_; uint8_t v___x_1870_; size_t v___x_1871_; size_t v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_v_1866_ = lean_array_uget_borrowed(v_bs_1864_, v_i_1863_);
v_fvarId_1867_ = lean_ctor_get(v_v_1866_, 0);
lean_inc(v_fvarId_1867_);
v___x_1868_ = lean_unsigned_to_nat(0u);
v_bs_x27_1869_ = lean_array_uset(v_bs_1864_, v_i_1863_, v___x_1868_);
v___x_1870_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1861_, v_fvarId_1867_);
lean_dec(v_fvarId_1867_);
v___x_1871_ = ((size_t)1ULL);
v___x_1872_ = lean_usize_add(v_i_1863_, v___x_1871_);
v___x_1873_ = lean_box(v___x_1870_);
v___x_1874_ = lean_array_uset(v_bs_x27_1869_, v_i_1863_, v___x_1873_);
v_i_1863_ = v___x_1872_;
v_bs_1864_ = v___x_1874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object* v_a_1876_, lean_object* v_sz_1877_, lean_object* v_i_1878_, lean_object* v_bs_1879_){
_start:
{
size_t v_sz_boxed_1880_; size_t v_i_boxed_1881_; lean_object* v_res_1882_; 
v_sz_boxed_1880_ = lean_unbox_usize(v_sz_1877_);
lean_dec(v_sz_1877_);
v_i_boxed_1881_ = lean_unbox_usize(v_i_1878_);
lean_dec(v_i_1878_);
v_res_1882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1876_, v_sz_boxed_1880_, v_i_boxed_1881_, v_bs_1879_);
lean_dec_ref(v_a_1876_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* v_a_1883_, size_t v_sz_1884_, size_t v_i_1885_, lean_object* v_bs_1886_){
_start:
{
uint8_t v___x_1887_; 
v___x_1887_ = lean_usize_dec_lt(v_i_1885_, v_sz_1884_);
if (v___x_1887_ == 0)
{
return v_bs_1886_;
}
else
{
lean_object* v_v_1888_; lean_object* v_fvarId_1889_; lean_object* v___x_1890_; lean_object* v_bs_x27_1891_; uint8_t v___x_1892_; size_t v___x_1893_; size_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_v_1888_ = lean_array_uget_borrowed(v_bs_1886_, v_i_1885_);
v_fvarId_1889_ = lean_ctor_get(v_v_1888_, 0);
lean_inc(v_fvarId_1889_);
v___x_1890_ = lean_unsigned_to_nat(0u);
v_bs_x27_1891_ = lean_array_uset(v_bs_1886_, v_i_1885_, v___x_1890_);
v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1883_, v_fvarId_1889_);
lean_dec(v_fvarId_1889_);
v___x_1893_ = ((size_t)1ULL);
v___x_1894_ = lean_usize_add(v_i_1885_, v___x_1893_);
v___x_1895_ = lean_box(v___x_1892_);
v___x_1896_ = lean_array_uset(v_bs_x27_1891_, v_i_1885_, v___x_1895_);
v___x_1897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1883_, v_sz_1884_, v___x_1894_, v___x_1896_);
return v___x_1897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object* v_a_1898_, lean_object* v_sz_1899_, lean_object* v_i_1900_, lean_object* v_bs_1901_){
_start:
{
size_t v_sz_boxed_1902_; size_t v_i_boxed_1903_; lean_object* v_res_1904_; 
v_sz_boxed_1902_ = lean_unbox_usize(v_sz_1899_);
lean_dec(v_sz_1899_);
v_i_boxed_1903_ = lean_unbox_usize(v_i_1900_);
lean_dec(v_i_1900_);
v_res_1904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1898_, v_sz_boxed_1902_, v_i_boxed_1903_, v_bs_1901_);
lean_dec_ref(v_a_1898_);
return v_res_1904_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_unsigned_to_nat(16u);
v___x_1907_ = lean_mk_array(v___x_1906_, v___x_1905_);
return v___x_1907_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0);
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v___x_1908_);
return v___x_1910_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = lean_box(0);
v___x_1920_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6));
v___x_1921_ = l_Lean_Expr_const___override(v___x_1920_, v___x_1919_);
return v___x_1921_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_1934_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14));
v___x_1935_ = l_Lean_Name_append(v___x_1934_, v___x_1933_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16));
v___x_1938_ = l_Lean_stringToMessageData(v___x_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* v_decl_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
uint8_t v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v_value_1983_; 
v_value_1983_ = lean_ctor_get(v_decl_1939_, 1);
lean_inc_ref(v_value_1983_);
if (lean_obj_tag(v_value_1983_) == 0)
{
lean_object* v_toSignature_1984_; uint8_t v_recursive_1985_; lean_object* v_inlineAttr_x3f_1986_; lean_object* v_code_1987_; lean_object* v_name_1988_; lean_object* v_levelParams_1989_; lean_object* v_type_1990_; lean_object* v_params_1991_; uint8_t v_safe_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_toSignature_1984_ = lean_ctor_get(v_decl_1939_, 0);
v_recursive_1985_ = lean_ctor_get_uint8(v_decl_1939_, sizeof(void*)*3);
v_inlineAttr_x3f_1986_ = lean_ctor_get(v_decl_1939_, 2);
v_code_1987_ = lean_ctor_get(v_value_1983_, 0);
v_name_1988_ = lean_ctor_get(v_toSignature_1984_, 0);
v_levelParams_1989_ = lean_ctor_get(v_toSignature_1984_, 1);
v_type_1990_ = lean_ctor_get(v_toSignature_1984_, 2);
v_params_1991_ = lean_ctor_get(v_toSignature_1984_, 3);
v_safe_1992_ = lean_ctor_get_uint8(v_toSignature_1984_, sizeof(void*)*4);
v___x_1993_ = lean_array_get_size(v_params_1991_);
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = lean_nat_dec_eq(v___x_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_inc_ref(v_code_1987_);
lean_inc_ref(v_decl_1939_);
v___x_1996_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2171_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2171_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2171_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v_size_2001_; lean_object* v_buckets_2002_; uint8_t v___x_2003_; 
v_size_2001_ = lean_ctor_get(v_a_1997_, 0);
v_buckets_2002_ = lean_ctor_get(v_a_1997_, 1);
v___x_2003_ = lean_nat_dec_eq(v_size_2001_, v___x_1993_);
if (v___x_2003_ == 0)
{
lean_object* v_toCold_2004_; lean_object* v_options_2005_; lean_object* v_inheritedTraceOptions_2006_; uint8_t v_hasTrace_2007_; uint8_t v___x_2008_; uint8_t v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; size_t v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; size_t v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; size_t v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; size_t v___y_2077_; lean_object* v___y_2078_; uint8_t v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; size_t v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; size_t v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; 
lean_inc_ref(v_params_1991_);
lean_inc_ref(v_type_1990_);
lean_inc(v_levelParams_1989_);
lean_inc(v_name_1988_);
lean_inc(v_inlineAttr_x3f_1986_);
lean_del_object(v___x_1999_);
lean_dec_ref(v_decl_1939_);
v_toCold_2004_ = lean_ctor_get(v_a_1942_, 0);
v_options_2005_ = lean_ctor_get(v_toCold_2004_, 2);
v_inheritedTraceOptions_2006_ = lean_ctor_get(v_toCold_2004_, 11);
v_hasTrace_2007_ = lean_ctor_get_uint8(v_options_2005_, sizeof(void*)*1);
v___x_2008_ = lean_nat_dec_eq(v_size_2001_, v___x_1994_);
if (v_hasTrace_2007_ == 0)
{
v___y_2116_ = v_a_1940_;
v___y_2117_ = v_a_1941_;
v___y_2118_ = v_a_1942_;
v___y_2119_ = v_a_1943_;
goto v___jp_2115_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2137_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_2138_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15);
v___x_2139_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2006_, v_options_2005_, v___x_2138_);
if (v___x_2139_ == 0)
{
v___y_2116_ = v_a_1940_;
v___y_2117_ = v_a_1941_;
v___y_2118_ = v_a_1942_;
v___y_2119_ = v_a_1943_;
goto v___jp_2115_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___y_2144_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
lean_inc(v_name_1988_);
v___x_2140_ = l_Lean_MessageData_ofName(v_name_1988_);
v___x_2141_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17);
v___x_2142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2159_ = lean_box(0);
v___x_2160_ = lean_array_get_size(v_buckets_2002_);
v___x_2161_ = lean_nat_dec_lt(v___x_1994_, v___x_2160_);
if (v___x_2161_ == 0)
{
v___y_2144_ = v___x_2159_;
goto v___jp_2143_;
}
else
{
size_t v___x_2162_; size_t v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = lean_usize_of_nat(v___x_2160_);
v___x_2163_ = ((size_t)0ULL);
v___x_2164_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_buckets_2002_, v___x_2162_, v___x_2163_, v___x_2159_);
v___y_2144_ = v___x_2164_;
goto v___jp_2143_;
}
v___jp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2145_ = lean_box(0);
v___x_2146_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(v___y_2144_, v___x_2145_);
v___x_2147_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(v___x_2146_, v___x_2145_);
v___x_2148_ = l_Lean_MessageData_ofList(v___x_2147_);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2142_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v___x_2137_, v___x_2149_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_dec_ref_known(v___x_2150_, 1);
v___y_2116_ = v_a_1940_;
v___y_2117_ = v_a_1941_;
v___y_2118_ = v_a_1942_;
v___y_2119_ = v_a_1943_;
goto v___jp_2115_;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_a_1997_);
lean_dec_ref(v_params_1991_);
lean_dec_ref(v_type_1990_);
lean_dec(v_levelParams_1989_);
lean_dec(v_name_1988_);
lean_dec_ref(v_code_1987_);
lean_dec(v_inlineAttr_x3f_1986_);
lean_dec_ref_known(v_value_1983_, 1);
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
}
v___jp_2009_:
{
if (lean_obj_tag(v___y_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_a_2022_ = lean_ctor_get(v___y_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___y_2021_, 1);
v___x_2023_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1);
v___x_2024_ = lean_st_mk_ref(v___x_2023_);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v___y_2020_, v___y_2016_, v_params_1991_, v___x_2003_, v___x_2024_, v___y_2018_, v___y_2014_, v___y_2013_, v___y_2019_);
if (lean_obj_tag(v___x_2025_) == 0)
{
if (v___x_2008_ == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; size_t v_sz_2031_; lean_object* v___x_2032_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc_n(v_a_2026_, 2);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_2028_ = lean_array_get_size(v_a_2026_);
v___x_2029_ = l_Array_toSubarray___redArg(v_a_2026_, v___x_1994_, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2027_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v_sz_2031_ = lean_array_size(v___y_2015_);
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v___y_2015_, v_sz_2031_, v___y_2016_, v___x_2030_);
lean_dec_ref(v___y_2015_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v_fst_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v_fst_2034_ = lean_ctor_get(v_a_2033_, 0);
lean_inc(v_fst_2034_);
lean_dec(v_a_2033_);
v___x_2035_ = lean_box(0);
v___x_2036_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___y_2011_, v___y_2010_, v_name_1988_, v_levelParams_1989_, v_type_1990_, v_a_2026_, v_safe_1992_, v___x_2003_, v___x_2035_, v_fst_2034_, v___x_2003_, v___x_2024_, v___y_2018_, v___y_2014_, v___y_2013_, v___y_2019_);
v___y_1946_ = v___y_2012_;
v___y_1947_ = v___y_2014_;
v___y_1948_ = v___y_2017_;
v___y_1949_ = v___x_2024_;
v___y_1950_ = v_a_2022_;
v___y_1951_ = v___x_2036_;
goto v___jp_1945_;
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_a_2026_);
lean_dec(v___x_2024_);
lean_dec(v_a_2022_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2011_);
lean_dec_ref(v_type_1990_);
lean_dec(v_levelParams_1989_);
lean_dec(v_name_1988_);
v_a_2037_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2032_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2032_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec_ref(v___y_2015_);
v_a_2045_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2046_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5));
v___x_2047_ = lean_box(0);
v___x_2048_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___y_2011_, v___y_2010_, v_name_1988_, v_levelParams_1989_, v_type_1990_, v_a_2045_, v_safe_1992_, v___x_2003_, v___x_2047_, v___x_2046_, v___x_2003_, v___x_2024_, v___y_2018_, v___y_2014_, v___y_2013_, v___y_2019_);
v___y_1946_ = v___y_2012_;
v___y_1947_ = v___y_2014_;
v___y_1948_ = v___y_2017_;
v___y_1949_ = v___x_2024_;
v___y_1950_ = v_a_2022_;
v___y_1951_ = v___x_2048_;
goto v___jp_1945_;
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v___x_2024_);
lean_dec(v_a_2022_);
lean_dec_ref(v___y_2017_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2011_);
lean_dec_ref(v_type_1990_);
lean_dec(v_levelParams_1989_);
lean_dec(v_name_1988_);
v_a_2049_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2025_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2025_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v___y_2017_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2011_);
lean_dec_ref(v_params_1991_);
lean_dec_ref(v_type_1990_);
lean_dec(v_levelParams_1989_);
lean_dec(v_name_1988_);
v_a_2057_ = lean_ctor_get(v___y_2021_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___y_2021_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___y_2021_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___y_2021_);
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
v___jp_2065_:
{
lean_object* v___x_2079_; 
lean_inc(v___y_2076_);
lean_inc_ref(v___y_2069_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2075_);
v___x_2079_ = lean_apply_6(v___y_2074_, v___y_2078_, v___y_2075_, v___y_2070_, v___y_2069_, v___y_2076_, lean_box(0));
v___y_2010_ = v___y_2066_;
v___y_2011_ = v___y_2067_;
v___y_2012_ = v___y_2068_;
v___y_2013_ = v___y_2069_;
v___y_2014_ = v___y_2070_;
v___y_2015_ = v___y_2072_;
v___y_2016_ = v___y_2071_;
v___y_2017_ = v___y_2073_;
v___y_2018_ = v___y_2075_;
v___y_2019_ = v___y_2076_;
v___y_2020_ = v___y_2077_;
v___y_2021_ = v___x_2079_;
goto v___jp_2009_;
}
v___jp_2080_:
{
if (v___x_2008_ == 0)
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_2093_ = lean_nat_dec_lt(v___x_1994_, v___x_1993_);
if (v___x_2093_ == 0)
{
lean_dec(v_a_1997_);
v___y_2066_ = v___y_2081_;
v___y_2067_ = v___y_2089_;
v___y_2068_ = v___y_2081_;
v___y_2069_ = v___y_2083_;
v___y_2070_ = v___y_2082_;
v___y_2071_ = v___y_2085_;
v___y_2072_ = v___y_2084_;
v___y_2073_ = v___y_2091_;
v___y_2074_ = v___y_2086_;
v___y_2075_ = v___y_2087_;
v___y_2076_ = v___y_2088_;
v___y_2077_ = v___y_2090_;
v___y_2078_ = v___x_2092_;
goto v___jp_2065_;
}
else
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_nat_dec_le(v___x_1993_, v___x_1993_);
if (v___x_2094_ == 0)
{
if (v___x_2093_ == 0)
{
lean_dec(v_a_1997_);
v___y_2066_ = v___y_2081_;
v___y_2067_ = v___y_2089_;
v___y_2068_ = v___y_2081_;
v___y_2069_ = v___y_2083_;
v___y_2070_ = v___y_2082_;
v___y_2071_ = v___y_2085_;
v___y_2072_ = v___y_2084_;
v___y_2073_ = v___y_2091_;
v___y_2074_ = v___y_2086_;
v___y_2075_ = v___y_2087_;
v___y_2076_ = v___y_2088_;
v___y_2077_ = v___y_2090_;
v___y_2078_ = v___x_2092_;
goto v___jp_2065_;
}
else
{
size_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_usize_of_nat(v___x_1993_);
v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1997_, v_params_1991_, v___y_2085_, v___x_2095_, v___x_2092_);
lean_dec(v_a_1997_);
v___y_2066_ = v___y_2081_;
v___y_2067_ = v___y_2089_;
v___y_2068_ = v___y_2081_;
v___y_2069_ = v___y_2083_;
v___y_2070_ = v___y_2082_;
v___y_2071_ = v___y_2085_;
v___y_2072_ = v___y_2084_;
v___y_2073_ = v___y_2091_;
v___y_2074_ = v___y_2086_;
v___y_2075_ = v___y_2087_;
v___y_2076_ = v___y_2088_;
v___y_2077_ = v___y_2090_;
v___y_2078_ = v___x_2096_;
goto v___jp_2065_;
}
}
else
{
size_t v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_usize_of_nat(v___x_1993_);
v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1997_, v_params_1991_, v___y_2085_, v___x_2097_, v___x_2092_);
lean_dec(v_a_1997_);
v___y_2066_ = v___y_2081_;
v___y_2067_ = v___y_2089_;
v___y_2068_ = v___y_2081_;
v___y_2069_ = v___y_2083_;
v___y_2070_ = v___y_2082_;
v___y_2071_ = v___y_2085_;
v___y_2072_ = v___y_2084_;
v___y_2073_ = v___y_2091_;
v___y_2074_ = v___y_2086_;
v___y_2075_ = v___y_2087_;
v___y_2076_ = v___y_2088_;
v___y_2077_ = v___y_2090_;
v___y_2078_ = v___x_2098_;
goto v___jp_2065_;
}
}
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
lean_dec(v_a_1997_);
v___x_2099_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4));
v___x_2100_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7);
v___x_2101_ = l_Lean_Compiler_LCNF_mkParam(v___y_2081_, v___x_2099_, v___x_2100_, v___x_2003_, v___y_2087_, v___y_2082_, v___y_2083_, v___y_2088_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = lean_unsigned_to_nat(1u);
v___x_2104_ = lean_mk_empty_array_with_capacity(v___x_2103_);
v___x_2105_ = lean_array_push(v___x_2104_, v_a_2102_);
lean_inc(v___y_2088_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2087_);
v___x_2106_ = lean_apply_6(v___y_2086_, v___x_2105_, v___y_2087_, v___y_2082_, v___y_2083_, v___y_2088_, lean_box(0));
v___y_2010_ = v___y_2081_;
v___y_2011_ = v___y_2089_;
v___y_2012_ = v___y_2081_;
v___y_2013_ = v___y_2083_;
v___y_2014_ = v___y_2082_;
v___y_2015_ = v___y_2084_;
v___y_2016_ = v___y_2085_;
v___y_2017_ = v___y_2091_;
v___y_2018_ = v___y_2087_;
v___y_2019_ = v___y_2088_;
v___y_2020_ = v___y_2090_;
v___y_2021_ = v___x_2106_;
goto v___jp_2009_;
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2086_);
lean_dec_ref(v___y_2084_);
lean_dec_ref(v_params_1991_);
lean_dec_ref(v_type_1990_);
lean_dec(v_levelParams_1989_);
lean_dec(v_name_1988_);
v_a_2107_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2101_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2101_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
v___jp_2115_:
{
size_t v_sz_2120_; size_t v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___f_2128_; uint8_t v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_sz_2120_ = lean_array_size(v_params_1991_);
v___x_2121_ = ((size_t)0ULL);
lean_inc_ref(v_params_1991_);
v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1997_, v_sz_2120_, v___x_2121_, v_params_1991_);
v___x_2123_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9));
lean_inc_n(v_name_1988_, 2);
v___x_2124_ = l_Lean_Name_append(v_name_1988_, v___x_2123_);
v___x_2125_ = lean_box(v___x_2008_);
v___x_2126_ = lean_box(v_safe_1992_);
v___x_2127_ = lean_box(v_recursive_1985_);
lean_inc_ref(v___x_2122_);
lean_inc(v___x_2124_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2128_, 0, v_name_1988_);
lean_closure_set(v___f_2128_, 1, v___x_2124_);
lean_closure_set(v___f_2128_, 2, v___x_2122_);
lean_closure_set(v___f_2128_, 3, v___x_2125_);
lean_closure_set(v___f_2128_, 4, v_value_1983_);
lean_closure_set(v___f_2128_, 5, v_code_1987_);
lean_closure_set(v___f_2128_, 6, v___x_2126_);
lean_closure_set(v___f_2128_, 7, v___x_2127_);
lean_closure_set(v___f_2128_, 8, v_inlineAttr_x3f_1986_);
v___x_2129_ = 0;
v___x_2130_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_2131_ = lean_nat_dec_lt(v___x_1994_, v___x_1993_);
if (v___x_2131_ == 0)
{
v___y_2081_ = v___x_2129_;
v___y_2082_ = v___y_2117_;
v___y_2083_ = v___y_2118_;
v___y_2084_ = v___x_2122_;
v___y_2085_ = v___x_2121_;
v___y_2086_ = v___f_2128_;
v___y_2087_ = v___y_2116_;
v___y_2088_ = v___y_2119_;
v___y_2089_ = v___x_2124_;
v___y_2090_ = v_sz_2120_;
v___y_2091_ = v___x_2130_;
goto v___jp_2080_;
}
else
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_nat_dec_le(v___x_1993_, v___x_1993_);
if (v___x_2132_ == 0)
{
if (v___x_2131_ == 0)
{
v___y_2081_ = v___x_2129_;
v___y_2082_ = v___y_2117_;
v___y_2083_ = v___y_2118_;
v___y_2084_ = v___x_2122_;
v___y_2085_ = v___x_2121_;
v___y_2086_ = v___f_2128_;
v___y_2087_ = v___y_2116_;
v___y_2088_ = v___y_2119_;
v___y_2089_ = v___x_2124_;
v___y_2090_ = v_sz_2120_;
v___y_2091_ = v___x_2130_;
goto v___jp_2080_;
}
else
{
size_t v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = lean_usize_of_nat(v___x_1993_);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1997_, v_params_1991_, v___x_2121_, v___x_2133_, v___x_2130_);
v___y_2081_ = v___x_2129_;
v___y_2082_ = v___y_2117_;
v___y_2083_ = v___y_2118_;
v___y_2084_ = v___x_2122_;
v___y_2085_ = v___x_2121_;
v___y_2086_ = v___f_2128_;
v___y_2087_ = v___y_2116_;
v___y_2088_ = v___y_2119_;
v___y_2089_ = v___x_2124_;
v___y_2090_ = v_sz_2120_;
v___y_2091_ = v___x_2134_;
goto v___jp_2080_;
}
}
else
{
size_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_usize_of_nat(v___x_1993_);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1997_, v_params_1991_, v___x_2121_, v___x_2135_, v___x_2130_);
v___y_2081_ = v___x_2129_;
v___y_2082_ = v___y_2117_;
v___y_2083_ = v___y_2118_;
v___y_2084_ = v___x_2122_;
v___y_2085_ = v___x_2121_;
v___y_2086_ = v___f_2128_;
v___y_2087_ = v___y_2116_;
v___y_2088_ = v___y_2119_;
v___y_2089_ = v___x_2124_;
v___y_2090_ = v_sz_2120_;
v___y_2091_ = v___x_2136_;
goto v___jp_2080_;
}
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
lean_dec(v_a_1997_);
lean_dec_ref(v_code_1987_);
lean_dec_ref_known(v_value_1983_, 1);
v___x_2165_ = lean_unsigned_to_nat(1u);
v___x_2166_ = lean_mk_empty_array_with_capacity(v___x_2165_);
v___x_2167_ = lean_array_push(v___x_2166_, v_decl_1939_);
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_2167_);
v___x_2169_ = v___x_1999_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v_code_1987_);
lean_dec_ref_known(v_value_1983_, 1);
lean_dec_ref(v_decl_1939_);
v_a_2172_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_1996_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_1996_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
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
lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2189_; 
v_isSharedCheck_2189_ = !lean_is_exclusive(v_value_1983_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; 
v_unused_2190_ = lean_ctor_get(v_value_1983_, 0);
lean_dec(v_unused_2190_);
v___x_2181_ = v_value_1983_;
v_isShared_2182_ = v_isSharedCheck_2189_;
goto v_resetjp_2180_;
}
else
{
lean_dec(v_value_1983_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2189_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2183_ = lean_unsigned_to_nat(1u);
v___x_2184_ = lean_mk_empty_array_with_capacity(v___x_2183_);
v___x_2185_ = lean_array_push(v___x_2184_, v_decl_1939_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2185_);
v___x_2187_ = v___x_2181_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2200_; 
v_isSharedCheck_2200_ = !lean_is_exclusive(v_value_1983_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; 
v_unused_2201_ = lean_ctor_get(v_value_1983_, 0);
lean_dec(v_unused_2201_);
v___x_2192_ = v_value_1983_;
v_isShared_2193_ = v_isSharedCheck_2200_;
goto v_resetjp_2191_;
}
else
{
lean_dec(v_value_1983_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2200_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_mk_empty_array_with_capacity(v___x_2194_);
v___x_2196_ = lean_array_push(v___x_2195_, v_decl_1939_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set_tag(v___x_2192_, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2196_);
v___x_2198_ = v___x_2192_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
v___jp_1945_:
{
if (lean_obj_tag(v___y_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_a_1952_ = lean_ctor_get(v___y_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___y_1951_, 1);
v___x_1953_ = lean_st_ref_get(v___y_1949_);
lean_dec(v___y_1949_);
lean_dec(v___x_1953_);
v___x_1954_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___y_1946_, v___y_1948_, v___y_1947_);
lean_dec_ref(v___y_1948_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1965_; 
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1954_, 0);
lean_dec(v_unused_1966_);
v___x_1956_ = v___x_1954_;
v_isShared_1957_ = v_isSharedCheck_1965_;
goto v_resetjp_1955_;
}
else
{
lean_dec(v___x_1954_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1965_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1958_ = lean_unsigned_to_nat(2u);
v___x_1959_ = lean_mk_empty_array_with_capacity(v___x_1958_);
v___x_1960_ = lean_array_push(v___x_1959_, v___y_1950_);
v___x_1961_ = lean_array_push(v___x_1960_, v_a_1952_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1961_);
v___x_1963_ = v___x_1956_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_a_1952_);
lean_dec_ref(v___y_1950_);
v_a_1967_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1954_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1954_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
v_a_1975_ = lean_ctor_get(v___y_1951_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___y_1951_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___y_1951_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___y_1951_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object* v_decl_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v_decl_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
return v_res_2208_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* v_00_u03b2_2209_, lean_object* v_m_2210_, lean_object* v_a_2211_){
_start:
{
uint8_t v___x_2212_; 
v___x_2212_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_2210_, v_a_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* v_00_u03b2_2213_, lean_object* v_m_2214_, lean_object* v_a_2215_){
_start:
{
uint8_t v_res_2216_; lean_object* v_r_2217_; 
v_res_2216_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(v_00_u03b2_2213_, v_m_2214_, v_a_2215_);
lean_dec(v_a_2215_);
lean_dec_ref(v_m_2214_);
v_r_2217_ = lean_box(v_res_2216_);
return v_r_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* v_as_2218_, size_t v_sz_2219_, size_t v_i_2220_, lean_object* v_b_2221_, uint8_t v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_2218_, v_sz_2219_, v_i_2220_, v_b_2221_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* v_as_2230_, lean_object* v_sz_2231_, lean_object* v_i_2232_, lean_object* v_b_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
size_t v_sz_boxed_2241_; size_t v_i_boxed_2242_; uint8_t v___y_13031__boxed_2243_; lean_object* v_res_2244_; 
v_sz_boxed_2241_ = lean_unbox_usize(v_sz_2231_);
lean_dec(v_sz_2231_);
v_i_boxed_2242_ = lean_unbox_usize(v_i_2232_);
lean_dec(v_i_2232_);
v___y_13031__boxed_2243_ = lean_unbox(v___y_2234_);
v_res_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_2230_, v_sz_boxed_2241_, v_i_boxed_2242_, v_b_2233_, v___y_13031__boxed_2243_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v_as_2230_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* v_as_2245_, size_t v_i_2246_, size_t v_stop_2247_, lean_object* v_b_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_a_2255_; uint8_t v___x_2259_; 
v___x_2259_ = lean_usize_dec_eq(v_i_2246_, v_stop_2247_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = lean_array_uget_borrowed(v_as_2245_, v_i_2246_);
lean_inc(v___x_2260_);
v___x_2261_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v___x_2260_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2263_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
v___x_2263_ = l_Array_append___redArg(v_b_2248_, v_a_2262_);
lean_dec(v_a_2262_);
v_a_2255_ = v___x_2263_;
goto v___jp_2254_;
}
else
{
lean_dec_ref(v_b_2248_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2264_; 
v_a_2264_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2264_);
lean_dec_ref_known(v___x_2261_, 1);
v_a_2255_ = v_a_2264_;
goto v___jp_2254_;
}
else
{
return v___x_2261_;
}
}
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_b_2248_);
return v___x_2265_;
}
v___jp_2254_:
{
size_t v___x_2256_; size_t v___x_2257_; 
v___x_2256_ = ((size_t)1ULL);
v___x_2257_ = lean_usize_add(v_i_2246_, v___x_2256_);
v_i_2246_ = v___x_2257_;
v_b_2248_ = v_a_2255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* v_as_2266_, lean_object* v_i_2267_, lean_object* v_stop_2268_, lean_object* v_b_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
size_t v_i_boxed_2275_; size_t v_stop_boxed_2276_; lean_object* v_res_2277_; 
v_i_boxed_2275_ = lean_unbox_usize(v_i_2267_);
lean_dec(v_i_2267_);
v_stop_boxed_2276_ = lean_unbox_usize(v_stop_2268_);
lean_dec(v_stop_2268_);
v_res_2277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_2266_, v_i_boxed_2275_, v_stop_boxed_2276_, v_b_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_as_2266_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* v___x_2278_, lean_object* v_decls_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2285_ = lean_mk_empty_array_with_capacity(v___x_2278_);
v___x_2286_ = lean_array_get_size(v_decls_2279_);
v___x_2287_ = lean_nat_dec_lt(v___x_2278_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2285_);
return v___x_2288_;
}
else
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_nat_dec_le(v___x_2286_, v___x_2286_);
if (v___x_2289_ == 0)
{
if (v___x_2287_ == 0)
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2285_);
return v___x_2290_;
}
else
{
size_t v___x_2291_; size_t v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = ((size_t)0ULL);
v___x_2292_ = lean_usize_of_nat(v___x_2286_);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2279_, v___x_2291_, v___x_2292_, v___x_2285_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2293_;
}
}
else
{
size_t v___x_2294_; size_t v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = ((size_t)0ULL);
v___x_2295_ = lean_usize_of_nat(v___x_2286_);
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2279_, v___x_2294_, v___x_2295_, v___x_2285_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* v___x_2297_, lean_object* v_decls_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(v___x_2297_, v_decls_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec_ref(v_decls_2298_);
lean_dec(v___x_2297_);
return v_res_2304_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = lean_unsigned_to_nat(2803462840u);
v___x_2368_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2369_ = l_Lean_Name_num___override(v___x_2368_, v___x_2367_);
return v___x_2369_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2372_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2373_ = l_Lean_Name_str___override(v___x_2372_, v___x_2371_);
return v___x_2373_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2376_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2377_ = l_Lean_Name_str___override(v___x_2376_, v___x_2375_);
return v___x_2377_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_unsigned_to_nat(2u);
v___x_2379_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2380_ = l_Lean_Name_num___override(v___x_2379_, v___x_2378_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2382_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_2383_ = 1;
v___x_2384_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2385_ = l_Lean_registerTraceClass(v___x_2382_, v___x_2383_, v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
return v_res_2387_;
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
