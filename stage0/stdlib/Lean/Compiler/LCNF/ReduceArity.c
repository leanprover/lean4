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
size_t v___x_395_; size_t v___x_396_; lean_object* v___x_397_; 
v___x_395_ = ((size_t)0ULL);
v___x_396_ = lean_usize_of_nat(v___x_391_);
v___x_397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_372_, v___x_395_, v___x_396_, v___x_392_, v_a_360_, v_a_361_);
lean_dec_ref(v_args_372_);
return v___x_397_;
}
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; size_t v_sz_401_; size_t v___x_402_; lean_object* v___x_403_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_array_get_size(v_args_372_);
lean_inc_ref(v_args_372_);
v___x_400_ = l_Array_toSubarray___redArg(v_args_372_, v___x_398_, v___x_399_);
v_sz_401_ = lean_array_size(v_params_374_);
v___x_402_ = ((size_t)0ULL);
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_params_374_, v_sz_401_, v___x_402_, v___x_400_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_lower_405_; lean_object* v_upper_406_; lean_object* v___x_412_; uint8_t v___x_413_; 
lean_dec_ref_known(v___x_403_, 1);
v___x_412_ = lean_array_get_size(v_params_374_);
v___x_413_ = lean_nat_dec_le(v___x_412_, v___x_398_);
if (v___x_413_ == 0)
{
v_lower_405_ = v___x_412_;
v_upper_406_ = v___x_399_;
goto v___jp_404_;
}
else
{
v_lower_405_ = v___x_398_;
v_upper_406_ = v___x_399_;
goto v___jp_404_;
}
v___jp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = l_Array_toSubarray___redArg(v_args_372_, v_lower_405_, v_upper_406_);
v___x_408_ = lean_box(0);
v___x_409_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v___x_407_, v___x_408_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
lean_dec_ref_known(v___x_409_, 1);
v___x_410_ = lean_array_get_size(v_params_374_);
v___x_411_ = lean_nat_dec_le(v___x_399_, v___x_398_);
if (v___x_411_ == 0)
{
v___y_376_ = v___x_408_;
v_lower_377_ = v___x_399_;
v_upper_378_ = v___x_410_;
goto v___jp_375_;
}
else
{
v___y_376_ = v___x_408_;
v_lower_377_ = v___x_398_;
v_upper_378_ = v___x_410_;
goto v___jp_375_;
}
}
else
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v_args_372_);
v_a_414_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_403_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_403_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
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
lean_object* v_fvarId_422_; lean_object* v_args_423_; lean_object* v___x_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_438_; 
v_fvarId_422_ = lean_ctor_get(v_e_359_, 0);
lean_inc(v_fvarId_422_);
v_args_423_ = lean_ctor_get(v_e_359_, 1);
lean_inc_ref(v_args_423_);
lean_dec_ref_known(v_e_359_, 2);
v___x_424_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_422_, v_a_360_, v_a_361_);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v___x_424_, 0);
lean_dec(v_unused_439_);
v___x_426_ = v___x_424_;
v_isShared_427_ = v_isSharedCheck_438_;
goto v_resetjp_425_;
}
else
{
lean_dec(v___x_424_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_438_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_array_get_size(v_args_423_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_nat_dec_lt(v___x_428_, v___x_429_);
if (v___x_431_ == 0)
{
lean_object* v___x_433_; 
lean_dec_ref(v_args_423_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_430_);
v___x_433_ = v___x_426_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_430_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
else
{
size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
lean_del_object(v___x_426_);
v___x_435_ = ((size_t)0ULL);
v___x_436_ = lean_usize_of_nat(v___x_429_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_423_, v___x_435_, v___x_436_, v___x_430_, v_a_360_, v_a_361_);
lean_dec_ref(v_args_423_);
return v___x_437_;
}
}
}
default: 
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v_e_359_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object* v_e_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_e_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object* v_as_451_, size_t v_i_452_, size_t v_stop_453_, lean_object* v_b_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_451_, v_i_452_, v_stop_453_, v_b_454_, v___y_455_, v___y_456_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object* v_as_463_, lean_object* v_i_464_, lean_object* v_stop_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
size_t v_i_boxed_474_; size_t v_stop_boxed_475_; lean_object* v_res_476_; 
v_i_boxed_474_ = lean_unbox_usize(v_i_464_);
lean_dec(v_i_464_);
v_stop_boxed_475_ = lean_unbox_usize(v_stop_465_);
lean_dec(v_stop_465_);
v_res_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(v_as_463_, v_i_boxed_474_, v_stop_boxed_475_, v_b_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec_ref(v_as_463_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object* v_as_477_, size_t v_sz_478_, size_t v_i_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_477_, v_sz_478_, v_i_479_, v_b_480_, v___y_481_, v___y_482_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object* v_as_489_, lean_object* v_sz_490_, lean_object* v_i_491_, lean_object* v_b_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
size_t v_sz_boxed_500_; size_t v_i_boxed_501_; lean_object* v_res_502_; 
v_sz_boxed_500_ = lean_unbox_usize(v_sz_490_);
lean_dec(v_sz_490_);
v_i_boxed_501_ = lean_unbox_usize(v_i_491_);
lean_dec(v_i_491_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(v_as_489_, v_sz_boxed_500_, v_i_boxed_501_, v_b_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object* v_inst_503_, lean_object* v_R_504_, lean_object* v_a_505_, lean_object* v_b_506_, lean_object* v_c_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_505_, v_b_506_, v___y_508_, v___y_509_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object* v_inst_516_, lean_object* v_R_517_, lean_object* v_a_518_, lean_object* v_b_519_, lean_object* v_c_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(v_inst_516_, v_R_517_, v_a_518_, v_b_519_, v_c_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object* v_inst_529_, lean_object* v_R_530_, lean_object* v_a_531_, lean_object* v_b_532_, lean_object* v_c_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_531_, v_b_532_, v___y_534_, v___y_535_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object* v_inst_542_, lean_object* v_R_543_, lean_object* v_a_544_, lean_object* v_b_545_, lean_object* v_c_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(v_inst_542_, v_R_543_, v_a_544_, v_b_545_, v_c_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object* v_code_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_decl_564_; lean_object* v_k_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; 
switch(lean_obj_tag(v_code_555_))
{
case 0:
{
lean_object* v_decl_575_; lean_object* v_k_576_; lean_object* v_value_577_; lean_object* v___x_578_; 
v_decl_575_ = lean_ctor_get(v_code_555_, 0);
lean_inc_ref(v_decl_575_);
v_k_576_ = lean_ctor_get(v_code_555_, 1);
lean_inc_ref(v_k_576_);
lean_dec_ref_known(v_code_555_, 2);
v_value_577_ = lean_ctor_get(v_decl_575_, 3);
lean_inc(v_value_577_);
lean_dec_ref(v_decl_575_);
v___x_578_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(v_value_577_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_dec_ref_known(v___x_578_, 1);
v_code_555_ = v_k_576_;
goto _start;
}
else
{
lean_dec_ref(v_k_576_);
return v___x_578_;
}
}
case 3:
{
lean_object* v_args_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v_args_580_ = lean_ctor_get(v_code_555_, 1);
lean_inc_ref(v_args_580_);
lean_dec_ref_known(v_code_555_, 2);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_array_get_size(v_args_580_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_nat_dec_lt(v___x_581_, v___x_582_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_dec_ref(v_args_580_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
return v___x_585_;
}
else
{
size_t v___x_586_; size_t v___x_587_; lean_object* v___x_588_; 
v___x_586_ = ((size_t)0ULL);
v___x_587_ = lean_usize_of_nat(v___x_582_);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_580_, v___x_586_, v___x_587_, v___x_583_, v_a_556_, v_a_557_);
lean_dec_ref(v_args_580_);
return v___x_588_;
}
}
case 4:
{
lean_object* v_cases_589_; lean_object* v_discr_590_; lean_object* v_alts_591_; lean_object* v___x_592_; 
v_cases_589_ = lean_ctor_get(v_code_555_, 0);
lean_inc_ref(v_cases_589_);
lean_dec_ref_known(v_code_555_, 1);
v_discr_590_ = lean_ctor_get(v_cases_589_, 2);
lean_inc(v_discr_590_);
v_alts_591_ = lean_ctor_get(v_cases_589_, 3);
lean_inc_ref(v_alts_591_);
lean_dec_ref(v_cases_589_);
v___x_592_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_discr_590_, v_a_556_, v_a_557_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_606_; 
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v___x_592_, 0);
lean_dec(v_unused_607_);
v___x_594_ = v___x_592_;
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
else
{
lean_dec(v___x_592_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_array_get_size(v_alts_591_);
v___x_598_ = lean_box(0);
v___x_599_ = lean_nat_dec_lt(v___x_596_, v___x_597_);
if (v___x_599_ == 0)
{
lean_object* v___x_601_; 
lean_dec_ref(v_alts_591_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_598_);
v___x_601_ = v___x_594_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_598_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
else
{
size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; 
lean_del_object(v___x_594_);
v___x_603_ = ((size_t)0ULL);
v___x_604_ = lean_usize_of_nat(v___x_597_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_591_, v___x_603_, v___x_604_, v___x_598_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec_ref(v_alts_591_);
return v___x_605_;
}
}
}
else
{
lean_dec_ref(v_alts_591_);
return v___x_592_;
}
}
case 5:
{
lean_object* v_fvarId_608_; lean_object* v___x_609_; 
v_fvarId_608_ = lean_ctor_get(v_code_555_, 0);
lean_inc(v_fvarId_608_);
lean_dec_ref_known(v_code_555_, 1);
v___x_609_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_608_, v_a_556_, v_a_557_);
return v___x_609_;
}
case 6:
{
lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_617_; 
v_isSharedCheck_617_ = !lean_is_exclusive(v_code_555_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v_code_555_, 0);
lean_dec(v_unused_618_);
v___x_611_ = v_code_555_;
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
else
{
lean_dec(v_code_555_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_617_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_box(0);
if (v_isShared_612_ == 0)
{
lean_ctor_set_tag(v___x_611_, 0);
lean_ctor_set(v___x_611_, 0, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
default: 
{
lean_object* v_decl_619_; lean_object* v_k_620_; 
v_decl_619_ = lean_ctor_get(v_code_555_, 0);
lean_inc_ref(v_decl_619_);
v_k_620_ = lean_ctor_get(v_code_555_, 1);
lean_inc_ref(v_k_620_);
lean_dec_ref(v_code_555_);
v_decl_564_ = v_decl_619_;
v_k_565_ = v_k_620_;
v___y_566_ = v_a_556_;
v___y_567_ = v_a_557_;
v___y_568_ = v_a_558_;
v___y_569_ = v_a_559_;
v___y_570_ = v_a_560_;
v___y_571_ = v_a_561_;
goto v___jp_563_;
}
}
v___jp_563_:
{
lean_object* v_value_572_; lean_object* v___x_573_; 
v_value_572_ = lean_ctor_get(v_decl_564_, 4);
lean_inc_ref(v_value_572_);
lean_dec_ref(v_decl_564_);
v___x_573_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_value_572_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_dec_ref_known(v___x_573_, 1);
v_code_555_ = v_k_565_;
v_a_556_ = v___y_566_;
v_a_557_ = v___y_567_;
v_a_558_ = v___y_568_;
v_a_559_ = v___y_569_;
v_a_560_ = v___y_570_;
v_a_561_ = v___y_571_;
goto _start;
}
else
{
lean_dec_ref(v_k_565_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object* v_as_621_, size_t v_i_622_, size_t v_stop_623_, lean_object* v_b_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___y_633_; uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_eq(v_i_622_, v_stop_623_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_array_uget_borrowed(v_as_621_, v_i_622_);
switch(lean_obj_tag(v___x_640_))
{
case 0:
{
lean_object* v_code_641_; 
v_code_641_ = lean_ctor_get(v___x_640_, 2);
lean_inc_ref(v_code_641_);
v___y_633_ = v_code_641_;
goto v___jp_632_;
}
case 1:
{
lean_object* v_code_642_; 
v_code_642_ = lean_ctor_get(v___x_640_, 1);
lean_inc_ref(v_code_642_);
v___y_633_ = v_code_642_;
goto v___jp_632_;
}
default: 
{
lean_object* v_code_643_; 
v_code_643_ = lean_ctor_get(v___x_640_, 0);
lean_inc_ref(v_code_643_);
v___y_633_ = v_code_643_;
goto v___jp_632_;
}
}
}
else
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v_b_624_);
return v___x_644_;
}
v___jp_632_:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Compiler_LCNF_FindUsed_visit(v___y_633_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; size_t v___x_636_; size_t v___x_637_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_add(v_i_622_, v___x_636_);
v_i_622_ = v___x_637_;
v_b_624_ = v_a_635_;
goto _start;
}
else
{
return v___x_634_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object* v_as_645_, lean_object* v_i_646_, lean_object* v_stop_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
size_t v_i_boxed_656_; size_t v_stop_boxed_657_; lean_object* v_res_658_; 
v_i_boxed_656_ = lean_unbox_usize(v_i_646_);
lean_dec(v_i_646_);
v_stop_boxed_657_ = lean_unbox_usize(v_stop_647_);
lean_dec(v_stop_647_);
v_res_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_as_645_, v_i_boxed_656_, v_stop_boxed_657_, v_b_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v_as_645_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object* v_code_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Compiler_LCNF_FindUsed_visit(v_code_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(lean_object* v_f_668_, lean_object* v_v_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
if (lean_obj_tag(v_v_669_) == 0)
{
lean_object* v_code_677_; lean_object* v___x_678_; 
v_code_677_ = lean_ctor_get(v_v_669_, 0);
lean_inc_ref(v_code_677_);
lean_dec_ref_known(v_v_669_, 1);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
lean_inc(v___y_671_);
lean_inc_ref(v___y_670_);
v___x_678_ = lean_apply_8(v_f_668_, v_code_677_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, lean_box(0));
return v___x_678_;
}
else
{
lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_f_668_);
v_isSharedCheck_686_ = !lean_is_exclusive(v_v_669_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v_v_669_, 0);
lean_dec(v_unused_687_);
v___x_680_ = v_v_669_;
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
else
{
lean_dec(v_v_669_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_682_ = lean_box(0);
if (v_isShared_681_ == 0)
{
lean_ctor_set_tag(v___x_680_, 0);
lean_ctor_set(v___x_680_, 0, v___x_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg___boxed(lean_object* v_f_688_, lean_object* v_v_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_688_, v_v_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(uint8_t v_pu_698_, lean_object* v_f_699_, lean_object* v_v_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_699_, v_v_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___boxed(lean_object* v_pu_709_, lean_object* v_f_710_, lean_object* v_v_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v_pu_boxed_719_; lean_object* v_res_720_; 
v_pu_boxed_719_ = lean_unbox(v_pu_709_);
v_res_720_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(v_pu_boxed_719_, v_f_710_, v_v_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object* v_as_721_, size_t v_i_722_, size_t v_stop_723_, lean_object* v_b_724_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = lean_usize_dec_eq(v_i_722_, v_stop_723_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v_fvarId_727_; lean_object* v___x_728_; size_t v___x_729_; size_t v___x_730_; 
v___x_726_ = lean_array_uget_borrowed(v_as_721_, v_i_722_);
v_fvarId_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_fvarId_727_);
v___x_728_ = l_Lean_FVarIdSet_insert(v_b_724_, v_fvarId_727_);
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_i_722_, v___x_729_);
v_i_722_ = v___x_730_;
v_b_724_ = v___x_728_;
goto _start;
}
else
{
return v_b_724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object* v_as_732_, lean_object* v_i_733_, lean_object* v_stop_734_, lean_object* v_b_735_){
_start:
{
size_t v_i_boxed_736_; size_t v_stop_boxed_737_; lean_object* v_res_738_; 
v_i_boxed_736_ = lean_unbox_usize(v_i_733_);
lean_dec(v_i_733_);
v_stop_boxed_737_ = lean_unbox_usize(v_stop_734_);
lean_dec(v_stop_734_);
v_res_738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_as_732_, v_i_boxed_736_, v_stop_boxed_737_, v_b_735_);
lean_dec_ref(v_as_732_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object* v_decl_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_toSignature_746_; lean_object* v_value_747_; lean_object* v_params_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___y_752_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_toSignature_746_ = lean_ctor_get(v_decl_740_, 0);
v_value_747_ = lean_ctor_get(v_decl_740_, 1);
lean_inc_ref(v_value_747_);
v_params_748_ = lean_ctor_get(v_toSignature_746_, 3);
v___x_749_ = lean_box(1);
v___x_750_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_array_get_size(v_params_748_);
v___x_776_ = lean_nat_dec_lt(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
v___y_752_ = v___x_749_;
goto v___jp_751_;
}
else
{
size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
v___x_777_ = ((size_t)0ULL);
v___x_778_ = lean_usize_of_nat(v___x_775_);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_748_, v___x_777_, v___x_778_, v___x_749_);
v___y_752_ = v___x_779_;
goto v___jp_751_;
}
v___jp_751_:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_753_ = ((lean_object*)(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0));
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_decl_740_);
lean_ctor_set(v___x_754_, 1, v___y_752_);
v___x_755_ = lean_st_mk_ref(v___x_750_);
v___x_756_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v___x_753_, v_value_747_, v___x_754_, v___x_755_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec_ref_known(v___x_754_, 2);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_764_; 
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v___x_756_, 0);
lean_dec(v_unused_765_);
v___x_758_ = v___x_756_;
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
else
{
lean_dec(v___x_756_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = lean_st_ref_get(v___x_755_);
lean_dec(v___x_755_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v___x_755_);
v_a_766_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_756_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_756_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(lean_object* v_decl_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
return v_res_786_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0(void){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object* v_msg_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0);
v___x_790_ = lean_panic_fn_borrowed(v___x_789_, v_msg_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(lean_object* v_args_791_, lean_object* v_upperBound_792_, lean_object* v___x_793_, lean_object* v_a_794_, lean_object* v_b_795_){
_start:
{
lean_object* v_a_798_; uint8_t v___x_805_; 
v___x_805_ = lean_nat_dec_lt(v_a_794_, v_upperBound_792_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec(v_a_794_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v_b_795_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_array_get_size(v___x_793_);
v___x_808_ = lean_nat_dec_lt(v_a_794_, v___x_807_);
if (v___x_808_ == 0)
{
goto v___jp_802_;
}
else
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = lean_array_fget_borrowed(v___x_793_, v_a_794_);
v___x_810_ = lean_unbox(v___x_809_);
if (v___x_810_ == 0)
{
v_a_798_ = v_b_795_;
goto v___jp_797_;
}
else
{
goto v___jp_802_;
}
}
}
v___jp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_a_794_, v___x_799_);
lean_dec(v_a_794_);
v_a_794_ = v___x_800_;
v_b_795_ = v_a_798_;
goto _start;
}
v___jp_802_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_array_fget_borrowed(v_args_791_, v_a_794_);
lean_inc(v___x_803_);
v___x_804_ = lean_array_push(v_b_795_, v___x_803_);
v_a_798_ = v___x_804_;
goto v___jp_797_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(lean_object* v_args_811_, lean_object* v_upperBound_812_, lean_object* v___x_813_, lean_object* v_a_814_, lean_object* v_b_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_811_, v_upperBound_812_, v___x_813_, v_a_814_, v_b_815_);
lean_dec_ref(v___x_813_);
lean_dec(v_upperBound_812_);
lean_dec_ref(v_args_811_);
return v_res_817_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_821_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2));
v___x_822_ = lean_unsigned_to_nat(9u);
v___x_823_ = lean_unsigned_to_nat(650u);
v___x_824_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1));
v___x_825_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0));
v___x_826_ = l_mkPanicMessageWithDecl(v___x_825_, v___x_824_, v___x_823_, v___x_822_, v___x_821_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* v_code_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_decl_841_; lean_object* v_k_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; 
switch(lean_obj_tag(v_code_833_))
{
case 0:
{
lean_object* v_decl_955_; lean_object* v_k_956_; lean_object* v_argsNew_958_; lean_object* v___y_959_; lean_object* v_auxDeclName_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v_value_1017_; 
v_decl_955_ = lean_ctor_get(v_code_833_, 0);
v_k_956_ = lean_ctor_get(v_code_833_, 1);
v_value_1017_ = lean_ctor_get(v_decl_955_, 3);
if (lean_obj_tag(v_value_1017_) == 3)
{
lean_object* v_declName_1018_; lean_object* v_args_1019_; lean_object* v_declName_1020_; lean_object* v_auxDeclName_1021_; lean_object* v_paramMask_1022_; uint8_t v_allUnused_1023_; uint8_t v___x_1024_; 
v_declName_1018_ = lean_ctor_get(v_value_1017_, 0);
v_args_1019_ = lean_ctor_get(v_value_1017_, 2);
v_declName_1020_ = lean_ctor_get(v_a_834_, 0);
v_auxDeclName_1021_ = lean_ctor_get(v_a_834_, 1);
v_paramMask_1022_ = lean_ctor_get(v_a_834_, 2);
v_allUnused_1023_ = lean_ctor_get_uint8(v_a_834_, sizeof(void*)*3);
v___x_1024_ = lean_name_eq(v_declName_1018_, v_declName_1020_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_inc_ref(v_k_956_);
v___x_1025_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_956_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1063_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1063_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1063_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
size_t v___x_1030_; size_t v___x_1031_; uint8_t v___x_1032_; 
v___x_1030_ = lean_ptr_addr(v_k_956_);
v___x_1031_ = lean_ptr_addr(v_a_1026_);
v___x_1032_ = lean_usize_dec_eq(v___x_1030_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1042_; 
lean_inc_ref(v_decl_955_);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; lean_object* v_unused_1044_; 
v_unused_1043_ = lean_ctor_get(v_code_833_, 1);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_1044_);
v___x_1034_ = v_code_833_;
v_isShared_1035_ = v_isSharedCheck_1042_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v_code_833_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1042_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v_a_1026_);
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_decl_955_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_a_1026_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1037_);
v___x_1039_ = v___x_1028_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
size_t v___x_1045_; size_t v___x_1046_; uint8_t v___x_1047_; 
v___x_1045_ = lean_ptr_addr(v_decl_955_);
v___x_1046_ = lean_ptr_addr(v_decl_955_);
v___x_1047_ = lean_usize_dec_eq(v___x_1045_, v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1057_; 
lean_inc_ref(v_decl_955_);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; lean_object* v_unused_1059_; 
v_unused_1058_ = lean_ctor_get(v_code_833_, 1);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_1059_);
v___x_1049_ = v_code_833_;
v_isShared_1050_ = v_isSharedCheck_1057_;
goto v_resetjp_1048_;
}
else
{
lean_dec(v_code_833_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1057_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v_a_1026_);
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_decl_955_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_a_1026_);
v___x_1052_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1052_);
v___x_1054_ = v___x_1028_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_object* v___x_1061_; 
lean_dec(v_a_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v_code_833_);
v___x_1061_ = v___x_1028_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_code_833_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_833_, 2);
return v___x_1025_;
}
}
else
{
if (v_allUnused_1023_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1064_ = lean_array_get_size(v_args_1019_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_1067_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1019_, v___x_1064_, v_paramMask_1022_, v___x_1065_, v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v_argsNew_958_ = v_a_1068_;
v___y_959_ = v_a_834_;
v_auxDeclName_960_ = v_auxDeclName_1021_;
v___y_961_ = v_a_835_;
v___y_962_ = v_a_836_;
v___y_963_ = v_a_837_;
v___y_964_ = v_a_838_;
goto v___jp_957_;
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref_known(v_code_833_, 2);
v_a_1069_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1067_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1067_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1077_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5));
v___x_1078_ = lean_array_get_size(v_paramMask_1022_);
v___x_1079_ = lean_array_get_size(v_args_1019_);
v___x_1080_ = l_Array_extract___redArg(v_args_1019_, v___x_1078_, v___x_1079_);
v___x_1081_ = l_Array_append___redArg(v___x_1077_, v___x_1080_);
lean_dec_ref(v___x_1080_);
v_argsNew_958_ = v___x_1081_;
v___y_959_ = v_a_834_;
v_auxDeclName_960_ = v_auxDeclName_1021_;
v___y_961_ = v_a_835_;
v___y_962_ = v_a_836_;
v___y_963_ = v_a_837_;
v___y_964_ = v_a_838_;
goto v___jp_957_;
}
}
}
else
{
lean_object* v___x_1082_; 
lean_inc_ref(v_k_956_);
v___x_1082_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_956_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1120_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1120_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1120_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
size_t v___x_1087_; size_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = lean_ptr_addr(v_k_956_);
v___x_1088_ = lean_ptr_addr(v_a_1083_);
v___x_1089_ = lean_usize_dec_eq(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1099_; 
lean_inc_ref(v_decl_955_);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; lean_object* v_unused_1101_; 
v_unused_1100_ = lean_ctor_get(v_code_833_, 1);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_1101_);
v___x_1091_ = v_code_833_;
v_isShared_1092_ = v_isSharedCheck_1099_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v_code_833_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1099_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v_a_1083_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_decl_955_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_a_1083_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1096_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1094_);
v___x_1096_ = v___x_1085_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
size_t v___x_1102_; size_t v___x_1103_; uint8_t v___x_1104_; 
v___x_1102_ = lean_ptr_addr(v_decl_955_);
v___x_1103_ = lean_ptr_addr(v_decl_955_);
v___x_1104_ = lean_usize_dec_eq(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1114_; 
lean_inc_ref(v_decl_955_);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; lean_object* v_unused_1116_; 
v_unused_1115_ = lean_ctor_get(v_code_833_, 1);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_1116_);
v___x_1106_ = v_code_833_;
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
else
{
lean_dec(v_code_833_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v_a_1083_);
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_decl_955_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_a_1083_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1109_);
v___x_1111_ = v___x_1085_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
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
lean_object* v___x_1118_; 
lean_dec(v_a_1083_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v_code_833_);
v___x_1118_ = v___x_1085_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_code_833_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_833_, 2);
return v___x_1082_;
}
}
v___jp_957_:
{
uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_965_ = 0;
v___x_966_ = lean_box(0);
lean_inc(v_auxDeclName_960_);
v___x_967_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_967_, 0, v_auxDeclName_960_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
lean_ctor_set(v___x_967_, 2, v_argsNew_958_);
lean_inc_ref(v_decl_955_);
v___x_968_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_965_, v_decl_955_, v___x_967_, v___y_962_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
lean_inc_ref(v_k_956_);
v___x_970_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_956_, v___y_959_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1008_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_1008_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1008_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
size_t v___x_975_; size_t v___x_976_; uint8_t v___x_977_; 
v___x_975_ = lean_ptr_addr(v_k_956_);
v___x_976_ = lean_ptr_addr(v_a_971_);
v___x_977_ = lean_usize_dec_eq(v___x_975_, v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_987_; 
v_isSharedCheck_987_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; lean_object* v_unused_989_; 
v_unused_988_ = lean_ctor_get(v_code_833_, 1);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_989_);
v___x_979_ = v_code_833_;
v_isShared_980_ = v_isSharedCheck_987_;
goto v_resetjp_978_;
}
else
{
lean_dec(v_code_833_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_987_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v_a_971_);
lean_ctor_set(v___x_979_, 0, v_a_969_);
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_969_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_a_971_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_984_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_982_);
v___x_984_ = v___x_973_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
size_t v___x_990_; size_t v___x_991_; uint8_t v___x_992_; 
v___x_990_ = lean_ptr_addr(v_decl_955_);
v___x_991_ = lean_ptr_addr(v_a_969_);
v___x_992_ = lean_usize_dec_eq(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1002_; 
v_isSharedCheck_1002_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; lean_object* v_unused_1004_; 
v_unused_1003_ = lean_ctor_get(v_code_833_, 1);
lean_dec(v_unused_1003_);
v_unused_1004_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_1004_);
v___x_994_ = v_code_833_;
v_isShared_995_ = v_isSharedCheck_1002_;
goto v_resetjp_993_;
}
else
{
lean_dec(v_code_833_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1002_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v_a_971_);
lean_ctor_set(v___x_994_, 0, v_a_969_);
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_969_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_a_971_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_997_);
v___x_999_ = v___x_973_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_object* v___x_1006_; 
lean_dec(v_a_971_);
lean_dec(v_a_969_);
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v_code_833_);
v___x_1006_ = v___x_973_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_code_833_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
else
{
lean_dec(v_a_969_);
lean_dec_ref_known(v_code_833_, 2);
return v___x_970_;
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref_known(v_code_833_, 2);
v_a_1009_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_968_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_968_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1121_; lean_object* v_k_1122_; 
v_decl_1121_ = lean_ctor_get(v_code_833_, 0);
v_k_1122_ = lean_ctor_get(v_code_833_, 1);
lean_inc_ref(v_k_1122_);
lean_inc_ref(v_decl_1121_);
v_decl_841_ = v_decl_1121_;
v_k_842_ = v_k_1122_;
v___y_843_ = v_a_834_;
v___y_844_ = v_a_835_;
v___y_845_ = v_a_836_;
v___y_846_ = v_a_837_;
v___y_847_ = v_a_838_;
goto v___jp_840_;
}
case 2:
{
lean_object* v_decl_1123_; lean_object* v_k_1124_; 
v_decl_1123_ = lean_ctor_get(v_code_833_, 0);
v_k_1124_ = lean_ctor_get(v_code_833_, 1);
lean_inc_ref(v_k_1124_);
lean_inc_ref(v_decl_1123_);
v_decl_841_ = v_decl_1123_;
v_k_842_ = v_k_1124_;
v___y_843_ = v_a_834_;
v___y_844_ = v_a_835_;
v___y_845_ = v_a_836_;
v___y_846_ = v_a_837_;
v___y_847_ = v_a_838_;
goto v___jp_840_;
}
case 4:
{
lean_object* v_cases_1125_; lean_object* v_typeName_1126_; lean_object* v_resultType_1127_; lean_object* v_discr_1128_; lean_object* v_alts_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1168_; 
v_cases_1125_ = lean_ctor_get(v_code_833_, 0);
lean_inc_ref(v_cases_1125_);
v_typeName_1126_ = lean_ctor_get(v_cases_1125_, 0);
v_resultType_1127_ = lean_ctor_get(v_cases_1125_, 1);
v_discr_1128_ = lean_ctor_get(v_cases_1125_, 2);
v_alts_1129_ = lean_ctor_get(v_cases_1125_, 3);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_cases_1125_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1131_ = v_cases_1125_;
v_isShared_1132_ = v_isSharedCheck_1168_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_alts_1129_);
lean_inc(v_discr_1128_);
lean_inc(v_resultType_1127_);
lean_inc(v_typeName_1126_);
lean_dec(v_cases_1125_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1168_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1129_);
v___x_1134_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v___x_1133_, v_alts_1129_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1159_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1159_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1159_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
size_t v___x_1139_; size_t v___x_1140_; uint8_t v___x_1141_; 
v___x_1139_ = lean_ptr_addr(v_alts_1129_);
lean_dec_ref(v_alts_1129_);
v___x_1140_ = lean_ptr_addr(v_a_1135_);
v___x_1141_ = lean_usize_dec_eq(v___x_1139_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1154_; 
v_isSharedCheck_1154_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_1155_);
v___x_1143_ = v_code_833_;
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
else
{
lean_dec(v_code_833_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 3, v_a_1135_);
v___x_1146_ = v___x_1131_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_typeName_1126_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_resultType_1127_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_discr_1128_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_a_1135_);
v___x_1146_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1146_);
v___x_1148_ = v___x_1143_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1150_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1148_);
v___x_1150_ = v___x_1137_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_a_1135_);
lean_del_object(v___x_1131_);
lean_dec(v_discr_1128_);
lean_dec_ref(v_resultType_1127_);
lean_dec(v_typeName_1126_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v_code_833_);
v___x_1157_ = v___x_1137_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_code_833_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_del_object(v___x_1131_);
lean_dec_ref(v_alts_1129_);
lean_dec(v_discr_1128_);
lean_dec_ref(v_resultType_1127_);
lean_dec(v_typeName_1126_);
lean_dec_ref_known(v_code_833_, 1);
v_a_1160_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1134_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1134_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
default: 
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_code_833_);
return v___x_1169_;
}
}
v___jp_840_:
{
lean_object* v_params_848_; lean_object* v_type_849_; lean_object* v_value_850_; uint8_t v___x_851_; lean_object* v___x_852_; 
v_params_848_ = lean_ctor_get(v_decl_841_, 2);
lean_inc_ref(v_params_848_);
v_type_849_ = lean_ctor_get(v_decl_841_, 3);
lean_inc_ref(v_type_849_);
v_value_850_ = lean_ctor_get(v_decl_841_, 4);
v___x_851_ = 0;
lean_inc_ref(v_value_850_);
v___x_852_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_value_850_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_851_, v_decl_841_, v_type_849_, v_params_848_, v_a_853_, v___y_845_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_k_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_856_) == 0)
{
switch(lean_obj_tag(v_code_833_))
{
case 1:
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_896_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_896_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_896_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_896_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_decl_861_; lean_object* v_k_862_; size_t v___x_863_; size_t v___x_864_; uint8_t v___x_865_; 
v_decl_861_ = lean_ctor_get(v_code_833_, 0);
v_k_862_ = lean_ctor_get(v_code_833_, 1);
v___x_863_ = lean_ptr_addr(v_k_862_);
v___x_864_ = lean_ptr_addr(v_a_857_);
v___x_865_ = lean_usize_dec_eq(v___x_863_, v___x_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_875_; 
v_isSharedCheck_875_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; lean_object* v_unused_877_; 
v_unused_876_ = lean_ctor_get(v_code_833_, 1);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_877_);
v___x_867_ = v_code_833_;
v_isShared_868_ = v_isSharedCheck_875_;
goto v_resetjp_866_;
}
else
{
lean_dec(v_code_833_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_875_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v_a_857_);
lean_ctor_set(v___x_867_, 0, v_a_855_);
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_855_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_a_857_);
v___x_870_ = v_reuseFailAlloc_874_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_870_);
v___x_872_ = v___x_859_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
size_t v___x_878_; size_t v___x_879_; uint8_t v___x_880_; 
v___x_878_ = lean_ptr_addr(v_decl_861_);
v___x_879_ = lean_ptr_addr(v_a_855_);
v___x_880_ = lean_usize_dec_eq(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_890_; 
v_isSharedCheck_890_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; lean_object* v_unused_892_; 
v_unused_891_ = lean_ctor_get(v_code_833_, 1);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_892_);
v___x_882_ = v_code_833_;
v_isShared_883_ = v_isSharedCheck_890_;
goto v_resetjp_881_;
}
else
{
lean_dec(v_code_833_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_890_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v_a_857_);
lean_ctor_set(v___x_882_, 0, v_a_855_);
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_855_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_a_857_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_885_);
v___x_887_ = v___x_859_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v___x_894_; 
lean_dec(v_a_857_);
lean_dec(v_a_855_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v_code_833_);
v___x_894_ = v___x_859_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_code_833_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
case 2:
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_936_; 
v_a_897_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_936_ == 0)
{
v___x_899_ = v___x_856_;
v_isShared_900_ = v_isSharedCheck_936_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_856_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_936_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_decl_901_; lean_object* v_k_902_; size_t v___x_903_; size_t v___x_904_; uint8_t v___x_905_; 
v_decl_901_ = lean_ctor_get(v_code_833_, 0);
v_k_902_ = lean_ctor_get(v_code_833_, 1);
v___x_903_ = lean_ptr_addr(v_k_902_);
v___x_904_ = lean_ptr_addr(v_a_897_);
v___x_905_ = lean_usize_dec_eq(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_915_; 
v_isSharedCheck_915_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; lean_object* v_unused_917_; 
v_unused_916_ = lean_ctor_get(v_code_833_, 1);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_917_);
v___x_907_ = v_code_833_;
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
else
{
lean_dec(v_code_833_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 1, v_a_897_);
lean_ctor_set(v___x_907_, 0, v_a_855_);
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_855_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_a_897_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_910_);
v___x_912_ = v___x_899_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
size_t v___x_918_; size_t v___x_919_; uint8_t v___x_920_; 
v___x_918_ = lean_ptr_addr(v_decl_901_);
v___x_919_ = lean_ptr_addr(v_a_855_);
v___x_920_ = lean_usize_dec_eq(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_930_; 
v_isSharedCheck_930_ = !lean_is_exclusive(v_code_833_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; lean_object* v_unused_932_; 
v_unused_931_ = lean_ctor_get(v_code_833_, 1);
lean_dec(v_unused_931_);
v_unused_932_ = lean_ctor_get(v_code_833_, 0);
lean_dec(v_unused_932_);
v___x_922_ = v_code_833_;
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
else
{
lean_dec(v_code_833_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_930_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v_a_897_);
lean_ctor_set(v___x_922_, 0, v_a_855_);
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_855_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_a_897_);
v___x_925_ = v_reuseFailAlloc_929_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_927_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_925_);
v___x_927_ = v___x_899_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v___x_934_; 
lean_dec(v_a_897_);
lean_dec(v_a_855_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v_code_833_);
v___x_934_ = v___x_899_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_code_833_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
default: 
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_a_855_);
lean_dec_ref(v_code_833_);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v___x_856_, 0);
lean_dec(v_unused_946_);
v___x_938_ = v___x_856_;
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
else
{
lean_dec(v___x_856_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_945_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = lean_obj_once(&l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3, &l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once, _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3);
v___x_941_ = l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(v___x_940_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_941_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
else
{
lean_dec(v_a_855_);
lean_dec_ref(v_code_833_);
return v___x_856_;
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v_k_842_);
lean_dec_ref(v_code_833_);
v_a_947_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_854_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_854_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
else
{
lean_dec_ref(v_type_849_);
lean_dec_ref(v_params_848_);
lean_dec_ref(v_k_842_);
lean_dec_ref(v_decl_841_);
lean_dec_ref(v_code_833_);
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(lean_object* v_i_1170_, lean_object* v_as_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_array_get_size(v_as_1171_);
v___x_1179_ = lean_nat_dec_lt(v_i_1170_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
lean_dec(v_i_1170_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_as_1171_);
return v___x_1180_;
}
else
{
lean_object* v_a_1181_; lean_object* v___y_1183_; 
v_a_1181_ = lean_array_fget_borrowed(v_as_1171_, v_i_1170_);
switch(lean_obj_tag(v_a_1181_))
{
case 0:
{
lean_object* v_code_1205_; 
v_code_1205_ = lean_ctor_get(v_a_1181_, 2);
lean_inc_ref(v_code_1205_);
v___y_1183_ = v_code_1205_;
goto v___jp_1182_;
}
case 1:
{
lean_object* v_code_1206_; 
v_code_1206_ = lean_ctor_get(v_a_1181_, 1);
lean_inc_ref(v_code_1206_);
v___y_1183_ = v_code_1206_;
goto v___jp_1182_;
}
default: 
{
lean_object* v_code_1207_; 
v_code_1207_ = lean_ctor_get(v_a_1181_, 0);
lean_inc_ref(v_code_1207_);
v___y_1183_ = v_code_1207_;
goto v___jp_1182_;
}
}
v___jp_1182_:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v___y_1183_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; uint8_t v___x_1189_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
lean_inc(v_a_1181_);
v___x_1186_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1181_, v_a_1185_);
v___x_1187_ = lean_ptr_addr(v_a_1181_);
v___x_1188_ = lean_ptr_addr(v___x_1186_);
v___x_1189_ = lean_usize_dec_eq(v___x_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_nat_add(v_i_1170_, v___x_1190_);
v___x_1192_ = lean_array_fset(v_as_1171_, v_i_1170_, v___x_1186_);
lean_dec(v_i_1170_);
v_i_1170_ = v___x_1191_;
v_as_1171_ = v___x_1192_;
goto _start;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec_ref(v___x_1186_);
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_add(v_i_1170_, v___x_1194_);
lean_dec(v_i_1170_);
v_i_1170_ = v___x_1195_;
goto _start;
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v_as_1171_);
lean_dec(v_i_1170_);
v_a_1197_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1184_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1184_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(lean_object* v_i_1208_, lean_object* v_as_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v_i_1208_, v_as_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object* v_code_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(v_code_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec_ref(v_a_1218_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object* v_args_1225_, lean_object* v_upperBound_1226_, lean_object* v___x_1227_, lean_object* v_inst_1228_, lean_object* v_R_1229_, lean_object* v_a_1230_, lean_object* v_b_1231_, lean_object* v_c_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_1225_, v_upperBound_1226_, v___x_1227_, v_a_1230_, v_b_1231_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object* v_args_1240_, lean_object* v_upperBound_1241_, lean_object* v___x_1242_, lean_object* v_inst_1243_, lean_object* v_R_1244_, lean_object* v_a_1245_, lean_object* v_b_1246_, lean_object* v_c_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(v_args_1240_, v_upperBound_1241_, v___x_1242_, v_inst_1243_, v_R_1244_, v_a_1245_, v_b_1246_, v_c_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec_ref(v___x_1242_);
lean_dec(v_upperBound_1241_);
lean_dec_ref(v_args_1240_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object* v_f_1255_, lean_object* v_v_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
if (lean_obj_tag(v_v_1256_) == 0)
{
lean_object* v_code_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1287_; 
v_code_1263_ = lean_ctor_get(v_v_1256_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_v_1256_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1265_ = v_v_1256_;
v_isShared_1266_ = v_isSharedCheck_1287_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_code_1263_);
lean_dec(v_v_1256_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1287_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; 
lean_inc(v___y_1261_);
lean_inc_ref(v___y_1260_);
lean_inc(v___y_1259_);
lean_inc_ref(v___y_1258_);
lean_inc_ref(v___y_1257_);
v___x_1267_ = lean_apply_7(v_f_1255_, v_code_1263_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, lean_box(0));
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1278_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v_a_1268_);
v___x_1273_ = v___x_1265_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v___x_1273_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_del_object(v___x_1265_);
v_a_1279_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1267_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1267_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
else
{
lean_object* v___x_1288_; 
lean_dec_ref(v_f_1255_);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_v_1256_);
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object* v_f_1289_, lean_object* v_v_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1289_, v_v_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec_ref(v___y_1291_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(uint8_t v_pu_1298_, lean_object* v_f_1299_, lean_object* v_v_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_1299_, v_v_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object* v_pu_1308_, lean_object* v_f_1309_, lean_object* v_v_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v_pu_boxed_1317_; lean_object* v_res_1318_; 
v_pu_boxed_1317_ = lean_unbox(v_pu_1308_);
v_res_1318_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(v_pu_boxed_1317_, v_f_1309_, v_v_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1318_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0(void){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1322_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1323_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1);
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
lean_ctor_set(v___x_1325_, 2, v___x_1324_);
lean_ctor_set(v___x_1325_, 3, v___x_1324_);
lean_ctor_set(v___x_1325_, 4, v___x_1323_);
lean_ctor_set(v___x_1325_, 5, v___x_1323_);
lean_ctor_set(v___x_1325_, 6, v___x_1323_);
lean_ctor_set(v___x_1325_, 7, v___x_1323_);
lean_ctor_set(v___x_1325_, 8, v___x_1323_);
lean_ctor_set(v___x_1325_, 9, v___x_1323_);
lean_ctor_set(v___x_1325_, 10, v___x_1323_);
lean_ctor_set(v___x_1325_, 11, v___x_1322_);
return v___x_1325_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3(void){
_start:
{
lean_object* v___x_1326_; double v___x_1327_; 
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = lean_float_of_nat(v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* v_cls_1331_, lean_object* v_msg_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_ref_1338_; lean_object* v___x_1339_; lean_object* v_env_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_ref_1338_ = lean_ctor_get(v___y_1335_, 2);
v___x_1339_ = lean_st_ref_get(v___y_1336_);
v_env_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc_ref(v_env_1340_);
lean_dec(v___x_1339_);
v___x_1341_ = lean_st_ref_get(v___y_1334_);
v___x_1342_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_1333_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1402_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1402_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1402_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_lctx_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1400_; 
v_lctx_1347_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1341_, 1);
lean_dec(v_unused_1401_);
v___x_1349_ = v___x_1341_;
v_isShared_1350_ = v_isSharedCheck_1400_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_lctx_1347_);
lean_dec(v___x_1341_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1400_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1351_ = lean_unbox(v_a_1343_);
lean_dec(v_a_1343_);
v___x_1352_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_1347_, v___x_1351_);
lean_dec_ref(v_lctx_1347_);
v___x_1353_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1335_);
v___x_1354_ = lean_obj_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2);
v___x_1355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1355_, 0, v_env_1340_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
lean_ctor_set(v___x_1355_, 2, v___x_1352_);
lean_ctor_set(v___x_1355_, 3, v___x_1353_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 3);
lean_ctor_set(v___x_1349_, 1, v_msg_1332_);
lean_ctor_set(v___x_1349_, 0, v___x_1355_);
v___x_1357_ = v___x_1349_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_msg_1332_);
v___x_1357_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v_traceState_1359_; lean_object* v_env_1360_; lean_object* v_nextMacroScope_1361_; lean_object* v_ngen_1362_; lean_object* v_auxDeclNGen_1363_; lean_object* v_cache_1364_; lean_object* v_recordedDeps_1365_; lean_object* v_messages_1366_; lean_object* v_infoState_1367_; lean_object* v_snapshotTasks_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1398_; 
v___x_1358_ = lean_st_ref_take(v___y_1336_);
v_traceState_1359_ = lean_ctor_get(v___x_1358_, 4);
v_env_1360_ = lean_ctor_get(v___x_1358_, 0);
v_nextMacroScope_1361_ = lean_ctor_get(v___x_1358_, 1);
v_ngen_1362_ = lean_ctor_get(v___x_1358_, 2);
v_auxDeclNGen_1363_ = lean_ctor_get(v___x_1358_, 3);
v_cache_1364_ = lean_ctor_get(v___x_1358_, 5);
v_recordedDeps_1365_ = lean_ctor_get(v___x_1358_, 6);
v_messages_1366_ = lean_ctor_get(v___x_1358_, 7);
v_infoState_1367_ = lean_ctor_get(v___x_1358_, 8);
v_snapshotTasks_1368_ = lean_ctor_get(v___x_1358_, 9);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1370_ = v___x_1358_;
v_isShared_1371_ = v_isSharedCheck_1398_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_snapshotTasks_1368_);
lean_inc(v_infoState_1367_);
lean_inc(v_messages_1366_);
lean_inc(v_recordedDeps_1365_);
lean_inc(v_cache_1364_);
lean_inc(v_traceState_1359_);
lean_inc(v_auxDeclNGen_1363_);
lean_inc(v_ngen_1362_);
lean_inc(v_nextMacroScope_1361_);
lean_inc(v_env_1360_);
lean_dec(v___x_1358_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1398_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
uint64_t v_tid_1372_; lean_object* v_traces_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1397_; 
v_tid_1372_ = lean_ctor_get_uint64(v_traceState_1359_, sizeof(void*)*1);
v_traces_1373_ = lean_ctor_get(v_traceState_1359_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_traceState_1359_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1375_ = v_traceState_1359_;
v_isShared_1376_ = v_isSharedCheck_1397_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_traces_1373_);
lean_dec(v_traceState_1359_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1397_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; double v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3, &l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once, _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3);
v___x_1380_ = 0;
v___x_1381_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4));
v___x_1382_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1382_, 0, v_cls_1331_);
lean_ctor_set(v___x_1382_, 1, v___x_1378_);
lean_ctor_set(v___x_1382_, 2, v___x_1381_);
lean_ctor_set_float(v___x_1382_, sizeof(void*)*3, v___x_1379_);
lean_ctor_set_float(v___x_1382_, sizeof(void*)*3 + 8, v___x_1379_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*3 + 16, v___x_1380_);
v___x_1383_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5));
v___x_1384_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set(v___x_1384_, 1, v___x_1357_);
lean_ctor_set(v___x_1384_, 2, v___x_1383_);
lean_inc(v_ref_1338_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v_ref_1338_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = l_Lean_PersistentArray_push___redArg(v_traces_1373_, v___x_1385_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1386_);
v___x_1388_ = v___x_1375_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1386_);
lean_ctor_set_uint64(v_reuseFailAlloc_1396_, sizeof(void*)*1, v_tid_1372_);
v___x_1388_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1390_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v___x_1388_);
v___x_1390_ = v___x_1370_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_env_1360_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_nextMacroScope_1361_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_ngen_1362_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_auxDeclNGen_1363_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1395_, 5, v_cache_1364_);
lean_ctor_set(v_reuseFailAlloc_1395_, 6, v_recordedDeps_1365_);
lean_ctor_set(v_reuseFailAlloc_1395_, 7, v_messages_1366_);
lean_ctor_set(v_reuseFailAlloc_1395_, 8, v_infoState_1367_);
lean_ctor_set(v_reuseFailAlloc_1395_, 9, v_snapshotTasks_1368_);
v___x_1390_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = lean_st_ref_put(v___y_1336_, v___x_1390_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1377_);
v___x_1393_ = v___x_1345_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1377_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
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
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v___x_1341_);
lean_dec_ref(v_env_1340_);
lean_dec_ref(v_msg_1332_);
lean_dec(v_cls_1331_);
v_a_1403_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1342_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1342_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___boxed(lean_object* v_cls_1411_, lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v_cls_1411_, v_msg_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(lean_object* v_name_1420_, lean_object* v___x_1421_, lean_object* v___x_1422_, uint8_t v___x_1423_, lean_object* v_value_1424_, lean_object* v_code_1425_, uint8_t v_safe_1426_, uint8_t v_recursive_1427_, lean_object* v_inlineAttr_x3f_1428_, lean_object* v_params_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_inc(v___x_1421_);
v___x_1435_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1435_, 0, v_name_1420_);
lean_ctor_set(v___x_1435_, 1, v___x_1421_);
lean_ctor_set(v___x_1435_, 2, v___x_1422_);
lean_ctor_set_uint8(v___x_1435_, sizeof(void*)*3, v___x_1423_);
v___x_1436_ = 0;
v___x_1437_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___closed__0));
v___x_1438_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v___x_1437_, v_value_1424_, v___x_1435_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec_ref_known(v___x_1435_, 3);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1440_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = l_Lean_Compiler_LCNF_Code_inferType(v___x_1436_, v_code_1425_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1442_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
lean_inc_ref(v_params_1429_);
v___x_1442_ = l_Lean_Compiler_LCNF_mkForallParams(v___x_1436_, v_params_1429_, v_a_1441_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v_a_1441_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1445_, 0, v___x_1421_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
lean_ctor_set(v___x_1445_, 2, v_a_1443_);
lean_ctor_set(v___x_1445_, 3, v_params_1429_);
lean_ctor_set_uint8(v___x_1445_, sizeof(void*)*4, v_safe_1426_);
v___x_1446_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v_a_1439_);
lean_ctor_set(v___x_1446_, 2, v_inlineAttr_x3f_1428_);
lean_ctor_set_uint8(v___x_1446_, sizeof(void*)*3, v_recursive_1427_);
lean_inc_ref(v___x_1446_);
v___x_1447_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1446_, v___y_1433_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v___x_1447_, 0);
lean_dec(v_unused_1455_);
v___x_1449_ = v___x_1447_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v___x_1447_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1446_);
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1446_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec_ref_known(v___x_1446_, 3);
v_a_1456_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1447_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1447_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_a_1439_);
lean_dec_ref(v_params_1429_);
lean_dec(v_inlineAttr_x3f_1428_);
lean_dec(v___x_1421_);
v_a_1464_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1442_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1442_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_a_1439_);
lean_dec_ref(v_params_1429_);
lean_dec(v_inlineAttr_x3f_1428_);
lean_dec(v___x_1421_);
v_a_1472_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1440_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1440_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v_params_1429_);
lean_dec(v_inlineAttr_x3f_1428_);
lean_dec_ref(v_code_1425_);
lean_dec(v___x_1421_);
v_a_1480_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1438_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1438_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed(lean_object* v_name_1488_, lean_object* v___x_1489_, lean_object* v___x_1490_, lean_object* v___x_1491_, lean_object* v_value_1492_, lean_object* v_code_1493_, lean_object* v_safe_1494_, lean_object* v_recursive_1495_, lean_object* v_inlineAttr_x3f_1496_, lean_object* v_params_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v___x_11811__boxed_1503_; uint8_t v_safe_boxed_1504_; uint8_t v_recursive_boxed_1505_; lean_object* v_res_1506_; 
v___x_11811__boxed_1503_ = lean_unbox(v___x_1491_);
v_safe_boxed_1504_ = lean_unbox(v_safe_1494_);
v_recursive_boxed_1505_ = lean_unbox(v_recursive_1495_);
v_res_1506_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0(v_name_1488_, v___x_1489_, v___x_1490_, v___x_11811__boxed_1503_, v_value_1492_, v_code_1493_, v_safe_boxed_1504_, v_recursive_boxed_1505_, v_inlineAttr_x3f_1496_, v_params_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(lean_object* v___x_1513_, uint8_t v___x_1514_, lean_object* v_name_1515_, lean_object* v_levelParams_1516_, lean_object* v_type_1517_, lean_object* v_a_1518_, uint8_t v_safe_1519_, uint8_t v___x_1520_, lean_object* v_____r_1521_, lean_object* v_args_1522_, uint8_t v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1513_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
lean_ctor_set(v___x_1531_, 2, v_args_1522_);
v___x_1532_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__1));
v___x_1533_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_1514_, v___x_1531_, v___x_1532_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v_fvarId_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v_fvarId_1535_ = lean_ctor_get(v_a_1534_, 0);
lean_inc(v_fvarId_1535_);
v___x_1536_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1536_, 0, v_fvarId_1535_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_a_1534_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
v___x_1539_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1539_, 0, v_name_1515_);
lean_ctor_set(v___x_1539_, 1, v_levelParams_1516_);
lean_ctor_set(v___x_1539_, 2, v_type_1517_);
lean_ctor_set(v___x_1539_, 3, v_a_1518_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*4, v_safe_1519_);
v___x_1540_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___closed__2));
v___x_1541_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1538_);
lean_ctor_set(v___x_1541_, 2, v___x_1540_);
lean_ctor_set_uint8(v___x_1541_, sizeof(void*)*3, v___x_1520_);
lean_inc_ref(v___x_1541_);
v___x_1542_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1541_, v___y_1528_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v___x_1542_, 0);
lean_dec(v_unused_1550_);
v___x_1544_ = v___x_1542_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_dec(v___x_1542_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1541_);
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1541_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref_known(v___x_1541_, 3);
v_a_1551_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1542_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1542_);
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
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref(v_a_1518_);
lean_dec_ref(v_type_1517_);
lean_dec(v_levelParams_1516_);
lean_dec(v_name_1515_);
v_a_1559_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1533_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1533_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1___boxed(lean_object** _args){
lean_object* v___x_1567_ = _args[0];
lean_object* v___x_1568_ = _args[1];
lean_object* v_name_1569_ = _args[2];
lean_object* v_levelParams_1570_ = _args[3];
lean_object* v_type_1571_ = _args[4];
lean_object* v_a_1572_ = _args[5];
lean_object* v_safe_1573_ = _args[6];
lean_object* v___x_1574_ = _args[7];
lean_object* v_____r_1575_ = _args[8];
lean_object* v_args_1576_ = _args[9];
lean_object* v___y_1577_ = _args[10];
lean_object* v___y_1578_ = _args[11];
lean_object* v___y_1579_ = _args[12];
lean_object* v___y_1580_ = _args[13];
lean_object* v___y_1581_ = _args[14];
lean_object* v___y_1582_ = _args[15];
lean_object* v___y_1583_ = _args[16];
_start:
{
uint8_t v___x_11955__boxed_1584_; uint8_t v_safe_boxed_1585_; uint8_t v___x_11957__boxed_1586_; uint8_t v___y_11959__boxed_1587_; lean_object* v_res_1588_; 
v___x_11955__boxed_1584_ = lean_unbox(v___x_1568_);
v_safe_boxed_1585_ = lean_unbox(v_safe_1573_);
v___x_11957__boxed_1586_ = lean_unbox(v___x_1574_);
v___y_11959__boxed_1587_ = lean_unbox(v___y_1577_);
v_res_1588_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___x_1567_, v___x_11955__boxed_1584_, v_name_1569_, v_levelParams_1570_, v_type_1571_, v_a_1572_, v_safe_boxed_1585_, v___x_11957__boxed_1586_, v_____r_1575_, v_args_1576_, v___y_11959__boxed_1587_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
if (lean_obj_tag(v_x_1590_) == 0)
{
lean_inc(v_x_1589_);
return v_x_1589_;
}
else
{
lean_object* v_key_1591_; lean_object* v_tail_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_key_1591_ = lean_ctor_get(v_x_1590_, 0);
v_tail_1592_ = lean_ctor_get(v_x_1590_, 2);
v___x_1593_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1589_, v_tail_1592_);
lean_inc(v_key_1591_);
v___x_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1594_, 0, v_key_1591_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_1595_, v_x_1596_);
lean_dec(v_x_1596_);
lean_dec(v_x_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object* v_as_1598_, size_t v_i_1599_, size_t v_stop_1600_, lean_object* v_b_1601_){
_start:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_usize_dec_eq(v_i_1599_, v_stop_1600_);
if (v___x_1602_ == 0)
{
size_t v___x_1603_; size_t v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1603_ = ((size_t)1ULL);
v___x_1604_ = lean_usize_sub(v_i_1599_, v___x_1603_);
v___x_1605_ = lean_array_uget_borrowed(v_as_1598_, v___x_1604_);
v___x_1606_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_b_1601_, v___x_1605_);
lean_dec(v_b_1601_);
v_i_1599_ = v___x_1604_;
v_b_1601_ = v___x_1606_;
goto _start;
}
else
{
return v_b_1601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object* v_as_1608_, lean_object* v_i_1609_, lean_object* v_stop_1610_, lean_object* v_b_1611_){
_start:
{
size_t v_i_boxed_1612_; size_t v_stop_boxed_1613_; lean_object* v_res_1614_; 
v_i_boxed_1612_ = lean_unbox_usize(v_i_1609_);
lean_dec(v_i_1609_);
v_stop_boxed_1613_ = lean_unbox_usize(v_stop_1610_);
lean_dec(v_stop_1610_);
v_res_1614_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_as_1608_, v_i_boxed_1612_, v_stop_boxed_1613_, v_b_1611_);
lean_dec_ref(v_as_1608_);
return v_res_1614_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(lean_object* v_m_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_buckets_1617_; lean_object* v___x_1618_; uint64_t v___x_1619_; uint64_t v___x_1620_; uint64_t v___x_1621_; uint64_t v_fold_1622_; uint64_t v___x_1623_; uint64_t v___x_1624_; uint64_t v___x_1625_; size_t v___x_1626_; size_t v___x_1627_; size_t v___x_1628_; size_t v___x_1629_; size_t v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v_buckets_1617_ = lean_ctor_get(v_m_1615_, 1);
v___x_1618_ = lean_array_get_size(v_buckets_1617_);
v___x_1619_ = l_Lean_instHashableFVarId_hash(v_a_1616_);
v___x_1620_ = 32ULL;
v___x_1621_ = lean_uint64_shift_right(v___x_1619_, v___x_1620_);
v_fold_1622_ = lean_uint64_xor(v___x_1619_, v___x_1621_);
v___x_1623_ = 16ULL;
v___x_1624_ = lean_uint64_shift_right(v_fold_1622_, v___x_1623_);
v___x_1625_ = lean_uint64_xor(v_fold_1622_, v___x_1624_);
v___x_1626_ = lean_uint64_to_usize(v___x_1625_);
v___x_1627_ = lean_usize_of_nat(v___x_1618_);
v___x_1628_ = ((size_t)1ULL);
v___x_1629_ = lean_usize_sub(v___x_1627_, v___x_1628_);
v___x_1630_ = lean_usize_land(v___x_1626_, v___x_1629_);
v___x_1631_ = lean_array_uget_borrowed(v_buckets_1617_, v___x_1630_);
v___x_1632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_1616_, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(lean_object* v_m_1633_, lean_object* v_a_1634_){
_start:
{
uint8_t v_res_1635_; lean_object* v_r_1636_; 
v_res_1635_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_m_1633_);
v_r_1636_ = lean_box(v_res_1635_);
return v_r_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* v_a_1637_, lean_object* v_as_1638_, size_t v_i_1639_, size_t v_stop_1640_, lean_object* v_b_1641_){
_start:
{
lean_object* v___y_1643_; uint8_t v___x_1647_; 
v___x_1647_ = lean_usize_dec_eq(v_i_1639_, v_stop_1640_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v_fvarId_1649_; uint8_t v___x_1650_; 
v___x_1648_ = lean_array_uget_borrowed(v_as_1638_, v_i_1639_);
v_fvarId_1649_ = lean_ctor_get(v___x_1648_, 0);
v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1637_, v_fvarId_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; 
lean_inc(v___x_1648_);
v___x_1651_ = lean_array_push(v_b_1641_, v___x_1648_);
v___y_1643_ = v___x_1651_;
goto v___jp_1642_;
}
else
{
v___y_1643_ = v_b_1641_;
goto v___jp_1642_;
}
}
else
{
return v_b_1641_;
}
v___jp_1642_:
{
size_t v___x_1644_; size_t v___x_1645_; 
v___x_1644_ = ((size_t)1ULL);
v___x_1645_ = lean_usize_add(v_i_1639_, v___x_1644_);
v_i_1639_ = v___x_1645_;
v_b_1641_ = v___y_1643_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* v_a_1652_, lean_object* v_as_1653_, lean_object* v_i_1654_, lean_object* v_stop_1655_, lean_object* v_b_1656_){
_start:
{
size_t v_i_boxed_1657_; size_t v_stop_boxed_1658_; lean_object* v_res_1659_; 
v_i_boxed_1657_ = lean_unbox_usize(v_i_1654_);
lean_dec(v_i_1654_);
v_stop_boxed_1658_ = lean_unbox_usize(v_stop_1655_);
lean_dec(v_stop_1655_);
v_res_1659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1652_, v_as_1653_, v_i_boxed_1657_, v_stop_boxed_1658_, v_b_1656_);
lean_dec_ref(v_as_1653_);
lean_dec_ref(v_a_1652_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
if (lean_obj_tag(v_a_1660_) == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = l_List_reverse___redArg(v_a_1661_);
return v___x_1662_;
}
else
{
lean_object* v_head_1663_; lean_object* v_tail_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1673_; 
v_head_1663_ = lean_ctor_get(v_a_1660_, 0);
v_tail_1664_ = lean_ctor_get(v_a_1660_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_a_1660_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1666_ = v_a_1660_;
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_tail_1664_);
lean_inc(v_head_1663_);
lean_dec(v_a_1660_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = l_Lean_MessageData_ofExpr(v_head_1663_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v_a_1661_);
lean_ctor_set(v___x_1666_, 0, v___x_1668_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_a_1661_);
v___x_1670_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
v_a_1660_ = v_tail_1664_;
v_a_1661_ = v___x_1670_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(lean_object* v_as_1674_, size_t v_sz_1675_, size_t v_i_1676_, lean_object* v_b_1677_){
_start:
{
lean_object* v_a_1680_; uint8_t v___x_1684_; 
v___x_1684_ = lean_usize_dec_lt(v_i_1676_, v_sz_1675_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v_b_1677_);
return v___x_1685_;
}
else
{
lean_object* v_snd_1686_; lean_object* v_fst_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1722_; 
v_snd_1686_ = lean_ctor_get(v_b_1677_, 1);
v_fst_1687_ = lean_ctor_get(v_b_1677_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_b_1677_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1689_ = v_b_1677_;
v_isShared_1690_ = v_isSharedCheck_1722_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_snd_1686_);
lean_inc(v_fst_1687_);
lean_dec(v_b_1677_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1722_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v_array_1691_; lean_object* v_start_1692_; lean_object* v_stop_1693_; uint8_t v___x_1694_; 
v_array_1691_ = lean_ctor_get(v_snd_1686_, 0);
v_start_1692_ = lean_ctor_get(v_snd_1686_, 1);
v_stop_1693_ = lean_ctor_get(v_snd_1686_, 2);
v___x_1694_ = lean_nat_dec_lt(v_start_1692_, v_stop_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1696_; 
if (v_isShared_1690_ == 0)
{
v___x_1696_ = v___x_1689_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_fst_1687_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_snd_1686_);
v___x_1696_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
}
else
{
lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1718_; 
lean_inc(v_stop_1693_);
lean_inc(v_start_1692_);
lean_inc_ref(v_array_1691_);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_snd_1686_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; lean_object* v_unused_1720_; lean_object* v_unused_1721_; 
v_unused_1719_ = lean_ctor_get(v_snd_1686_, 2);
lean_dec(v_unused_1719_);
v_unused_1720_ = lean_ctor_get(v_snd_1686_, 1);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_snd_1686_, 0);
lean_dec(v_unused_1721_);
v___x_1700_ = v_snd_1686_;
v_isShared_1701_ = v_isSharedCheck_1718_;
goto v_resetjp_1699_;
}
else
{
lean_dec(v_snd_1686_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1718_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_a_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v_a_1702_ = lean_array_uget_borrowed(v_as_1674_, v_i_1676_);
v___x_1703_ = lean_array_fget(v_array_1691_, v_start_1692_);
v___x_1704_ = lean_unsigned_to_nat(1u);
v___x_1705_ = lean_nat_add(v_start_1692_, v___x_1704_);
lean_dec(v_start_1692_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v___x_1705_);
v___x_1707_ = v___x_1700_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_array_1691_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_stop_1693_);
v___x_1707_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_unbox(v_a_1702_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1710_; 
lean_dec(v___x_1703_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 1, v___x_1707_);
v___x_1710_ = v___x_1689_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_fst_1687_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___x_1707_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
v_a_1680_ = v___x_1710_;
goto v___jp_1679_;
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1712_ = l_Lean_Compiler_LCNF_Param_toArg___redArg(v___x_1703_);
lean_dec(v___x_1703_);
v___x_1713_ = lean_array_push(v_fst_1687_, v___x_1712_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 1, v___x_1707_);
lean_ctor_set(v___x_1689_, 0, v___x_1713_);
v___x_1715_ = v___x_1689_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1707_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
v_a_1680_ = v___x_1715_;
goto v___jp_1679_;
}
}
}
}
}
}
}
v___jp_1679_:
{
size_t v___x_1681_; size_t v___x_1682_; 
v___x_1681_ = ((size_t)1ULL);
v___x_1682_ = lean_usize_add(v_i_1676_, v___x_1681_);
v_i_1676_ = v___x_1682_;
v_b_1677_ = v_a_1680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(lean_object* v_as_1723_, lean_object* v_sz_1724_, lean_object* v_i_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_){
_start:
{
size_t v_sz_boxed_1728_; size_t v_i_boxed_1729_; lean_object* v_res_1730_; 
v_sz_boxed_1728_ = lean_unbox_usize(v_sz_1724_);
lean_dec(v_sz_1724_);
v_i_boxed_1729_ = lean_unbox_usize(v_i_1725_);
lean_dec(v_i_1725_);
v_res_1730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_1723_, v_sz_boxed_1728_, v_i_boxed_1729_, v_b_1726_);
lean_dec_ref(v_as_1723_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(size_t v_sz_1731_, size_t v_i_1732_, lean_object* v_bs_1733_, uint8_t v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_usize_dec_lt(v_i_1732_, v_sz_1731_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; 
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_bs_1733_);
return v___x_1742_;
}
else
{
uint8_t v___x_1743_; lean_object* v_v_1744_; lean_object* v___x_1745_; lean_object* v_bs_x27_1746_; lean_object* v___x_1747_; 
v___x_1743_ = 0;
v_v_1744_ = lean_array_uget(v_bs_1733_, v_i_1732_);
v___x_1745_ = lean_unsigned_to_nat(0u);
v_bs_x27_1746_ = lean_array_uset(v_bs_1733_, v_i_1732_, v___x_1745_);
v___x_1747_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(v___x_1743_, v_v_1744_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; size_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_add(v_i_1732_, v___x_1749_);
v___x_1751_ = lean_array_uset(v_bs_x27_1746_, v_i_1732_, v_a_1748_);
v_i_1732_ = v___x_1750_;
v_bs_1733_ = v___x_1751_;
goto _start;
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v_bs_x27_1746_);
v_a_1753_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1747_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1747_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* v_sz_1761_, lean_object* v_i_1762_, lean_object* v_bs_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
size_t v_sz_boxed_1771_; size_t v_i_boxed_1772_; uint8_t v___y_12256__boxed_1773_; lean_object* v_res_1774_; 
v_sz_boxed_1771_ = lean_unbox_usize(v_sz_1761_);
lean_dec(v_sz_1761_);
v_i_boxed_1772_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v___y_12256__boxed_1773_ = lean_unbox(v___y_1764_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_boxed_1771_, v_i_boxed_1772_, v_bs_1763_, v___y_12256__boxed_1773_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
if (lean_obj_tag(v_a_1775_) == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = l_List_reverse___redArg(v_a_1776_);
return v___x_1777_;
}
else
{
lean_object* v_head_1778_; lean_object* v_tail_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1788_; 
v_head_1778_ = lean_ctor_get(v_a_1775_, 0);
v_tail_1779_ = lean_ctor_get(v_a_1775_, 1);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1781_ = v_a_1775_;
v_isShared_1782_ = v_isSharedCheck_1788_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_tail_1779_);
lean_inc(v_head_1778_);
lean_dec(v_a_1775_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1788_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1783_ = l_Lean_mkFVar(v_head_1778_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 1, v_a_1776_);
lean_ctor_set(v___x_1781_, 0, v___x_1783_);
v___x_1785_ = v___x_1781_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_a_1776_);
v___x_1785_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
v_a_1775_ = v_tail_1779_;
v_a_1776_ = v___x_1785_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(lean_object* v_a_1789_, lean_object* v_as_1790_, size_t v_i_1791_, size_t v_stop_1792_, lean_object* v_b_1793_){
_start:
{
lean_object* v___y_1795_; uint8_t v___x_1799_; 
v___x_1799_ = lean_usize_dec_eq(v_i_1791_, v_stop_1792_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v_fvarId_1801_; uint8_t v___x_1802_; 
v___x_1800_ = lean_array_uget_borrowed(v_as_1790_, v_i_1791_);
v_fvarId_1801_ = lean_ctor_get(v___x_1800_, 0);
v___x_1802_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1789_, v_fvarId_1801_);
if (v___x_1802_ == 0)
{
v___y_1795_ = v_b_1793_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_1803_; 
lean_inc(v___x_1800_);
v___x_1803_ = lean_array_push(v_b_1793_, v___x_1800_);
v___y_1795_ = v___x_1803_;
goto v___jp_1794_;
}
}
else
{
return v_b_1793_;
}
v___jp_1794_:
{
size_t v___x_1796_; size_t v___x_1797_; 
v___x_1796_ = ((size_t)1ULL);
v___x_1797_ = lean_usize_add(v_i_1791_, v___x_1796_);
v_i_1791_ = v___x_1797_;
v_b_1793_ = v___y_1795_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6___boxed(lean_object* v_a_1804_, lean_object* v_as_1805_, lean_object* v_i_1806_, lean_object* v_stop_1807_, lean_object* v_b_1808_){
_start:
{
size_t v_i_boxed_1809_; size_t v_stop_boxed_1810_; lean_object* v_res_1811_; 
v_i_boxed_1809_ = lean_unbox_usize(v_i_1806_);
lean_dec(v_i_1806_);
v_stop_boxed_1810_ = lean_unbox_usize(v_stop_1807_);
lean_dec(v_stop_1807_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1804_, v_as_1805_, v_i_boxed_1809_, v_stop_boxed_1810_, v_b_1808_);
lean_dec_ref(v_as_1805_);
lean_dec_ref(v_a_1804_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(lean_object* v_a_1812_, lean_object* v_as_1813_, size_t v_i_1814_, size_t v_stop_1815_, lean_object* v_b_1816_){
_start:
{
lean_object* v___y_1818_; uint8_t v___x_1822_; 
v___x_1822_ = lean_usize_dec_eq(v_i_1814_, v_stop_1815_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v_fvarId_1824_; uint8_t v___x_1825_; 
v___x_1823_ = lean_array_uget_borrowed(v_as_1813_, v_i_1814_);
v_fvarId_1824_ = lean_ctor_get(v___x_1823_, 0);
v___x_1825_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1812_, v_fvarId_1824_);
if (v___x_1825_ == 0)
{
v___y_1818_ = v_b_1816_;
goto v___jp_1817_;
}
else
{
lean_object* v___x_1826_; 
lean_inc(v___x_1823_);
v___x_1826_ = lean_array_push(v_b_1816_, v___x_1823_);
v___y_1818_ = v___x_1826_;
goto v___jp_1817_;
}
}
else
{
return v_b_1816_;
}
v___jp_1817_:
{
size_t v___x_1819_; size_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = ((size_t)1ULL);
v___x_1820_ = lean_usize_add(v_i_1814_, v___x_1819_);
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5_spec__6(v_a_1812_, v_as_1813_, v___x_1820_, v_stop_1815_, v___y_1818_);
return v___x_1821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(lean_object* v_a_1827_, lean_object* v_as_1828_, lean_object* v_i_1829_, lean_object* v_stop_1830_, lean_object* v_b_1831_){
_start:
{
size_t v_i_boxed_1832_; size_t v_stop_boxed_1833_; lean_object* v_res_1834_; 
v_i_boxed_1832_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_stop_boxed_1833_ = lean_unbox_usize(v_stop_1830_);
lean_dec(v_stop_1830_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1827_, v_as_1828_, v_i_boxed_1832_, v_stop_boxed_1833_, v_b_1831_);
lean_dec_ref(v_as_1828_);
lean_dec_ref(v_a_1827_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(lean_object* v_a_1835_, size_t v_sz_1836_, size_t v_i_1837_, lean_object* v_bs_1838_){
_start:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_usize_dec_lt(v_i_1837_, v_sz_1836_);
if (v___x_1839_ == 0)
{
return v_bs_1838_;
}
else
{
lean_object* v_v_1840_; lean_object* v_fvarId_1841_; lean_object* v___x_1842_; lean_object* v_bs_x27_1843_; uint8_t v___x_1844_; size_t v___x_1845_; size_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v_v_1840_ = lean_array_uget_borrowed(v_bs_1838_, v_i_1837_);
v_fvarId_1841_ = lean_ctor_get(v_v_1840_, 0);
lean_inc(v_fvarId_1841_);
v___x_1842_ = lean_unsigned_to_nat(0u);
v_bs_x27_1843_ = lean_array_uset(v_bs_1838_, v_i_1837_, v___x_1842_);
v___x_1844_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1835_, v_fvarId_1841_);
lean_dec(v_fvarId_1841_);
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1837_, v___x_1845_);
v___x_1847_ = lean_box(v___x_1844_);
v___x_1848_ = lean_array_uset(v_bs_x27_1843_, v_i_1837_, v___x_1847_);
v_i_1837_ = v___x_1846_;
v_bs_1838_ = v___x_1848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(lean_object* v_a_1850_, lean_object* v_sz_1851_, lean_object* v_i_1852_, lean_object* v_bs_1853_){
_start:
{
size_t v_sz_boxed_1854_; size_t v_i_boxed_1855_; lean_object* v_res_1856_; 
v_sz_boxed_1854_ = lean_unbox_usize(v_sz_1851_);
lean_dec(v_sz_1851_);
v_i_boxed_1855_ = lean_unbox_usize(v_i_1852_);
lean_dec(v_i_1852_);
v_res_1856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1850_, v_sz_boxed_1854_, v_i_boxed_1855_, v_bs_1853_);
lean_dec_ref(v_a_1850_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* v_a_1857_, size_t v_sz_1858_, size_t v_i_1859_, lean_object* v_bs_1860_){
_start:
{
uint8_t v___x_1861_; 
v___x_1861_ = lean_usize_dec_lt(v_i_1859_, v_sz_1858_);
if (v___x_1861_ == 0)
{
return v_bs_1860_;
}
else
{
lean_object* v_v_1862_; lean_object* v_fvarId_1863_; lean_object* v___x_1864_; lean_object* v_bs_x27_1865_; uint8_t v___x_1866_; size_t v___x_1867_; size_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v_v_1862_ = lean_array_uget_borrowed(v_bs_1860_, v_i_1859_);
v_fvarId_1863_ = lean_ctor_get(v_v_1862_, 0);
lean_inc(v_fvarId_1863_);
v___x_1864_ = lean_unsigned_to_nat(0u);
v_bs_x27_1865_ = lean_array_uset(v_bs_1860_, v_i_1859_, v___x_1864_);
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_1857_, v_fvarId_1863_);
lean_dec(v_fvarId_1863_);
v___x_1867_ = ((size_t)1ULL);
v___x_1868_ = lean_usize_add(v_i_1859_, v___x_1867_);
v___x_1869_ = lean_box(v___x_1866_);
v___x_1870_ = lean_array_uset(v_bs_x27_1865_, v_i_1859_, v___x_1869_);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_1857_, v_sz_1858_, v___x_1868_, v___x_1870_);
return v___x_1871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(lean_object* v_a_1872_, lean_object* v_sz_1873_, lean_object* v_i_1874_, lean_object* v_bs_1875_){
_start:
{
size_t v_sz_boxed_1876_; size_t v_i_boxed_1877_; lean_object* v_res_1878_; 
v_sz_boxed_1876_ = lean_unbox_usize(v_sz_1873_);
lean_dec(v_sz_1873_);
v_i_boxed_1877_ = lean_unbox_usize(v_i_1874_);
lean_dec(v_i_1874_);
v_res_1878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1872_, v_sz_boxed_1876_, v_i_boxed_1877_, v_bs_1875_);
lean_dec_ref(v_a_1872_);
return v_res_1878_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = lean_box(0);
v___x_1880_ = lean_unsigned_to_nat(16u);
v___x_1881_ = lean_mk_array(v___x_1880_, v___x_1879_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0);
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v___x_1882_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_box(0);
v___x_1894_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6));
v___x_1895_ = l_Lean_Expr_const___override(v___x_1894_, v___x_1893_);
return v___x_1895_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_1908_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14));
v___x_1909_ = l_Lean_Name_append(v___x_1908_, v___x_1907_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__16));
v___x_1912_ = l_Lean_stringToMessageData(v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* v_decl_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; uint8_t v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v_value_1957_; 
v_value_1957_ = lean_ctor_get(v_decl_1913_, 1);
lean_inc_ref(v_value_1957_);
if (lean_obj_tag(v_value_1957_) == 0)
{
lean_object* v_toSignature_1958_; uint8_t v_recursive_1959_; lean_object* v_inlineAttr_x3f_1960_; lean_object* v_code_1961_; lean_object* v_name_1962_; lean_object* v_levelParams_1963_; lean_object* v_type_1964_; lean_object* v_params_1965_; uint8_t v_safe_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v_toSignature_1958_ = lean_ctor_get(v_decl_1913_, 0);
v_recursive_1959_ = lean_ctor_get_uint8(v_decl_1913_, sizeof(void*)*3);
v_inlineAttr_x3f_1960_ = lean_ctor_get(v_decl_1913_, 2);
v_code_1961_ = lean_ctor_get(v_value_1957_, 0);
v_name_1962_ = lean_ctor_get(v_toSignature_1958_, 0);
v_levelParams_1963_ = lean_ctor_get(v_toSignature_1958_, 1);
v_type_1964_ = lean_ctor_get(v_toSignature_1958_, 2);
v_params_1965_ = lean_ctor_get(v_toSignature_1958_, 3);
v_safe_1966_ = lean_ctor_get_uint8(v_toSignature_1958_, sizeof(void*)*4);
v___x_1967_ = lean_array_get_size(v_params_1965_);
v___x_1968_ = lean_unsigned_to_nat(0u);
v___x_1969_ = lean_nat_dec_eq(v___x_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_inc_ref(v_code_1961_);
lean_inc_ref(v_decl_1913_);
v___x_1970_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(v_decl_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2139_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_2139_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2139_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_size_1975_; lean_object* v_buckets_1976_; uint8_t v___x_1977_; 
v_size_1975_ = lean_ctor_get(v_a_1971_, 0);
v_buckets_1976_ = lean_ctor_get(v_a_1971_, 1);
v___x_1977_ = lean_nat_dec_eq(v_size_1975_, v___x_1967_);
if (v___x_1977_ == 0)
{
lean_object* v_toCold_1978_; lean_object* v_options_1979_; lean_object* v_inheritedTraceOptions_1980_; uint8_t v_hasTrace_1981_; uint8_t v___x_1982_; lean_object* v___y_1984_; uint8_t v___y_1985_; size_t v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; size_t v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; uint8_t v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_2040_; uint8_t v___y_2041_; size_t v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; size_t v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2052_; size_t v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; size_t v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; uint8_t v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; 
lean_inc_ref(v_params_1965_);
lean_inc_ref(v_type_1964_);
lean_inc(v_levelParams_1963_);
lean_inc(v_name_1962_);
lean_inc(v_inlineAttr_x3f_1960_);
lean_del_object(v___x_1973_);
lean_dec_ref(v_decl_1913_);
v_toCold_1978_ = lean_ctor_get(v_a_1916_, 0);
v_options_1979_ = lean_ctor_get(v_toCold_1978_, 2);
v_inheritedTraceOptions_1980_ = lean_ctor_get(v_toCold_1978_, 11);
v_hasTrace_1981_ = lean_ctor_get_uint8(v_options_1979_, sizeof(void*)*1);
v___x_1982_ = lean_nat_dec_eq(v_size_1975_, v___x_1968_);
if (v_hasTrace_1981_ == 0)
{
v___y_2087_ = v_a_1914_;
v___y_2088_ = v_a_1915_;
v___y_2089_ = v_a_1916_;
v___y_2090_ = v_a_1917_;
goto v___jp_2086_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2105_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_2106_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15);
v___x_2107_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1980_, v_options_1979_, v___x_2106_);
if (v___x_2107_ == 0)
{
v___y_2087_ = v_a_1914_;
v___y_2088_ = v_a_1915_;
v___y_2089_ = v_a_1916_;
v___y_2090_ = v_a_1917_;
goto v___jp_2086_;
}
else
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___y_2112_; lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
lean_inc(v_name_1962_);
v___x_2108_ = l_Lean_MessageData_ofName(v_name_1962_);
v___x_2109_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__17);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_array_get_size(v_buckets_1976_);
v___x_2129_ = lean_nat_dec_lt(v___x_1968_, v___x_2128_);
if (v___x_2129_ == 0)
{
v___y_2112_ = v___x_2127_;
goto v___jp_2111_;
}
else
{
size_t v___x_2130_; size_t v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = lean_usize_of_nat(v___x_2128_);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_buckets_1976_, v___x_2130_, v___x_2131_, v___x_2127_);
v___y_2112_ = v___x_2132_;
goto v___jp_2111_;
}
v___jp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2113_ = lean_box(0);
v___x_2114_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(v___y_2112_, v___x_2113_);
v___x_2115_ = l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(v___x_2114_, v___x_2113_);
v___x_2116_ = l_Lean_MessageData_ofList(v___x_2115_);
v___x_2117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2110_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(v___x_2105_, v___x_2117_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_dec_ref_known(v___x_2118_, 1);
v___y_2087_ = v_a_1914_;
v___y_2088_ = v_a_1915_;
v___y_2089_ = v_a_1916_;
v___y_2090_ = v_a_1917_;
goto v___jp_2086_;
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_1971_);
lean_dec_ref(v_params_1965_);
lean_dec_ref(v_type_1964_);
lean_dec(v_levelParams_1963_);
lean_dec(v_name_1962_);
lean_dec_ref(v_code_1961_);
lean_dec(v_inlineAttr_x3f_1960_);
lean_dec_ref_known(v_value_1957_, 1);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
}
v___jp_1983_:
{
if (lean_obj_tag(v___y_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v_a_1996_ = lean_ctor_get(v___y_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___y_1995_, 1);
v___x_1997_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1);
v___x_1998_ = lean_st_mk_ref(v___x_1997_);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v___y_1986_, v___y_1989_, v_params_1965_, v___x_1977_, v___x_1998_, v___y_1987_, v___y_1993_, v___y_1988_, v___y_1992_);
if (lean_obj_tag(v___x_1999_) == 0)
{
if (v___x_1982_ == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; size_t v_sz_2005_; lean_object* v___x_2006_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_n(v_a_2000_, 2);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4));
v___x_2002_ = lean_array_get_size(v_a_2000_);
v___x_2003_ = l_Array_toSubarray___redArg(v_a_2000_, v___x_1968_, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2001_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v_sz_2005_ = lean_array_size(v___y_1990_);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v___y_1990_, v_sz_2005_, v___y_1989_, v___x_2004_);
lean_dec_ref(v___y_1990_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v_fst_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v_fst_2008_ = lean_ctor_get(v_a_2007_, 0);
lean_inc(v_fst_2008_);
lean_dec(v_a_2007_);
v___x_2009_ = lean_box(0);
v___x_2010_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___y_1984_, v___y_1985_, v_name_1962_, v_levelParams_1963_, v_type_1964_, v_a_2000_, v_safe_1966_, v___x_1977_, v___x_2009_, v_fst_2008_, v___x_1977_, v___x_1998_, v___y_1987_, v___y_1993_, v___y_1988_, v___y_1992_);
v___y_1920_ = v___x_1998_;
v___y_1921_ = v___y_1991_;
v___y_1922_ = v___y_1993_;
v___y_1923_ = v___y_1994_;
v___y_1924_ = v_a_1996_;
v___y_1925_ = v___x_2010_;
goto v___jp_1919_;
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_a_2000_);
lean_dec(v___x_1998_);
lean_dec(v_a_1996_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1984_);
lean_dec_ref(v_type_1964_);
lean_dec(v_levelParams_1963_);
lean_dec(v_name_1962_);
v_a_2011_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2006_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2006_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec_ref(v___y_1990_);
v_a_2019_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2020_ = ((lean_object*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__5));
v___x_2021_ = lean_box(0);
v___x_2022_ = l_Lean_Compiler_LCNF_Decl_reduceArity___lam__1(v___y_1984_, v___y_1985_, v_name_1962_, v_levelParams_1963_, v_type_1964_, v_a_2019_, v_safe_1966_, v___x_1977_, v___x_2021_, v___x_2020_, v___x_1977_, v___x_1998_, v___y_1987_, v___y_1993_, v___y_1988_, v___y_1992_);
v___y_1920_ = v___x_1998_;
v___y_1921_ = v___y_1991_;
v___y_1922_ = v___y_1993_;
v___y_1923_ = v___y_1994_;
v___y_1924_ = v_a_1996_;
v___y_1925_ = v___x_2022_;
goto v___jp_1919_;
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v___x_1998_);
lean_dec(v_a_1996_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1984_);
lean_dec_ref(v_type_1964_);
lean_dec(v_levelParams_1963_);
lean_dec(v_name_1962_);
v_a_2023_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1999_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1999_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1984_);
lean_dec_ref(v_params_1965_);
lean_dec_ref(v_type_1964_);
lean_dec(v_levelParams_1963_);
lean_dec(v_name_1962_);
v_a_2031_ = lean_ctor_get(v___y_1995_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___y_1995_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___y_1995_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___y_1995_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
v___jp_2039_:
{
lean_object* v___x_2053_; 
lean_inc(v___y_2049_);
lean_inc_ref(v___y_2044_);
lean_inc(v___y_2050_);
lean_inc_ref(v___y_2043_);
v___x_2053_ = lean_apply_6(v___y_2048_, v___y_2052_, v___y_2043_, v___y_2050_, v___y_2044_, v___y_2049_, lean_box(0));
v___y_1984_ = v___y_2040_;
v___y_1985_ = v___y_2041_;
v___y_1986_ = v___y_2042_;
v___y_1987_ = v___y_2043_;
v___y_1988_ = v___y_2044_;
v___y_1989_ = v___y_2045_;
v___y_1990_ = v___y_2046_;
v___y_1991_ = v___y_2047_;
v___y_1992_ = v___y_2049_;
v___y_1993_ = v___y_2050_;
v___y_1994_ = v___y_2051_;
v___y_1995_ = v___x_2053_;
goto v___jp_1983_;
}
v___jp_2054_:
{
if (v___x_1982_ == 0)
{
lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_2067_ = lean_nat_dec_lt(v___x_1968_, v___x_1967_);
if (v___x_2067_ == 0)
{
lean_dec(v_a_1971_);
v___y_2040_ = v___y_2061_;
v___y_2041_ = v___y_2064_;
v___y_2042_ = v___y_2055_;
v___y_2043_ = v___y_2056_;
v___y_2044_ = v___y_2057_;
v___y_2045_ = v___y_2058_;
v___y_2046_ = v___y_2059_;
v___y_2047_ = v___y_2065_;
v___y_2048_ = v___y_2060_;
v___y_2049_ = v___y_2063_;
v___y_2050_ = v___y_2062_;
v___y_2051_ = v___y_2064_;
v___y_2052_ = v___x_2066_;
goto v___jp_2039_;
}
else
{
size_t v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_usize_of_nat(v___x_1967_);
v___x_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_1971_, v_params_1965_, v___y_2058_, v___x_2068_, v___x_2066_);
lean_dec(v_a_1971_);
v___y_2040_ = v___y_2061_;
v___y_2041_ = v___y_2064_;
v___y_2042_ = v___y_2055_;
v___y_2043_ = v___y_2056_;
v___y_2044_ = v___y_2057_;
v___y_2045_ = v___y_2058_;
v___y_2046_ = v___y_2059_;
v___y_2047_ = v___y_2065_;
v___y_2048_ = v___y_2060_;
v___y_2049_ = v___y_2063_;
v___y_2050_ = v___y_2062_;
v___y_2051_ = v___y_2064_;
v___y_2052_ = v___x_2069_;
goto v___jp_2039_;
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec(v_a_1971_);
v___x_2070_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4));
v___x_2071_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7, &l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_once, _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7);
v___x_2072_ = l_Lean_Compiler_LCNF_mkParam(v___y_2064_, v___x_2070_, v___x_2071_, v___x_1977_, v___y_2056_, v___y_2062_, v___y_2057_, v___y_2063_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = lean_mk_empty_array_with_capacity(v___x_2074_);
v___x_2076_ = lean_array_push(v___x_2075_, v_a_2073_);
lean_inc(v___y_2063_);
lean_inc_ref(v___y_2057_);
lean_inc(v___y_2062_);
lean_inc_ref(v___y_2056_);
v___x_2077_ = lean_apply_6(v___y_2060_, v___x_2076_, v___y_2056_, v___y_2062_, v___y_2057_, v___y_2063_, lean_box(0));
v___y_1984_ = v___y_2061_;
v___y_1985_ = v___y_2064_;
v___y_1986_ = v___y_2055_;
v___y_1987_ = v___y_2056_;
v___y_1988_ = v___y_2057_;
v___y_1989_ = v___y_2058_;
v___y_1990_ = v___y_2059_;
v___y_1991_ = v___y_2065_;
v___y_1992_ = v___y_2063_;
v___y_1993_ = v___y_2062_;
v___y_1994_ = v___y_2064_;
v___y_1995_ = v___x_2077_;
goto v___jp_1983_;
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec_ref(v_params_1965_);
lean_dec_ref(v_type_1964_);
lean_dec(v_levelParams_1963_);
lean_dec(v_name_1962_);
v_a_2078_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2072_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2072_);
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
}
v___jp_2086_:
{
size_t v_sz_2091_; size_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___f_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v_sz_2091_ = lean_array_size(v_params_1965_);
v___x_2092_ = ((size_t)0ULL);
lean_inc_ref(v_params_1965_);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_1971_, v_sz_2091_, v___x_2092_, v_params_1965_);
v___x_2094_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9));
lean_inc_n(v_name_1962_, 2);
v___x_2095_ = l_Lean_Name_append(v_name_1962_, v___x_2094_);
v___x_2096_ = lean_box(v___x_1982_);
v___x_2097_ = lean_box(v_safe_1966_);
v___x_2098_ = lean_box(v_recursive_1959_);
lean_inc_ref(v___x_2093_);
lean_inc(v___x_2095_);
v___f_2099_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_reduceArity___lam__0___boxed), 15, 9);
lean_closure_set(v___f_2099_, 0, v_name_1962_);
lean_closure_set(v___f_2099_, 1, v___x_2095_);
lean_closure_set(v___f_2099_, 2, v___x_2093_);
lean_closure_set(v___f_2099_, 3, v___x_2096_);
lean_closure_set(v___f_2099_, 4, v_value_1957_);
lean_closure_set(v___f_2099_, 5, v_code_1961_);
lean_closure_set(v___f_2099_, 6, v___x_2097_);
lean_closure_set(v___f_2099_, 7, v___x_2098_);
lean_closure_set(v___f_2099_, 8, v_inlineAttr_x3f_1960_);
v___x_2100_ = 0;
v___x_2101_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2));
v___x_2102_ = lean_nat_dec_lt(v___x_1968_, v___x_1967_);
if (v___x_2102_ == 0)
{
v___y_2055_ = v_sz_2091_;
v___y_2056_ = v___y_2087_;
v___y_2057_ = v___y_2089_;
v___y_2058_ = v___x_2092_;
v___y_2059_ = v___x_2093_;
v___y_2060_ = v___f_2099_;
v___y_2061_ = v___x_2095_;
v___y_2062_ = v___y_2088_;
v___y_2063_ = v___y_2090_;
v___y_2064_ = v___x_2100_;
v___y_2065_ = v___x_2101_;
goto v___jp_2054_;
}
else
{
size_t v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = lean_usize_of_nat(v___x_1967_);
v___x_2104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_1971_, v_params_1965_, v___x_2092_, v___x_2103_, v___x_2101_);
v___y_2055_ = v_sz_2091_;
v___y_2056_ = v___y_2087_;
v___y_2057_ = v___y_2089_;
v___y_2058_ = v___x_2092_;
v___y_2059_ = v___x_2093_;
v___y_2060_ = v___f_2099_;
v___y_2061_ = v___x_2095_;
v___y_2062_ = v___y_2088_;
v___y_2063_ = v___y_2090_;
v___y_2064_ = v___x_2100_;
v___y_2065_ = v___x_2104_;
goto v___jp_2054_;
}
}
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2137_; 
lean_dec(v_a_1971_);
lean_dec_ref(v_code_1961_);
lean_dec_ref_known(v_value_1957_, 1);
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_mk_empty_array_with_capacity(v___x_2133_);
v___x_2135_ = lean_array_push(v___x_2134_, v_decl_1913_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_2135_);
v___x_2137_ = v___x_1973_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec_ref(v_code_1961_);
lean_dec_ref_known(v_value_1957_, 1);
lean_dec_ref(v_decl_1913_);
v_a_2140_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_1970_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_1970_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2157_; 
v_isSharedCheck_2157_ = !lean_is_exclusive(v_value_1957_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v_value_1957_, 0);
lean_dec(v_unused_2158_);
v___x_2149_ = v_value_1957_;
v_isShared_2150_ = v_isSharedCheck_2157_;
goto v_resetjp_2148_;
}
else
{
lean_dec(v_value_1957_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2157_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2151_ = lean_unsigned_to_nat(1u);
v___x_2152_ = lean_mk_empty_array_with_capacity(v___x_2151_);
v___x_2153_ = lean_array_push(v___x_2152_, v_decl_1913_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2153_);
v___x_2155_ = v___x_2149_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2168_; 
v_isSharedCheck_2168_ = !lean_is_exclusive(v_value_1957_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v_value_1957_, 0);
lean_dec(v_unused_2169_);
v___x_2160_ = v_value_1957_;
v_isShared_2161_ = v_isSharedCheck_2168_;
goto v_resetjp_2159_;
}
else
{
lean_dec(v_value_1957_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2168_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2162_ = lean_unsigned_to_nat(1u);
v___x_2163_ = lean_mk_empty_array_with_capacity(v___x_2162_);
v___x_2164_ = lean_array_push(v___x_2163_, v_decl_1913_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set_tag(v___x_2160_, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2164_);
v___x_2166_ = v___x_2160_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
v___jp_1919_:
{
if (lean_obj_tag(v___y_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_a_1926_ = lean_ctor_get(v___y_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___y_1925_, 1);
v___x_1927_ = lean_st_ref_get(v___y_1920_);
lean_dec(v___y_1920_);
lean_dec(v___x_1927_);
v___x_1928_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___y_1923_, v___y_1921_, v___y_1922_);
lean_dec_ref(v___y_1921_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1939_; 
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1928_, 0);
lean_dec(v_unused_1940_);
v___x_1930_ = v___x_1928_;
v_isShared_1931_ = v_isSharedCheck_1939_;
goto v_resetjp_1929_;
}
else
{
lean_dec(v___x_1928_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1939_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1932_ = lean_unsigned_to_nat(2u);
v___x_1933_ = lean_mk_empty_array_with_capacity(v___x_1932_);
v___x_1934_ = lean_array_push(v___x_1933_, v___y_1924_);
v___x_1935_ = lean_array_push(v___x_1934_, v_a_1926_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1935_);
v___x_1937_ = v___x_1930_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_a_1926_);
lean_dec_ref(v___y_1924_);
v_a_1941_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1928_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1928_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v___y_1924_);
lean_dec_ref(v___y_1921_);
lean_dec(v___y_1920_);
v_a_1949_ = lean_ctor_get(v___y_1925_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___y_1925_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___y_1925_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___y_1925_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(lean_object* v_decl_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v_decl_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
return v_res_2176_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* v_00_u03b2_2177_, lean_object* v_m_2178_, lean_object* v_a_2179_){
_start:
{
uint8_t v___x_2180_; 
v___x_2180_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_2178_, v_a_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* v_00_u03b2_2181_, lean_object* v_m_2182_, lean_object* v_a_2183_){
_start:
{
uint8_t v_res_2184_; lean_object* v_r_2185_; 
v_res_2184_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(v_00_u03b2_2181_, v_m_2182_, v_a_2183_);
lean_dec(v_a_2183_);
lean_dec_ref(v_m_2182_);
v_r_2185_ = lean_box(v_res_2184_);
return v_r_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* v_as_2186_, size_t v_sz_2187_, size_t v_i_2188_, lean_object* v_b_2189_, uint8_t v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_2186_, v_sz_2187_, v_i_2188_, v_b_2189_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* v_as_2198_, lean_object* v_sz_2199_, lean_object* v_i_2200_, lean_object* v_b_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
size_t v_sz_boxed_2209_; size_t v_i_boxed_2210_; uint8_t v___y_13020__boxed_2211_; lean_object* v_res_2212_; 
v_sz_boxed_2209_ = lean_unbox_usize(v_sz_2199_);
lean_dec(v_sz_2199_);
v_i_boxed_2210_ = lean_unbox_usize(v_i_2200_);
lean_dec(v_i_2200_);
v___y_13020__boxed_2211_ = lean_unbox(v___y_2202_);
v_res_2212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_2198_, v_sz_boxed_2209_, v_i_boxed_2210_, v_b_2201_, v___y_13020__boxed_2211_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v_as_2198_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* v_as_2213_, size_t v_i_2214_, size_t v_stop_2215_, lean_object* v_b_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
uint8_t v___x_2222_; 
v___x_2222_ = lean_usize_dec_eq(v_i_2214_, v_stop_2215_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_array_uget_borrowed(v_as_2213_, v_i_2214_);
lean_inc(v___x_2223_);
v___x_2224_ = l_Lean_Compiler_LCNF_Decl_reduceArity(v___x_2223_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2226_; size_t v___x_2227_; size_t v___x_2228_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
v___x_2226_ = l_Array_append___redArg(v_b_2216_, v_a_2225_);
lean_dec(v_a_2225_);
v___x_2227_ = ((size_t)1ULL);
v___x_2228_ = lean_usize_add(v_i_2214_, v___x_2227_);
v_i_2214_ = v___x_2228_;
v_b_2216_ = v___x_2226_;
goto _start;
}
else
{
lean_dec_ref(v_b_2216_);
return v___x_2224_;
}
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2230_, 0, v_b_2216_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* v_as_2231_, lean_object* v_i_2232_, lean_object* v_stop_2233_, lean_object* v_b_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
size_t v_i_boxed_2240_; size_t v_stop_boxed_2241_; lean_object* v_res_2242_; 
v_i_boxed_2240_ = lean_unbox_usize(v_i_2232_);
lean_dec(v_i_2232_);
v_stop_boxed_2241_ = lean_unbox_usize(v_stop_2233_);
lean_dec(v_stop_2233_);
v_res_2242_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_2231_, v_i_boxed_2240_, v_stop_boxed_2241_, v_b_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec_ref(v_as_2231_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* v___x_2243_, lean_object* v_decls_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2250_ = lean_mk_empty_array_with_capacity(v___x_2243_);
v___x_2251_ = lean_array_get_size(v_decls_2244_);
v___x_2252_ = lean_nat_dec_lt(v___x_2243_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2250_);
return v___x_2253_;
}
else
{
size_t v___x_2254_; size_t v___x_2255_; lean_object* v___x_2256_; 
v___x_2254_ = ((size_t)0ULL);
v___x_2255_ = lean_usize_of_nat(v___x_2251_);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_2244_, v___x_2254_, v___x_2255_, v___x_2250_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* v___x_2257_, lean_object* v_decls_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(v___x_2257_, v_decls_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v_decls_2258_);
lean_dec(v___x_2257_);
return v_res_2264_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2327_ = lean_unsigned_to_nat(2803462840u);
v___x_2328_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2329_ = l_Lean_Name_num___override(v___x_2328_, v___x_2327_);
return v___x_2329_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2332_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2333_ = l_Lean_Name_str___override(v___x_2332_, v___x_2331_);
return v___x_2333_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_));
v___x_2336_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2337_ = l_Lean_Name_str___override(v___x_2336_, v___x_2335_);
return v___x_2337_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2338_ = lean_unsigned_to_nat(2u);
v___x_2339_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2340_ = l_Lean_Name_num___override(v___x_2339_, v___x_2338_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2342_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12));
v___x_2343_ = 1;
v___x_2344_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
v___x_2345_ = l_Lean_registerTraceClass(v___x_2342_, v___x_2343_, v___x_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
return v_res_2347_;
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
