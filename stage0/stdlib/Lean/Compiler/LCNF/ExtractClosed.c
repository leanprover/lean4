// Lean compiler output
// Module: Lean.Compiler.LCNF.ExtractClosed
// Imports: public import Lean.Compiler.ClosedTermCache public import Lean.Compiler.NeverExtractAttr public import Lean.Compiler.LCNF.Internalize public import Lean.Compiler.LCNF.ToExpr import Lean.Compiler.LCNF.ElimDead import Lean.Compiler.LCNF.DependsOn meta import Init.Data.FloatArray.Basic
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
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_dependsOn(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object*);
uint8_t l_Lean_hasNeverExtractAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toExpr(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_getClosedTermName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_cacheClosedTermName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_elimDeadVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(uint8_t, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "push"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ByteArray"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FloatArray"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mkEmpty"};
static const lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "emptyWithCapacity"};
static const lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3;
static const lean_array_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_closed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(29, 126, 0, 54, 34, 229, 13, 211)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3;
static const lean_array_object l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_extractClosed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_extractClosed___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_extractClosed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "extractClosed"};
static const lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_extractClosed___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_extractClosed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_extractClosed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(16, 21, 66, 200, 64, 129, 192, 37)}};
static const lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_extractClosed___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_extractClosed___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_extractClosed___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_extractClosed___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_extractClosed___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_extractClosed = (const lean_object*)&l_Lean_Compiler_LCNF_extractClosed___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_extractClosed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 14, 140, 205, 207, 60, 147, 42)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ExtractClosed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 145, 126, 90, 151, 26, 34, 9)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(139, 235, 184, 174, 76, 101, 161, 215)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 112, 10, 236, 225, 168, 165, 247)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 156, 124, 16, 61, 103, 21, 1)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(21, 117, 23, 217, 176, 101, 65, 172)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 123, 29, 205, 113, 82, 167, 38)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 54, 59, 99, 42, 73, 109, 59)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 32, 233, 137, 255, 41, 188, 205)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 56, 82, 205, 141, 229, 9, 9)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 148, 208, 83, 164, 82, 56, 215)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(248, 36, 227, 28, 19, 166, 37, 247)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)(((size_t)(998081055) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(114, 224, 201, 26, 129, 73, 142, 133)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 11, 234, 77, 173, 247, 226, 232)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(93, 133, 36, 146, 26, 150, 84, 2)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 58, 6, 47, 207, 210, 115, 225)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
uint8_t v___x_11_; 
v___x_11_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v___x_13_ = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(v___x_12_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; size_t v___x_15_; size_t v___x_16_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_13_, 1);
v___x_15_ = ((size_t)1ULL);
v___x_16_ = lean_usize_add(v_i_2_, v___x_15_);
v_i_2_ = v___x_16_;
v_b_4_ = v_a_14_;
goto _start;
}
else
{
return v___x_13_;
}
}
else
{
lean_object* v___x_18_; 
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v_b_4_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(lean_object* v_v_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
switch(lean_obj_tag(v_v_19_))
{
case 2:
{
lean_object* v_struct_26_; lean_object* v___x_27_; 
v_struct_26_ = lean_ctor_get(v_v_19_, 2);
v___x_27_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_struct_26_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_27_;
}
case 3:
{
lean_object* v_args_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_args_28_ = lean_ctor_get(v_v_19_, 2);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_array_get_size(v_args_28_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_nat_dec_lt(v___x_29_, v___x_30_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; 
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_31_);
return v___x_33_;
}
else
{
size_t v___x_34_; size_t v___x_35_; lean_object* v___x_36_; 
v___x_34_ = ((size_t)0ULL);
v___x_35_ = lean_usize_of_nat(v___x_30_);
v___x_36_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_28_, v___x_34_, v___x_35_, v___x_31_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_36_;
}
}
case 4:
{
lean_object* v_fvarId_37_; lean_object* v_args_38_; lean_object* v___x_39_; 
v_fvarId_37_ = lean_ctor_get(v_v_19_, 0);
v_args_38_ = lean_ctor_get(v_v_19_, 1);
v___x_39_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_37_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_53_; 
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_53_ == 0)
{
lean_object* v_unused_54_; 
v_unused_54_ = lean_ctor_get(v___x_39_, 0);
lean_dec(v_unused_54_);
v___x_41_ = v___x_39_;
v_isShared_42_ = v_isSharedCheck_53_;
goto v_resetjp_40_;
}
else
{
lean_dec(v___x_39_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_53_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_array_get_size(v_args_38_);
v___x_45_ = lean_box(0);
v___x_46_ = lean_nat_dec_lt(v___x_43_, v___x_44_);
if (v___x_46_ == 0)
{
lean_object* v___x_48_; 
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 0, v___x_45_);
v___x_48_ = v___x_41_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_45_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
else
{
size_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; 
lean_del_object(v___x_41_);
v___x_50_ = ((size_t)0ULL);
v___x_51_ = lean_usize_of_nat(v___x_44_);
v___x_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_38_, v___x_50_, v___x_51_, v___x_45_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_52_;
}
}
}
else
{
return v___x_39_;
}
}
default: 
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_box(0);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(lean_object* v_fvarId_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
uint8_t v___x_64_; lean_object* v___x_65_; 
v___x_64_ = 0;
v___x_65_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_64_, v_fvarId_57_, v_a_60_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_87_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_87_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_87_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_87_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
if (lean_obj_tag(v_a_66_) == 1)
{
lean_object* v_val_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_82_; 
lean_del_object(v___x_68_);
v_val_70_ = lean_ctor_get(v_a_66_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v_a_66_);
if (v_isSharedCheck_82_ == 0)
{
v___x_72_ = v_a_66_;
v_isShared_73_ = v_isSharedCheck_82_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_val_70_);
lean_dec(v_a_66_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_82_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_74_ = lean_st_ref_take(v_a_58_);
lean_inc(v_val_70_);
if (v_isShared_73_ == 0)
{
lean_ctor_set_tag(v___x_72_, 0);
v___x_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_val_70_);
v___x_76_ = v_reuseFailAlloc_81_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v_value_79_; lean_object* v___x_80_; 
v___x_77_ = lean_array_push(v___x_74_, v___x_76_);
v___x_78_ = lean_st_ref_put(v_a_58_, v___x_77_);
v_value_79_ = lean_ctor_get(v_val_70_, 3);
lean_inc(v_value_79_);
lean_dec(v_val_70_);
v___x_80_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_79_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_value_79_);
return v___x_80_;
}
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_85_; 
lean_dec(v_a_66_);
v___x_83_ = lean_box(0);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_83_);
v___x_85_ = v___x_68_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
else
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_88_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_65_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_65_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg(lean_object* v_arg_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
if (lean_obj_tag(v_arg_96_) == 1)
{
lean_object* v_fvarId_103_; lean_object* v___x_104_; 
v_fvarId_103_ = lean_ctor_get(v_arg_96_, 0);
v___x_104_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_103_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
return v___x_104_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_box(0);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg___boxed(lean_object* v_arg_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(v_arg_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec(v_arg_107_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0___boxed(lean_object* v_as_115_, lean_object* v_i_116_, lean_object* v_stop_117_, lean_object* v_b_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
size_t v_i_boxed_125_; size_t v_stop_boxed_126_; lean_object* v_res_127_; 
v_i_boxed_125_ = lean_unbox_usize(v_i_116_);
lean_dec(v_i_116_);
v_stop_boxed_126_ = lean_unbox_usize(v_stop_117_);
lean_dec(v_stop_117_);
v_res_127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_as_115_, v_i_boxed_125_, v_stop_boxed_126_, v_b_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v_as_115_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar___boxed(lean_object* v_fvarId_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec(v_fvarId_128_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___boxed(lean_object* v_v_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_v_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec(v_v_136_);
return v_res_143_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(lean_object* v_arg_144_){
_start:
{
if (lean_obj_tag(v_arg_144_) == 1)
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = 1;
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg___boxed(lean_object* v_arg_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v_arg_147_);
lean_dec(v_arg_147_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t v_____do__lift_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
if (v_____do__lift_150_ == 0)
{
uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = 1;
v___x_159_ = lean_box(v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
else
{
uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = 0;
v___x_162_ = lean_box(v___x_161_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object* v_____do__lift_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
uint8_t v_____do__lift_14860__boxed_172_; lean_object* v_res_173_; 
v_____do__lift_14860__boxed_172_ = lean_unbox(v_____do__lift_164_);
v_res_173_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v_____do__lift_14860__boxed_172_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_175_) == 0)
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v_key_177_; lean_object* v_value_178_; lean_object* v_tail_179_; uint8_t v___x_180_; 
v_key_177_ = lean_ctor_get(v_x_175_, 0);
v_value_178_ = lean_ctor_get(v_x_175_, 1);
v_tail_179_ = lean_ctor_get(v_x_175_, 2);
v___x_180_ = l_Lean_instBEqFVarId_beq(v_key_177_, v_a_174_);
if (v___x_180_ == 0)
{
v_x_175_ = v_tail_179_;
goto _start;
}
else
{
lean_object* v___x_182_; 
lean_inc(v_value_178_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_value_178_);
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg___boxed(lean_object* v_a_183_, lean_object* v_x_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_183_, v_x_184_);
lean_dec(v_x_184_);
lean_dec(v_a_183_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(lean_object* v_m_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_buckets_188_; lean_object* v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v_fold_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_buckets_188_ = lean_ctor_get(v_m_186_, 1);
v___x_189_ = lean_array_get_size(v_buckets_188_);
v___x_190_ = l_Lean_instHashableFVarId_hash(v_a_187_);
v___x_191_ = 32ULL;
v___x_192_ = lean_uint64_shift_right(v___x_190_, v___x_191_);
v_fold_193_ = lean_uint64_xor(v___x_190_, v___x_192_);
v___x_194_ = 16ULL;
v___x_195_ = lean_uint64_shift_right(v_fold_193_, v___x_194_);
v___x_196_ = lean_uint64_xor(v_fold_193_, v___x_195_);
v___x_197_ = lean_uint64_to_usize(v___x_196_);
v___x_198_ = lean_usize_of_nat(v___x_189_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_sub(v___x_198_, v___x_199_);
v___x_201_ = lean_usize_land(v___x_197_, v___x_200_);
v___x_202_ = lean_array_uget_borrowed(v_buckets_188_, v___x_201_);
v___x_203_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_187_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg___boxed(lean_object* v_m_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_m_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 0)
{
return v_x_207_;
}
else
{
lean_object* v_key_209_; lean_object* v_value_210_; lean_object* v_tail_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_234_; 
v_key_209_ = lean_ctor_get(v_x_208_, 0);
v_value_210_ = lean_ctor_get(v_x_208_, 1);
v_tail_211_ = lean_ctor_get(v_x_208_, 2);
v_isSharedCheck_234_ = !lean_is_exclusive(v_x_208_);
if (v_isSharedCheck_234_ == 0)
{
v___x_213_ = v_x_208_;
v_isShared_214_ = v_isSharedCheck_234_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_tail_211_);
lean_inc(v_value_210_);
lean_inc(v_key_209_);
lean_dec(v_x_208_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_234_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; uint64_t v___x_218_; uint64_t v_fold_219_; uint64_t v___x_220_; uint64_t v___x_221_; uint64_t v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v___x_225_; size_t v___x_226_; size_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_215_ = lean_array_get_size(v_x_207_);
v___x_216_ = l_Lean_instHashableFVarId_hash(v_key_209_);
v___x_217_ = 32ULL;
v___x_218_ = lean_uint64_shift_right(v___x_216_, v___x_217_);
v_fold_219_ = lean_uint64_xor(v___x_216_, v___x_218_);
v___x_220_ = 16ULL;
v___x_221_ = lean_uint64_shift_right(v_fold_219_, v___x_220_);
v___x_222_ = lean_uint64_xor(v_fold_219_, v___x_221_);
v___x_223_ = lean_uint64_to_usize(v___x_222_);
v___x_224_ = lean_usize_of_nat(v___x_215_);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_sub(v___x_224_, v___x_225_);
v___x_227_ = lean_usize_land(v___x_223_, v___x_226_);
v___x_228_ = lean_array_uget_borrowed(v_x_207_, v___x_227_);
lean_inc(v___x_228_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 2, v___x_228_);
v___x_230_ = v___x_213_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_key_209_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_value_210_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v___x_228_);
v___x_230_ = v_reuseFailAlloc_233_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_array_uset(v_x_207_, v___x_227_, v___x_230_);
v_x_207_ = v___x_231_;
v_x_208_ = v_tail_211_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(lean_object* v_i_235_, lean_object* v_source_236_, lean_object* v_target_237_){
_start:
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_array_get_size(v_source_236_);
v___x_239_ = lean_nat_dec_lt(v_i_235_, v___x_238_);
if (v___x_239_ == 0)
{
lean_dec_ref(v_source_236_);
lean_dec(v_i_235_);
return v_target_237_;
}
else
{
lean_object* v_es_240_; lean_object* v___x_241_; lean_object* v_source_242_; lean_object* v_target_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_es_240_ = lean_array_fget(v_source_236_, v_i_235_);
v___x_241_ = lean_box(0);
v_source_242_ = lean_array_fset(v_source_236_, v_i_235_, v___x_241_);
v_target_243_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_target_237_, v_es_240_);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_add(v_i_235_, v___x_244_);
lean_dec(v_i_235_);
v_i_235_ = v___x_245_;
v_source_236_ = v_source_242_;
v_target_237_ = v_target_243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(lean_object* v_data_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v_nbuckets_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_248_ = lean_array_get_size(v_data_247_);
v___x_249_ = lean_unsigned_to_nat(2u);
v_nbuckets_250_ = lean_nat_mul(v___x_248_, v___x_249_);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_box(0);
v___x_253_ = lean_mk_array(v_nbuckets_250_, v___x_252_);
v___x_254_ = lean_array_propagate_mark(v_data_247_, v___x_253_);
v___x_255_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v___x_251_, v_data_247_, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(lean_object* v_a_256_, lean_object* v_b_257_, lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_dec(v_b_257_);
lean_dec(v_a_256_);
return v_x_258_;
}
else
{
lean_object* v_key_259_; lean_object* v_value_260_; lean_object* v_tail_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_273_; 
v_key_259_ = lean_ctor_get(v_x_258_, 0);
v_value_260_ = lean_ctor_get(v_x_258_, 1);
v_tail_261_ = lean_ctor_get(v_x_258_, 2);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_273_ == 0)
{
v___x_263_ = v_x_258_;
v_isShared_264_ = v_isSharedCheck_273_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_tail_261_);
lean_inc(v_value_260_);
lean_inc(v_key_259_);
lean_dec(v_x_258_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_273_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
uint8_t v___x_265_; 
v___x_265_ = l_Lean_instBEqFVarId_beq(v_key_259_, v_a_256_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_266_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_256_, v_b_257_, v_tail_261_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 2, v___x_266_);
v___x_268_ = v___x_263_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_key_259_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_value_260_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
else
{
lean_object* v___x_271_; 
lean_dec(v_value_260_);
lean_dec(v_key_259_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v_b_257_);
lean_ctor_set(v___x_263_, 0, v_a_256_);
v___x_271_ = v___x_263_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_256_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_b_257_);
lean_ctor_set(v_reuseFailAlloc_272_, 2, v_tail_261_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(lean_object* v_a_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
uint8_t v___x_276_; 
v___x_276_ = 0;
return v___x_276_;
}
else
{
lean_object* v_key_277_; lean_object* v_tail_278_; uint8_t v___x_279_; 
v_key_277_ = lean_ctor_get(v_x_275_, 0);
v_tail_278_ = lean_ctor_get(v_x_275_, 2);
v___x_279_ = l_Lean_instBEqFVarId_beq(v_key_277_, v_a_274_);
if (v___x_279_ == 0)
{
v_x_275_ = v_tail_278_;
goto _start;
}
else
{
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg___boxed(lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_281_, v_x_282_);
lean_dec(v_x_282_);
lean_dec(v_a_281_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(lean_object* v_m_285_, lean_object* v_a_286_, lean_object* v_b_287_){
_start:
{
lean_object* v_size_288_; lean_object* v_buckets_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_332_; 
v_size_288_ = lean_ctor_get(v_m_285_, 0);
v_buckets_289_ = lean_ctor_get(v_m_285_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_m_285_);
if (v_isSharedCheck_332_ == 0)
{
v___x_291_ = v_m_285_;
v_isShared_292_ = v_isSharedCheck_332_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_buckets_289_);
lean_inc(v_size_288_);
lean_dec(v_m_285_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_332_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v_fold_297_; uint64_t v___x_298_; uint64_t v___x_299_; uint64_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; lean_object* v_bkt_306_; uint8_t v___x_307_; 
v___x_293_ = lean_array_get_size(v_buckets_289_);
v___x_294_ = l_Lean_instHashableFVarId_hash(v_a_286_);
v___x_295_ = 32ULL;
v___x_296_ = lean_uint64_shift_right(v___x_294_, v___x_295_);
v_fold_297_ = lean_uint64_xor(v___x_294_, v___x_296_);
v___x_298_ = 16ULL;
v___x_299_ = lean_uint64_shift_right(v_fold_297_, v___x_298_);
v___x_300_ = lean_uint64_xor(v_fold_297_, v___x_299_);
v___x_301_ = lean_uint64_to_usize(v___x_300_);
v___x_302_ = lean_usize_of_nat(v___x_293_);
v___x_303_ = ((size_t)1ULL);
v___x_304_ = lean_usize_sub(v___x_302_, v___x_303_);
v___x_305_ = lean_usize_land(v___x_301_, v___x_304_);
v_bkt_306_ = lean_array_uget_borrowed(v_buckets_289_, v___x_305_);
v___x_307_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_286_, v_bkt_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v_size_x27_309_; lean_object* v___x_310_; lean_object* v_buckets_x27_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_308_ = lean_unsigned_to_nat(1u);
v_size_x27_309_ = lean_nat_add(v_size_288_, v___x_308_);
lean_dec(v_size_288_);
lean_inc(v_bkt_306_);
v___x_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_310_, 0, v_a_286_);
lean_ctor_set(v___x_310_, 1, v_b_287_);
lean_ctor_set(v___x_310_, 2, v_bkt_306_);
v_buckets_x27_311_ = lean_array_uset(v_buckets_289_, v___x_305_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(4u);
v___x_313_ = lean_nat_mul(v_size_x27_309_, v___x_312_);
v___x_314_ = lean_unsigned_to_nat(3u);
v___x_315_ = lean_nat_div(v___x_313_, v___x_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_array_get_size(v_buckets_x27_311_);
v___x_317_ = lean_nat_dec_le(v___x_315_, v___x_316_);
lean_dec(v___x_315_);
if (v___x_317_ == 0)
{
lean_object* v_val_318_; lean_object* v___x_320_; 
v_val_318_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_buckets_x27_311_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v_val_318_);
lean_ctor_set(v___x_291_, 0, v_size_x27_309_);
v___x_320_ = v___x_291_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_size_x27_309_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_val_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
else
{
lean_object* v___x_323_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v_buckets_x27_311_);
lean_ctor_set(v___x_291_, 0, v_size_x27_309_);
v___x_323_ = v___x_291_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_size_x27_309_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_buckets_x27_311_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v___x_325_; lean_object* v_buckets_x27_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
lean_inc(v_bkt_306_);
v___x_325_ = lean_box(0);
v_buckets_x27_326_ = lean_array_uset(v_buckets_289_, v___x_305_, v___x_325_);
v___x_327_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_286_, v_b_287_, v_bkt_306_);
v___x_328_ = lean_array_uset(v_buckets_x27_326_, v___x_305_, v___x_327_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v___x_328_);
v___x_330_ = v___x_291_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_size_288_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(lean_object* v_declName_333_, lean_object* v_as_334_, size_t v_i_335_, size_t v_stop_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_usize_dec_eq(v_i_335_, v_stop_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; lean_object* v_toSignature_339_; lean_object* v_name_340_; uint8_t v___x_341_; 
v___x_338_ = lean_array_uget_borrowed(v_as_334_, v_i_335_);
v_toSignature_339_ = lean_ctor_get(v___x_338_, 0);
v_name_340_ = lean_ctor_get(v_toSignature_339_, 0);
v___x_341_ = lean_name_eq(v_name_340_, v_declName_333_);
if (v___x_341_ == 0)
{
size_t v___x_342_; size_t v___x_343_; 
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_add(v_i_335_, v___x_342_);
v_i_335_ = v___x_343_;
goto _start;
}
else
{
return v___x_341_;
}
}
else
{
uint8_t v___x_345_; 
v___x_345_ = 0;
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3___boxed(lean_object* v_declName_346_, lean_object* v_as_347_, lean_object* v_i_348_, lean_object* v_stop_349_){
_start:
{
size_t v_i_boxed_350_; size_t v_stop_boxed_351_; uint8_t v_res_352_; lean_object* v_r_353_; 
v_i_boxed_350_ = lean_unbox_usize(v_i_348_);
lean_dec(v_i_348_);
v_stop_boxed_351_ = lean_unbox_usize(v_stop_349_);
lean_dec(v_stop_349_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_346_, v_as_347_, v_i_boxed_350_, v_stop_boxed_351_);
lean_dec_ref(v_as_347_);
lean_dec(v_declName_346_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(uint8_t v_isRoot_354_, uint8_t v___x_355_, lean_object* v_as_356_, size_t v_i_357_, size_t v_stop_358_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = lean_usize_dec_eq(v_i_357_, v_stop_358_);
if (v___x_359_ == 0)
{
uint8_t v___x_360_; uint8_t v___y_362_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_360_ = 1;
v___x_366_ = lean_array_uget_borrowed(v_as_356_, v_i_357_);
v___x_367_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v___x_366_);
if (v___x_367_ == 0)
{
v___y_362_ = v_isRoot_354_;
goto v___jp_361_;
}
else
{
v___y_362_ = v___x_355_;
goto v___jp_361_;
}
v___jp_361_:
{
if (v___y_362_ == 0)
{
size_t v___x_363_; size_t v___x_364_; 
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_add(v_i_357_, v___x_363_);
v_i_357_ = v___x_364_;
goto _start;
}
else
{
return v___x_360_;
}
}
}
else
{
uint8_t v___x_368_; 
v___x_368_ = 0;
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object* v_isRoot_369_, lean_object* v___x_370_, lean_object* v_as_371_, lean_object* v_i_372_, lean_object* v_stop_373_){
_start:
{
uint8_t v_isRoot_boxed_374_; uint8_t v___x_15167__boxed_375_; size_t v_i_boxed_376_; size_t v_stop_boxed_377_; uint8_t v_res_378_; lean_object* v_r_379_; 
v_isRoot_boxed_374_ = lean_unbox(v_isRoot_369_);
v___x_15167__boxed_375_ = lean_unbox(v___x_370_);
v_i_boxed_376_ = lean_unbox_usize(v_i_372_);
lean_dec(v_i_372_);
v_stop_boxed_377_ = lean_unbox_usize(v_stop_373_);
lean_dec(v_stop_373_);
v_res_378_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_boxed_374_, v___x_15167__boxed_375_, v_as_371_, v_i_boxed_376_, v_stop_boxed_377_);
lean_dec_ref(v_as_371_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0(void){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = lean_cstr_to_nat("9223372036854775808");
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(uint8_t v___x_381_, lean_object* v_as_382_, size_t v_i_383_, size_t v_stop_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
uint8_t v___x_392_; 
v___x_392_ = lean_usize_dec_eq(v_i_383_, v_stop_384_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = 1;
v___x_394_ = lean_array_uget_borrowed(v_as_382_, v_i_383_);
lean_inc(v___x_394_);
v___x_395_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_394_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_412_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_412_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_412_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_412_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
uint8_t v___x_400_; 
v___x_400_ = lean_unbox(v_a_396_);
lean_dec(v_a_396_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_box(v___x_393_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_401_);
v___x_403_ = v___x_398_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
else
{
if (v___x_381_ == 0)
{
size_t v___x_405_; size_t v___x_406_; 
lean_del_object(v___x_398_);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_add(v_i_383_, v___x_405_);
v_i_383_ = v___x_406_;
goto _start;
}
else
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_box(v___x_393_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_408_);
v___x_410_ = v___x_398_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
else
{
return v___x_395_;
}
}
else
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = 0;
v___x_414_ = lean_box(v___x_413_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(lean_object* v_as_416_, size_t v_i_417_, size_t v_stop_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = lean_usize_dec_eq(v_i_417_, v_stop_418_);
if (v___x_426_ == 0)
{
uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = 1;
v___x_428_ = lean_array_uget_borrowed(v_as_416_, v_i_417_);
lean_inc(v___x_428_);
v___x_429_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_428_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_442_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_442_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_442_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_442_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint8_t v___x_434_; 
v___x_434_ = lean_unbox(v_a_430_);
lean_dec(v_a_430_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = lean_box(v___x_427_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_435_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
else
{
size_t v___x_439_; size_t v___x_440_; 
lean_del_object(v___x_432_);
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_i_417_, v___x_439_);
v_i_417_ = v___x_440_;
goto _start;
}
}
}
else
{
return v___x_429_;
}
}
else
{
uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = 0;
v___x_444_ = lean_box(v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t v_isRoot_446_, lean_object* v_v_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
switch(lean_obj_tag(v_v_447_))
{
case 0:
{
lean_object* v_value_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_504_; 
v_value_459_ = lean_ctor_get(v_v_447_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v_v_447_);
if (v_isSharedCheck_504_ == 0)
{
v___x_461_ = v_v_447_;
v_isShared_462_ = v_isSharedCheck_504_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_value_459_);
lean_dec(v_v_447_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_504_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
switch(lean_obj_tag(v_value_459_))
{
case 1:
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_471_; 
lean_del_object(v___x_461_);
v_isSharedCheck_471_ = !lean_is_exclusive(v_value_459_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v_value_459_, 0);
lean_dec(v_unused_472_);
v___x_464_ = v_value_459_;
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
else
{
lean_dec(v_value_459_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = 1;
v___x_467_ = lean_box(v___x_466_);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 0);
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
case 0:
{
lean_del_object(v___x_461_);
if (v_isRoot_446_ == 0)
{
lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_481_; 
v_isSharedCheck_481_ = !lean_is_exclusive(v_value_459_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; 
v_unused_482_ = lean_ctor_get(v_value_459_, 0);
lean_dec(v_unused_482_);
v___x_474_ = v_value_459_;
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
else
{
lean_dec(v_value_459_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = 1;
v___x_477_ = lean_box(v___x_476_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_477_);
v___x_479_ = v___x_474_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_object* v_val_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_493_; 
v_val_483_ = lean_ctor_get(v_value_459_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_value_459_);
if (v_isSharedCheck_493_ == 0)
{
v___x_485_ = v_value_459_;
v_isShared_486_ = v_isSharedCheck_493_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_val_483_);
lean_dec(v_value_459_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_493_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_487_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0, &l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0);
v___x_488_ = lean_nat_dec_le(v___x_487_, v_val_483_);
lean_dec(v_val_483_);
v___x_489_ = lean_box(v___x_488_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_489_);
v___x_491_ = v___x_485_;
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
}
default: 
{
lean_dec_ref(v_value_459_);
if (v_isRoot_446_ == 0)
{
uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_494_ = 1;
v___x_495_ = lean_box(v___x_494_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_495_);
v___x_497_ = v___x_461_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
else
{
uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_499_ = 0;
v___x_500_ = lean_box(v___x_499_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_500_);
v___x_502_ = v___x_461_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
case 1:
{
if (v_isRoot_446_ == 0)
{
uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = 1;
v___x_506_ = lean_box(v___x_505_);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
else
{
uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = 0;
v___x_509_ = lean_box(v___x_508_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
case 2:
{
lean_object* v_struct_511_; lean_object* v___x_512_; 
v_struct_511_ = lean_ctor_get(v_v_447_, 2);
lean_inc(v_struct_511_);
lean_dec_ref_known(v_v_447_, 3);
v___x_512_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_struct_511_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
return v___x_512_;
}
case 3:
{
lean_object* v_declName_513_; lean_object* v_args_514_; lean_object* v_sccDecls_515_; lean_object* v___x_516_; uint8_t v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; uint8_t v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; uint8_t v___y_570_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_declName_513_ = lean_ctor_get(v_v_447_, 0);
lean_inc(v_declName_513_);
v_args_514_ = lean_ctor_get(v_v_447_, 2);
lean_inc_ref(v_args_514_);
lean_dec_ref_known(v_v_447_, 3);
v_sccDecls_515_ = lean_ctor_get(v_a_448_, 1);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_array_get_size(v_sccDecls_515_);
v___x_615_ = lean_nat_dec_lt(v___x_516_, v___x_614_);
if (v___x_615_ == 0)
{
v___y_570_ = v___x_615_;
goto v___jp_569_;
}
else
{
if (v___x_615_ == 0)
{
v___y_570_ = v___x_615_;
goto v___jp_569_;
}
else
{
size_t v___x_616_; size_t v___x_617_; uint8_t v___x_618_; 
v___x_616_ = ((size_t)0ULL);
v___x_617_ = lean_usize_of_nat(v___x_614_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_513_, v_sccDecls_515_, v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
v___y_570_ = v___x_618_;
goto v___jp_569_;
}
else
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec_ref(v_args_514_);
lean_dec(v_declName_513_);
v___x_619_ = 0;
v___x_620_ = lean_box(v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
v___jp_517_:
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_array_get_size(v_args_514_);
v___x_526_ = lean_nat_dec_lt(v___x_516_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec_ref(v_args_514_);
goto v___jp_455_;
}
else
{
if (v___x_526_ == 0)
{
lean_dec_ref(v_args_514_);
goto v___jp_455_;
}
else
{
size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
v___x_527_ = ((size_t)0ULL);
v___x_528_ = lean_usize_of_nat(v___x_525_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___y_518_, v_args_514_, v___x_527_, v___x_528_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec_ref(v_args_514_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_539_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_539_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
uint8_t v___x_534_; 
v___x_534_ = lean_unbox(v_a_530_);
lean_dec(v_a_530_);
if (v___x_534_ == 0)
{
lean_del_object(v___x_532_);
goto v___jp_455_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_box(v___y_518_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_535_);
v___x_537_ = v___x_532_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
return v___x_529_;
}
}
}
}
v___jp_540_:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_513_, v___y_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_560_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_560_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_560_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_560_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
if (lean_obj_tag(v_a_549_) == 1)
{
lean_object* v_val_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_val_553_ = lean_ctor_get(v_a_549_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v_a_549_, 1);
v___x_554_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_553_);
lean_dec(v_val_553_);
v___x_555_ = lean_nat_dec_eq(v___x_554_, v___x_516_);
lean_dec(v___x_554_);
if (v___x_555_ == 0)
{
lean_del_object(v___x_551_);
v___y_518_ = v___y_541_;
v___y_519_ = v___y_542_;
v___y_520_ = v___y_543_;
v___y_521_ = v___y_544_;
v___y_522_ = v___y_545_;
v___y_523_ = v___y_546_;
v___y_524_ = v___y_547_;
goto v___jp_517_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_558_; 
lean_dec_ref(v_args_514_);
v___x_556_ = lean_box(v___y_541_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_556_);
v___x_558_ = v___x_551_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
else
{
lean_del_object(v___x_551_);
lean_dec(v_a_549_);
v___y_518_ = v___y_541_;
v___y_519_ = v___y_542_;
v___y_520_ = v___y_543_;
v___y_521_ = v___y_544_;
v___y_522_ = v___y_545_;
v___y_523_ = v___y_546_;
v___y_524_ = v___y_547_;
goto v___jp_517_;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec_ref(v_args_514_);
v_a_561_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_548_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_548_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
v___jp_569_:
{
lean_object* v___x_571_; lean_object* v_env_572_; uint8_t v___x_573_; 
v___x_571_ = lean_st_ref_get(v_a_453_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_env_572_);
lean_dec(v___x_571_);
lean_inc(v_declName_513_);
v___x_573_ = l_Lean_hasNeverExtractAttribute(v_env_572_, v_declName_513_);
if (v___x_573_ == 0)
{
if (v_isRoot_446_ == 0)
{
lean_dec(v_declName_513_);
v___y_518_ = v___x_573_;
v___y_519_ = v_a_448_;
v___y_520_ = v_a_449_;
v___y_521_ = v_a_450_;
v___y_522_ = v_a_451_;
v___y_523_ = v_a_452_;
v___y_524_ = v_a_453_;
goto v___jp_517_;
}
else
{
lean_object* v___x_574_; lean_object* v_env_575_; lean_object* v___x_576_; 
v___x_574_ = lean_st_ref_get(v_a_453_);
v_env_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_env_575_);
lean_dec(v___x_574_);
lean_inc(v_declName_513_);
v___x_576_ = l_Lean_Environment_find_x3f(v_env_575_, v_declName_513_, v___x_573_);
if (lean_obj_tag(v___x_576_) == 1)
{
lean_object* v_val_577_; 
v_val_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_val_577_);
lean_dec_ref_known(v___x_576_, 1);
switch(lean_obj_tag(v_val_577_))
{
case 1:
{
lean_object* v_val_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_589_; 
v_val_578_ = lean_ctor_get(v_val_577_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v_val_577_);
if (v_isSharedCheck_589_ == 0)
{
v___x_580_ = v_val_577_;
v_isShared_581_ = v_isSharedCheck_589_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_val_578_);
lean_dec(v_val_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_589_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_toConstantVal_582_; lean_object* v_type_583_; uint8_t v___x_584_; 
v_toConstantVal_582_ = lean_ctor_get(v_val_578_, 0);
lean_inc_ref(v_toConstantVal_582_);
lean_dec_ref(v_val_578_);
v_type_583_ = lean_ctor_get(v_toConstantVal_582_, 2);
lean_inc_ref(v_type_583_);
lean_dec_ref(v_toConstantVal_582_);
v___x_584_ = l_Lean_Expr_isForall(v_type_583_);
lean_dec_ref(v_type_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_587_; 
lean_dec_ref(v_args_514_);
lean_dec(v_declName_513_);
v___x_585_ = lean_box(v___x_573_);
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 0);
lean_ctor_set(v___x_580_, 0, v___x_585_);
v___x_587_ = v___x_580_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
lean_del_object(v___x_580_);
v___y_541_ = v___x_573_;
v___y_542_ = v_a_448_;
v___y_543_ = v_a_449_;
v___y_544_ = v_a_450_;
v___y_545_ = v_a_451_;
v___y_546_ = v_a_452_;
v___y_547_ = v_a_453_;
goto v___jp_540_;
}
}
}
case 6:
{
lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_610_; 
v_isSharedCheck_610_ = !lean_is_exclusive(v_val_577_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v_val_577_, 0);
lean_dec(v_unused_611_);
v___x_591_ = v_val_577_;
v_isShared_592_ = v_isSharedCheck_610_;
goto v_resetjp_590_;
}
else
{
lean_dec(v_val_577_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_610_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_array_get_size(v_args_514_);
v___x_594_ = lean_nat_dec_lt(v___x_516_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_597_; 
lean_dec_ref(v_args_514_);
lean_dec(v_declName_513_);
v___x_595_ = lean_box(v___x_573_);
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 0);
lean_ctor_set(v___x_591_, 0, v___x_595_);
v___x_597_ = v___x_591_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
else
{
if (v___x_594_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_601_; 
lean_dec_ref(v_args_514_);
lean_dec(v_declName_513_);
v___x_599_ = lean_box(v___x_573_);
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 0);
lean_ctor_set(v___x_591_, 0, v___x_599_);
v___x_601_ = v___x_591_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
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
size_t v___x_603_; size_t v___x_604_; uint8_t v___x_605_; 
v___x_603_ = ((size_t)0ULL);
v___x_604_ = lean_usize_of_nat(v___x_593_);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_446_, v___x_573_, v_args_514_, v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_608_; 
lean_dec_ref(v_args_514_);
lean_dec(v_declName_513_);
v___x_606_ = lean_box(v___x_573_);
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 0);
lean_ctor_set(v___x_591_, 0, v___x_606_);
v___x_608_ = v___x_591_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
else
{
lean_del_object(v___x_591_);
v___y_541_ = v___x_573_;
v___y_542_ = v_a_448_;
v___y_543_ = v_a_449_;
v___y_544_ = v_a_450_;
v___y_545_ = v_a_451_;
v___y_546_ = v_a_452_;
v___y_547_ = v_a_453_;
goto v___jp_540_;
}
}
}
}
}
default: 
{
lean_dec(v_val_577_);
v___y_541_ = v___x_573_;
v___y_542_ = v_a_448_;
v___y_543_ = v_a_449_;
v___y_544_ = v_a_450_;
v___y_545_ = v_a_451_;
v___y_546_ = v_a_452_;
v___y_547_ = v_a_453_;
goto v___jp_540_;
}
}
}
else
{
lean_dec(v___x_576_);
v___y_541_ = v___x_573_;
v___y_542_ = v_a_448_;
v___y_543_ = v_a_449_;
v___y_544_ = v_a_450_;
v___y_545_ = v_a_451_;
v___y_546_ = v_a_452_;
v___y_547_ = v_a_453_;
goto v___jp_540_;
}
}
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec_ref(v_args_514_);
lean_dec(v_declName_513_);
v___x_612_ = lean_box(v___y_570_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
}
default: 
{
lean_object* v_fvarId_622_; lean_object* v_args_623_; lean_object* v___x_624_; 
v_fvarId_622_ = lean_ctor_get(v_v_447_, 0);
lean_inc(v_fvarId_622_);
v_args_623_ = lean_ctor_get(v_v_447_, 1);
lean_inc_ref(v_args_623_);
lean_dec_ref_known(v_v_447_, 2);
v___x_624_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_622_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___y_627_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_array_get_size(v_args_623_);
v___x_639_ = lean_nat_dec_lt(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec_ref(v_args_623_);
v___x_640_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_639_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
v___y_627_ = v___x_640_;
goto v___jp_626_;
}
else
{
if (v___x_639_ == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v_args_623_);
v___x_641_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_639_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
v___y_627_ = v___x_641_;
goto v___jp_626_;
}
else
{
size_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
v___x_642_ = ((size_t)0ULL);
v___x_643_ = lean_usize_of_nat(v___x_638_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_args_623_, v___x_642_, v___x_643_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec_ref(v_args_623_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; uint8_t v___x_646_; lean_object* v___x_647_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___x_646_ = lean_unbox(v_a_645_);
lean_dec(v_a_645_);
v___x_647_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_646_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
v___y_627_ = v___x_647_;
goto v___jp_626_;
}
else
{
lean_dec(v_a_625_);
return v___x_644_;
}
}
}
v___jp_626_:
{
if (lean_obj_tag(v___y_627_) == 0)
{
uint8_t v___x_628_; 
v___x_628_ = lean_unbox(v_a_625_);
if (v___x_628_ == 0)
{
lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
v_isSharedCheck_635_ = !lean_is_exclusive(v___y_627_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v___y_627_, 0);
lean_dec(v_unused_636_);
v___x_630_ = v___y_627_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_dec(v___y_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v_a_625_);
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_625_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
else
{
lean_dec(v_a_625_);
return v___y_627_;
}
}
else
{
lean_dec(v_a_625_);
return v___y_627_;
}
}
}
else
{
lean_dec_ref(v_args_623_);
return v___x_624_;
}
}
}
v___jp_455_:
{
uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = 1;
v___x_457_ = lean_box(v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(lean_object* v_fvarId_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
uint8_t v___x_656_; lean_object* v___x_657_; 
v___x_656_ = 0;
v___x_657_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_656_, v_fvarId_648_, v_a_652_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_671_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_671_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_671_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_671_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
if (lean_obj_tag(v_a_658_) == 1)
{
lean_object* v_val_662_; lean_object* v_value_663_; uint8_t v___x_664_; lean_object* v___x_665_; 
lean_del_object(v___x_660_);
v_val_662_ = lean_ctor_get(v_a_658_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v_a_658_, 1);
v_value_663_ = lean_ctor_get(v_val_662_, 3);
lean_inc(v_value_663_);
lean_dec(v_val_662_);
v___x_664_ = 0;
v___x_665_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_664_, v_value_663_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
return v___x_665_;
}
else
{
uint8_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
lean_dec(v_a_658_);
v___x_666_ = 0;
v___x_667_ = lean_box(v___x_666_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_667_);
v___x_669_ = v___x_660_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
v_a_672_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_657_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_657_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object* v_fvarId_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; lean_object* v_fvarDecisionCache_689_; lean_object* v___x_690_; 
v___x_688_ = lean_st_ref_get(v_a_682_);
v_fvarDecisionCache_689_ = lean_ctor_get(v___x_688_, 1);
lean_inc_ref(v_fvarDecisionCache_689_);
lean_dec(v___x_688_);
v___x_690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_fvarDecisionCache_689_, v_fvarId_680_);
lean_dec_ref(v_fvarDecisionCache_689_);
if (lean_obj_tag(v___x_690_) == 1)
{
lean_object* v_val_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v_fvarId_680_);
v_val_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_val_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 0);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_val_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
else
{
lean_object* v___x_699_; 
lean_dec(v___x_690_);
v___x_699_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_719_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_719_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_719_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_719_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v_decls_705_; lean_object* v_fvarDecisionCache_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_718_; 
v___x_704_ = lean_st_ref_take(v_a_682_);
v_decls_705_ = lean_ctor_get(v___x_704_, 0);
v_fvarDecisionCache_706_ = lean_ctor_get(v___x_704_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_718_ == 0)
{
v___x_708_ = v___x_704_;
v_isShared_709_ = v_isSharedCheck_718_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_fvarDecisionCache_706_);
lean_inc(v_decls_705_);
lean_dec(v___x_704_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_718_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
lean_inc(v_a_700_);
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_fvarDecisionCache_706_, v_fvarId_680_, v_a_700_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_decls_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_717_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_st_ref_put(v_a_682_, v___x_712_);
if (v_isShared_703_ == 0)
{
v___x_715_ = v___x_702_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_700_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_680_);
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object* v_arg_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
if (lean_obj_tag(v_arg_720_) == 1)
{
lean_object* v_fvarId_728_; lean_object* v___x_729_; 
v_fvarId_728_ = lean_ctor_get(v_arg_720_, 0);
lean_inc(v_fvarId_728_);
lean_dec_ref_known(v_arg_720_, 1);
v___x_729_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_728_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
return v___x_729_;
}
else
{
uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec(v_arg_720_);
v___x_730_ = 1;
v___x_731_ = lean_box(v___x_730_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object* v_arg_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v_arg_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(lean_object* v_fvarId_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_fvarId_742_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(lean_object* v_as_751_, lean_object* v_i_752_, lean_object* v_stop_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
size_t v_i_boxed_761_; size_t v_stop_boxed_762_; lean_object* v_res_763_; 
v_i_boxed_761_ = lean_unbox_usize(v_i_752_);
lean_dec(v_i_752_);
v_stop_boxed_762_ = lean_unbox_usize(v_stop_753_);
lean_dec(v_stop_753_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_as_751_, v_i_boxed_761_, v_stop_boxed_762_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec_ref(v_as_751_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object* v___x_764_, lean_object* v_as_765_, lean_object* v_i_766_, lean_object* v_stop_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
uint8_t v___x_15226__boxed_775_; size_t v_i_boxed_776_; size_t v_stop_boxed_777_; lean_object* v_res_778_; 
v___x_15226__boxed_775_ = lean_unbox(v___x_764_);
v_i_boxed_776_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_stop_boxed_777_ = lean_unbox_usize(v_stop_767_);
lean_dec(v_stop_767_);
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___x_15226__boxed_775_, v_as_765_, v_i_boxed_776_, v_stop_boxed_777_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec_ref(v_as_765_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object* v_fvarId_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object* v_isRoot_788_, lean_object* v_v_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
uint8_t v_isRoot_boxed_797_; lean_object* v_res_798_; 
v_isRoot_boxed_797_ = lean_unbox(v_isRoot_788_);
v_res_798_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v_isRoot_boxed_797_, v_v_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object* v_00_u03b2_799_, lean_object* v_m_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_800_, v_a_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___boxed(lean_object* v_00_u03b2_803_, lean_object* v_m_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(v_00_u03b2_803_, v_m_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_m_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(lean_object* v_00_u03b2_807_, lean_object* v_m_808_, lean_object* v_a_809_, lean_object* v_b_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_m_808_, v_a_809_, v_b_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(lean_object* v_00_u03b2_812_, lean_object* v_a_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___boxed(lean_object* v_00_u03b2_816_, lean_object* v_a_817_, lean_object* v_x_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(v_00_u03b2_816_, v_a_817_, v_x_818_);
lean_dec(v_x_818_);
lean_dec(v_a_817_);
return v_res_819_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(lean_object* v_00_u03b2_820_, lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
uint8_t v___x_823_; 
v___x_823_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_821_, v_x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___boxed(lean_object* v_00_u03b2_824_, lean_object* v_a_825_, lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(v_00_u03b2_824_, v_a_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec(v_a_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10(lean_object* v_00_u03b2_829_, lean_object* v_data_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_data_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11(lean_object* v_00_u03b2_832_, lean_object* v_a_833_, lean_object* v_b_834_, lean_object* v_x_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_833_, v_b_834_, v_x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_837_, lean_object* v_i_838_, lean_object* v_source_839_, lean_object* v_target_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v_i_838_, v_source_839_, v_target_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_842_, lean_object* v_x_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_x_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(lean_object* v_prevArrayId_851_, lean_object* v_decl_852_, lean_object* v_k_853_, lean_object* v_illegalSet_854_, lean_object* v_size_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_decl_867_; lean_object* v_k_868_; lean_object* v_illegalSet_869_; lean_object* v_zero_877_; uint8_t v_isZero_878_; 
v_zero_877_ = lean_unsigned_to_nat(0u);
v_isZero_878_ = lean_nat_dec_eq(v_size_855_, v_zero_877_);
if (v_isZero_878_ == 1)
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec(v_size_855_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
lean_dec(v_prevArrayId_851_);
v___x_879_ = lean_box(0);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
else
{
lean_object* v_value_881_; 
v_value_881_ = lean_ctor_get(v_decl_852_, 3);
if (lean_obj_tag(v_value_881_) == 3)
{
lean_object* v_declName_882_; 
v_declName_882_ = lean_ctor_get(v_value_881_, 0);
if (lean_obj_tag(v_declName_882_) == 1)
{
lean_object* v_pre_883_; 
v_pre_883_ = lean_ctor_get(v_declName_882_, 0);
if (lean_obj_tag(v_pre_883_) == 1)
{
lean_object* v_pre_884_; 
v_pre_884_ = lean_ctor_get(v_pre_883_, 0);
if (lean_obj_tag(v_pre_884_) == 0)
{
lean_object* v_fvarId_885_; lean_object* v_args_886_; lean_object* v_str_887_; lean_object* v_str_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v_fvarId_885_ = lean_ctor_get(v_decl_852_, 0);
v_args_886_ = lean_ctor_get(v_value_881_, 2);
v_str_887_ = lean_ctor_get(v_declName_882_, 1);
v_str_888_ = lean_ctor_get(v_pre_883_, 1);
v___x_889_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_890_ = lean_string_dec_eq(v_str_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_dec(v_size_855_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
lean_dec(v_prevArrayId_851_);
goto v___jp_863_;
}
else
{
lean_object* v___x_891_; uint8_t v___x_892_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_892_ = lean_string_dec_eq(v_str_887_, v___x_891_);
if (v___x_892_ == 0)
{
lean_dec(v_size_855_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
lean_dec(v_prevArrayId_851_);
goto v___jp_863_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = lean_array_get_size(v_args_886_);
v___x_894_ = lean_unsigned_to_nat(3u);
v___x_895_ = lean_nat_dec_eq(v___x_893_, v___x_894_);
if (v___x_895_ == 0)
{
lean_dec(v_size_855_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
lean_dec(v_prevArrayId_851_);
goto v___jp_863_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_array_fget(v_args_886_, v___x_896_);
if (lean_obj_tag(v___x_897_) == 1)
{
lean_object* v_fvarId_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_1015_; 
v_fvarId_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_1015_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_fvarId_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_1015_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
uint8_t v___x_902_; 
v___x_902_ = l_Lean_instBEqFVarId_beq(v_fvarId_898_, v_prevArrayId_851_);
lean_dec(v_prevArrayId_851_);
lean_dec(v_fvarId_898_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_905_; 
lean_dec(v_size_855_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
v___x_903_ = lean_box(0);
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 0);
lean_ctor_set(v___x_900_, 0, v___x_903_);
v___x_905_ = v___x_900_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
else
{
lean_object* v_n_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_del_object(v___x_900_);
v_n_907_ = lean_nat_sub(v_size_855_, v___x_896_);
lean_dec(v_size_855_);
v___x_908_ = lean_unsigned_to_nat(2u);
v___x_909_ = lean_array_fget_borrowed(v_args_886_, v___x_908_);
lean_inc(v___x_909_);
v___x_910_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_909_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_1006_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_1006_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_1006_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
uint8_t v___x_915_; 
v___x_915_ = lean_unbox(v_a_911_);
lean_dec(v_a_911_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_918_; 
lean_dec(v_n_907_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
v___x_916_ = lean_box(0);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_916_);
v___x_918_ = v___x_913_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
else
{
uint8_t v___x_920_; 
v___x_920_ = lean_nat_dec_eq(v_n_907_, v_zero_877_);
if (v___x_920_ == 0)
{
lean_inc(v_fvarId_885_);
lean_dec_ref(v_decl_852_);
if (lean_obj_tag(v_k_853_) == 0)
{
lean_object* v_decl_921_; lean_object* v_k_922_; lean_object* v___x_923_; 
lean_del_object(v___x_913_);
v_decl_921_ = lean_ctor_get(v_k_853_, 0);
lean_inc_ref(v_decl_921_);
v_k_922_ = lean_ctor_get(v_k_853_, 1);
lean_inc_ref(v_k_922_);
lean_dec_ref_known(v_k_853_, 2);
lean_inc(v_fvarId_885_);
v___x_923_ = l_Lean_FVarIdSet_insert(v_illegalSet_854_, v_fvarId_885_);
v_prevArrayId_851_ = v_fvarId_885_;
v_decl_852_ = v_decl_921_;
v_k_853_ = v_k_922_;
v_illegalSet_854_ = v___x_923_;
v_size_855_ = v_n_907_;
goto _start;
}
else
{
lean_object* v___x_925_; lean_object* v___x_927_; 
lean_dec(v_n_907_);
lean_dec(v_fvarId_885_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
v___x_925_ = lean_box(0);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_925_);
v___x_927_ = v___x_913_;
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
else
{
lean_del_object(v___x_913_);
lean_dec(v_n_907_);
if (lean_obj_tag(v_k_853_) == 0)
{
lean_object* v_decl_929_; lean_object* v_value_930_; 
v_decl_929_ = lean_ctor_get(v_k_853_, 0);
lean_inc_ref(v_decl_929_);
v_value_930_ = lean_ctor_get(v_decl_929_, 3);
lean_inc(v_value_930_);
if (lean_obj_tag(v_value_930_) == 3)
{
lean_object* v_declName_931_; 
v_declName_931_ = lean_ctor_get(v_value_930_, 0);
lean_inc(v_declName_931_);
if (lean_obj_tag(v_declName_931_) == 1)
{
lean_object* v_pre_932_; 
v_pre_932_ = lean_ctor_get(v_declName_931_, 0);
lean_inc(v_pre_932_);
if (lean_obj_tag(v_pre_932_) == 1)
{
lean_object* v_pre_933_; 
v_pre_933_ = lean_ctor_get(v_pre_932_, 0);
lean_inc(v_pre_933_);
if (lean_obj_tag(v_pre_933_) == 0)
{
lean_object* v_k_934_; lean_object* v_fvarId_935_; lean_object* v_binderName_936_; lean_object* v_type_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_1004_; 
v_k_934_ = lean_ctor_get(v_k_853_, 1);
v_fvarId_935_ = lean_ctor_get(v_decl_929_, 0);
v_binderName_936_ = lean_ctor_get(v_decl_929_, 1);
v_type_937_ = lean_ctor_get(v_decl_929_, 2);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_decl_929_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; 
v_unused_1005_ = lean_ctor_get(v_decl_929_, 3);
lean_dec(v_unused_1005_);
v___x_939_ = v_decl_929_;
v_isShared_940_ = v_isSharedCheck_1004_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_type_937_);
lean_inc(v_binderName_936_);
lean_inc(v_fvarId_935_);
lean_dec(v_decl_929_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_1004_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_us_941_; lean_object* v_args_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_1002_; 
v_us_941_ = lean_ctor_get(v_value_930_, 1);
v_args_942_ = lean_ctor_get(v_value_930_, 2);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_value_930_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v_value_930_, 0);
lean_dec(v_unused_1003_);
v___x_944_ = v_value_930_;
v_isShared_945_ = v_isSharedCheck_1002_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_args_942_);
lean_inc(v_us_941_);
lean_dec(v_value_930_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_1002_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_str_946_; lean_object* v_str_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_str_946_ = lean_ctor_get(v_declName_931_, 1);
lean_inc_ref(v_str_946_);
lean_dec_ref_known(v_declName_931_, 2);
v_str_947_ = lean_ctor_get(v_pre_932_, 1);
lean_inc_ref(v_str_947_);
lean_dec_ref_known(v_pre_932_, 2);
v___x_948_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2));
v___x_949_ = lean_string_dec_eq(v_str_947_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3));
v___x_951_ = lean_string_dec_eq(v_str_947_, v___x_950_);
lean_dec_ref(v_str_947_);
if (v___x_951_ == 0)
{
lean_dec_ref(v_str_946_);
lean_del_object(v___x_944_);
lean_dec_ref(v_args_942_);
lean_dec(v_us_941_);
lean_del_object(v___x_939_);
lean_dec_ref(v_type_937_);
lean_dec(v_binderName_936_);
lean_dec(v_fvarId_935_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
else
{
lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_952_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_953_ = lean_string_dec_eq(v_str_946_, v___x_952_);
lean_dec_ref(v_str_946_);
if (v___x_953_ == 0)
{
lean_del_object(v___x_944_);
lean_dec_ref(v_args_942_);
lean_dec(v_us_941_);
lean_del_object(v___x_939_);
lean_dec_ref(v_type_937_);
lean_dec(v_binderName_936_);
lean_dec(v_fvarId_935_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
else
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_array_get_size(v_args_942_);
v___x_955_ = lean_nat_dec_eq(v___x_954_, v___x_896_);
if (v___x_955_ == 0)
{
lean_del_object(v___x_944_);
lean_dec_ref(v_args_942_);
lean_dec(v_us_941_);
lean_del_object(v___x_939_);
lean_dec_ref(v_type_937_);
lean_dec(v_binderName_936_);
lean_dec(v_fvarId_935_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
else
{
lean_object* v___x_956_; 
v___x_956_ = lean_array_fget(v_args_942_, v_zero_877_);
lean_dec_ref(v_args_942_);
if (lean_obj_tag(v___x_956_) == 1)
{
lean_object* v_fvarId_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_976_; 
v_fvarId_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_976_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_976_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_fvarId_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_976_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
uint8_t v___x_961_; 
v___x_961_ = l_Lean_instBEqFVarId_beq(v_fvarId_957_, v_fvarId_885_);
if (v___x_961_ == 0)
{
lean_del_object(v___x_959_);
lean_dec(v_fvarId_957_);
lean_del_object(v___x_944_);
lean_dec(v_us_941_);
lean_del_object(v___x_939_);
lean_dec_ref(v_type_937_);
lean_dec(v_binderName_936_);
lean_dec(v_fvarId_935_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
lean_inc_ref(v_k_934_);
lean_inc(v_fvarId_885_);
lean_dec_ref_known(v_k_853_, 2);
lean_dec_ref(v_decl_852_);
v___x_962_ = l_Lean_Name_str___override(v_pre_933_, v___x_950_);
v___x_963_ = l_Lean_Name_str___override(v___x_962_, v___x_952_);
if (v_isShared_960_ == 0)
{
v___x_965_ = v___x_959_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_fvarId_957_);
v___x_965_ = v_reuseFailAlloc_975_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = lean_mk_empty_array_with_capacity(v___x_896_);
v___x_967_ = lean_array_push(v___x_966_, v___x_965_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 2, v___x_967_);
lean_ctor_set(v___x_944_, 0, v___x_963_);
v___x_969_ = v___x_944_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_us_941_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v___x_967_);
v___x_969_ = v_reuseFailAlloc_974_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 3, v___x_969_);
v___x_971_ = v___x_939_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_fvarId_935_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_binderName_936_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_type_937_);
lean_ctor_set(v_reuseFailAlloc_973_, 3, v___x_969_);
v___x_971_ = v_reuseFailAlloc_973_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_FVarIdSet_insert(v_illegalSet_854_, v_fvarId_885_);
v_decl_867_ = v___x_971_;
v_k_868_ = v_k_934_;
v_illegalSet_869_ = v___x_972_;
goto v___jp_866_;
}
}
}
}
}
}
else
{
lean_dec(v___x_956_);
lean_del_object(v___x_944_);
lean_dec(v_us_941_);
lean_del_object(v___x_939_);
lean_dec_ref(v_type_937_);
lean_dec(v_binderName_936_);
lean_dec(v_fvarId_935_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
}
}
}
}
else
{
lean_object* v___x_977_; uint8_t v___x_978_; 
lean_dec_ref(v_str_947_);
v___x_977_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_978_ = lean_string_dec_eq(v_str_946_, v___x_977_);
lean_dec_ref(v_str_946_);
if (v___x_978_ == 0)
{
lean_del_object(v___x_944_);
lean_dec_ref(v_args_942_);
lean_dec(v_us_941_);
lean_del_object(v___x_939_);
lean_dec_ref(v_type_937_);
lean_dec(v_binderName_936_);
lean_dec(v_fvarId_935_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
else
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = lean_array_get_size(v_args_942_);
v___x_980_ = lean_nat_dec_eq(v___x_979_, v___x_896_);
if (v___x_980_ == 0)
{
lean_del_object(v___x_944_);
lean_dec_ref(v_args_942_);
lean_dec(v_us_941_);
lean_del_object(v___x_939_);
lean_dec_ref(v_type_937_);
lean_dec(v_binderName_936_);
lean_dec(v_fvarId_935_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
else
{
lean_object* v___x_981_; 
v___x_981_ = lean_array_fget(v_args_942_, v_zero_877_);
lean_dec_ref(v_args_942_);
if (lean_obj_tag(v___x_981_) == 1)
{
lean_object* v_fvarId_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1001_; 
v_fvarId_982_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_984_ = v___x_981_;
v_isShared_985_ = v_isSharedCheck_1001_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_fvarId_982_);
lean_dec(v___x_981_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1001_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
uint8_t v___x_986_; 
v___x_986_ = l_Lean_instBEqFVarId_beq(v_fvarId_982_, v_fvarId_885_);
if (v___x_986_ == 0)
{
lean_del_object(v___x_984_);
lean_dec(v_fvarId_982_);
lean_del_object(v___x_944_);
lean_dec(v_us_941_);
lean_del_object(v___x_939_);
lean_dec_ref(v_type_937_);
lean_dec(v_binderName_936_);
lean_dec(v_fvarId_935_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
lean_inc_ref(v_k_934_);
lean_inc(v_fvarId_885_);
lean_dec_ref_known(v_k_853_, 2);
lean_dec_ref(v_decl_852_);
v___x_987_ = l_Lean_Name_str___override(v_pre_933_, v___x_948_);
v___x_988_ = l_Lean_Name_str___override(v___x_987_, v___x_977_);
if (v_isShared_985_ == 0)
{
v___x_990_ = v___x_984_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_fvarId_982_);
v___x_990_ = v_reuseFailAlloc_1000_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_896_);
v___x_992_ = lean_array_push(v___x_991_, v___x_990_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 2, v___x_992_);
lean_ctor_set(v___x_944_, 0, v___x_988_);
v___x_994_ = v___x_944_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_us_941_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v___x_992_);
v___x_994_ = v_reuseFailAlloc_999_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_996_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 3, v___x_994_);
v___x_996_ = v___x_939_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_fvarId_935_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_binderName_936_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_type_937_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v___x_994_);
v___x_996_ = v_reuseFailAlloc_998_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_FVarIdSet_insert(v_illegalSet_854_, v_fvarId_885_);
v_decl_867_ = v___x_996_;
v_k_868_ = v_k_934_;
v_illegalSet_869_ = v___x_997_;
goto v___jp_866_;
}
}
}
}
}
}
else
{
lean_dec(v___x_981_);
lean_del_object(v___x_944_);
lean_dec(v_us_941_);
lean_del_object(v___x_939_);
lean_dec_ref(v_type_937_);
lean_dec(v_binderName_936_);
lean_dec(v_fvarId_935_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_932_, 2);
lean_dec(v_pre_933_);
lean_dec_ref_known(v_declName_931_, 2);
lean_dec_ref_known(v_value_930_, 3);
lean_dec_ref(v_decl_929_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
}
else
{
lean_dec(v_pre_932_);
lean_dec_ref_known(v_declName_931_, 2);
lean_dec_ref_known(v_value_930_, 3);
lean_dec_ref(v_decl_929_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
}
else
{
lean_dec_ref_known(v_value_930_, 3);
lean_dec(v_declName_931_);
lean_dec_ref(v_decl_929_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
}
else
{
lean_dec(v_value_930_);
lean_dec_ref(v_decl_929_);
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
}
else
{
v_decl_867_ = v_decl_852_;
v_k_868_ = v_k_853_;
v_illegalSet_869_ = v_illegalSet_854_;
goto v___jp_866_;
}
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec(v_n_907_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
v_a_1007_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_910_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_910_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
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
}
}
else
{
lean_dec(v___x_897_);
lean_dec(v_size_855_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
lean_dec(v_prevArrayId_851_);
goto v___jp_863_;
}
}
}
}
}
else
{
lean_dec(v_size_855_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
lean_dec(v_prevArrayId_851_);
goto v___jp_863_;
}
}
else
{
lean_dec(v_size_855_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
lean_dec(v_prevArrayId_851_);
goto v___jp_863_;
}
}
else
{
lean_dec(v_size_855_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
lean_dec(v_prevArrayId_851_);
goto v___jp_863_;
}
}
else
{
lean_dec(v_size_855_);
lean_dec(v_illegalSet_854_);
lean_dec_ref(v_k_853_);
lean_dec_ref(v_decl_852_);
lean_dec(v_prevArrayId_851_);
goto v___jp_863_;
}
}
v___jp_863_:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
v___jp_866_:
{
uint8_t v___x_870_; uint8_t v___x_871_; 
v___x_870_ = 0;
v___x_871_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_870_, v_k_868_, v_illegalSet_869_);
lean_dec(v_illegalSet_869_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v_decl_867_);
lean_ctor_set(v___x_872_, 1, v_k_868_);
v___x_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec_ref(v_k_868_);
lean_dec_ref(v_decl_867_);
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___boxed(lean_object* v_prevArrayId_1016_, lean_object* v_decl_1017_, lean_object* v_k_1018_, lean_object* v_illegalSet_1019_, lean_object* v_size_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_prevArrayId_1016_, v_decl_1017_, v_k_1018_, v_illegalSet_1019_, v_size_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(lean_object* v_decl_1031_, lean_object* v_k_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_value_1049_; 
v_value_1049_ = lean_ctor_get(v_decl_1031_, 3);
if (lean_obj_tag(v_value_1049_) == 3)
{
lean_object* v_declName_1050_; 
v_declName_1050_ = lean_ctor_get(v_value_1049_, 0);
if (lean_obj_tag(v_declName_1050_) == 1)
{
lean_object* v_pre_1051_; 
v_pre_1051_ = lean_ctor_get(v_declName_1050_, 0);
if (lean_obj_tag(v_pre_1051_) == 1)
{
lean_object* v_pre_1052_; 
v_pre_1052_ = lean_ctor_get(v_pre_1051_, 0);
if (lean_obj_tag(v_pre_1052_) == 0)
{
lean_object* v_args_1053_; lean_object* v_str_1054_; lean_object* v_str_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v_args_1053_ = lean_ctor_get(v_value_1049_, 2);
v_str_1054_ = lean_ctor_get(v_declName_1050_, 1);
v_str_1055_ = lean_ctor_get(v_pre_1051_, 1);
v___x_1056_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1057_ = lean_string_dec_eq(v_str_1055_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1046_;
}
else
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_1059_ = lean_string_dec_eq(v_str_1054_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1046_;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v___x_1060_ = lean_array_get_size(v_args_1053_);
v___x_1061_ = lean_unsigned_to_nat(3u);
v___x_1062_ = lean_nat_dec_eq(v___x_1060_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1046_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_array_fget_borrowed(v_args_1053_, v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 1)
{
lean_object* v_fvarId_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; 
v_fvarId_1065_ = lean_ctor_get(v___x_1064_, 0);
v___x_1066_ = lean_box(1);
v___x_1067_ = 0;
v___x_1068_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_1067_, v_fvarId_1065_, v_a_1036_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1123_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1123_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1123_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
if (lean_obj_tag(v_a_1069_) == 1)
{
lean_object* v_val_1073_; lean_object* v_fvarId_1074_; lean_object* v_value_1075_; lean_object* v_sizeFVar_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; 
lean_del_object(v___x_1071_);
v_val_1073_ = lean_ctor_get(v_a_1069_, 0);
lean_inc(v_val_1073_);
lean_dec_ref_known(v_a_1069_, 1);
v_fvarId_1074_ = lean_ctor_get(v_val_1073_, 0);
lean_inc(v_fvarId_1074_);
v_value_1075_ = lean_ctor_get(v_val_1073_, 3);
lean_inc(v_value_1075_);
lean_dec(v_val_1073_);
if (lean_obj_tag(v_value_1075_) == 3)
{
lean_object* v_declName_1098_; 
v_declName_1098_ = lean_ctor_get(v_value_1075_, 0);
lean_inc(v_declName_1098_);
if (lean_obj_tag(v_declName_1098_) == 1)
{
lean_object* v_pre_1099_; 
v_pre_1099_ = lean_ctor_get(v_declName_1098_, 0);
lean_inc(v_pre_1099_);
if (lean_obj_tag(v_pre_1099_) == 1)
{
lean_object* v_pre_1100_; 
v_pre_1100_ = lean_ctor_get(v_pre_1099_, 0);
if (lean_obj_tag(v_pre_1100_) == 0)
{
lean_object* v_args_1101_; lean_object* v_str_1102_; lean_object* v_str_1103_; uint8_t v___x_1104_; 
v_args_1101_ = lean_ctor_get(v_value_1075_, 2);
lean_inc_ref(v_args_1101_);
lean_dec_ref_known(v_value_1075_, 3);
v_str_1102_ = lean_ctor_get(v_declName_1098_, 1);
lean_inc_ref(v_str_1102_);
lean_dec_ref_known(v_declName_1098_, 2);
v_str_1103_ = lean_ctor_get(v_pre_1099_, 1);
lean_inc_ref(v_str_1103_);
lean_dec_ref_known(v_pre_1099_, 2);
v___x_1104_ = lean_string_dec_eq(v_str_1103_, v___x_1056_);
lean_dec_ref(v_str_1103_);
if (v___x_1104_ == 0)
{
lean_dec_ref(v_str_1102_);
lean_dec_ref(v_args_1101_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1043_;
}
else
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1106_ = lean_string_dec_eq(v_str_1102_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1108_ = lean_string_dec_eq(v_str_1102_, v___x_1107_);
lean_dec_ref(v_str_1102_);
if (v___x_1108_ == 0)
{
lean_dec_ref(v_args_1101_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1043_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1109_ = lean_array_get_size(v_args_1101_);
v___x_1110_ = lean_unsigned_to_nat(2u);
v___x_1111_ = lean_nat_dec_eq(v___x_1109_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v_args_1101_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1043_;
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_array_fget(v_args_1101_, v___x_1063_);
lean_dec_ref(v_args_1101_);
if (lean_obj_tag(v___x_1112_) == 1)
{
lean_object* v_fvarId_1113_; 
v_fvarId_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_fvarId_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v_sizeFVar_1077_ = v_fvarId_1113_;
v___y_1078_ = v_a_1033_;
v___y_1079_ = v_a_1034_;
v___y_1080_ = v_a_1035_;
v___y_1081_ = v_a_1036_;
v___y_1082_ = v_a_1037_;
v___y_1083_ = v_a_1038_;
goto v___jp_1076_;
}
else
{
lean_dec(v___x_1112_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1043_;
}
}
}
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
lean_dec_ref(v_str_1102_);
v___x_1114_ = lean_array_get_size(v_args_1101_);
v___x_1115_ = lean_unsigned_to_nat(2u);
v___x_1116_ = lean_nat_dec_eq(v___x_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v_args_1101_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1043_;
}
else
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_array_fget(v_args_1101_, v___x_1063_);
lean_dec_ref(v_args_1101_);
if (lean_obj_tag(v___x_1117_) == 1)
{
lean_object* v_fvarId_1118_; 
v_fvarId_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_fvarId_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v_sizeFVar_1077_ = v_fvarId_1118_;
v___y_1078_ = v_a_1033_;
v___y_1079_ = v_a_1034_;
v___y_1080_ = v_a_1035_;
v___y_1081_ = v_a_1036_;
v___y_1082_ = v_a_1037_;
v___y_1083_ = v_a_1038_;
goto v___jp_1076_;
}
else
{
lean_dec(v___x_1117_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1043_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1099_, 2);
lean_dec_ref_known(v_declName_1098_, 2);
lean_dec_ref_known(v_value_1075_, 3);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1043_;
}
}
else
{
lean_dec(v_pre_1099_);
lean_dec_ref_known(v_declName_1098_, 2);
lean_dec_ref_known(v_value_1075_, 3);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1043_;
}
}
else
{
lean_dec_ref_known(v_value_1075_, 3);
lean_dec(v_declName_1098_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1043_;
}
}
else
{
lean_dec(v_value_1075_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1043_;
}
v___jp_1076_:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1067_, v_sizeFVar_1077_, v___y_1081_);
lean_dec(v_sizeFVar_1077_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
if (lean_obj_tag(v_a_1085_) == 1)
{
lean_object* v_val_1086_; 
v_val_1086_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v_a_1085_, 1);
if (lean_obj_tag(v_val_1086_) == 0)
{
lean_object* v_value_1087_; 
v_value_1087_ = lean_ctor_get(v_val_1086_, 0);
lean_inc_ref(v_value_1087_);
lean_dec_ref_known(v_val_1086_, 1);
if (lean_obj_tag(v_value_1087_) == 0)
{
lean_object* v_val_1088_; lean_object* v___x_1089_; 
v_val_1088_ = lean_ctor_get(v_value_1087_, 0);
lean_inc(v_val_1088_);
lean_dec_ref_known(v_value_1087_, 1);
v___x_1089_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_fvarId_1074_, v_decl_1031_, v_k_1032_, v___x_1066_, v_val_1088_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1089_;
}
else
{
lean_dec_ref(v_value_1087_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1040_;
}
}
else
{
lean_dec(v_val_1086_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1040_;
}
}
else
{
lean_dec(v_a_1085_);
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1040_;
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_fvarId_1074_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
v_a_1090_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1084_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1084_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
lean_dec(v_a_1069_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
v___x_1119_ = lean_box(0);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1119_);
v___x_1121_ = v___x_1071_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
v_a_1124_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1068_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1068_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
else
{
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1046_;
}
}
}
}
}
else
{
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1046_;
}
}
else
{
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1046_;
}
}
else
{
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1046_;
}
}
else
{
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_decl_1031_);
goto v___jp_1046_;
}
v___jp_1040_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
v___jp_1043_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
v___jp_1046_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___boxed(lean_object* v_decl_1132_, lean_object* v_k_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1132_, v_k_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__0);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__1);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg(lean_object* v_env_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; lean_object* v_nextMacroScope_1151_; lean_object* v_ngen_1152_; lean_object* v_auxDeclNGen_1153_; lean_object* v_traceState_1154_; lean_object* v_recordedDeps_1155_; lean_object* v_messages_1156_; lean_object* v_infoState_1157_; lean_object* v_snapshotTasks_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1169_; 
v___x_1150_ = lean_st_ref_take(v___y_1148_);
v_nextMacroScope_1151_ = lean_ctor_get(v___x_1150_, 1);
v_ngen_1152_ = lean_ctor_get(v___x_1150_, 2);
v_auxDeclNGen_1153_ = lean_ctor_get(v___x_1150_, 3);
v_traceState_1154_ = lean_ctor_get(v___x_1150_, 4);
v_recordedDeps_1155_ = lean_ctor_get(v___x_1150_, 6);
v_messages_1156_ = lean_ctor_get(v___x_1150_, 7);
v_infoState_1157_ = lean_ctor_get(v___x_1150_, 8);
v_snapshotTasks_1158_ = lean_ctor_get(v___x_1150_, 9);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; lean_object* v_unused_1171_; 
v_unused_1170_ = lean_ctor_get(v___x_1150_, 5);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v___x_1150_, 0);
lean_dec(v_unused_1171_);
v___x_1160_ = v___x_1150_;
v_isShared_1161_ = v_isSharedCheck_1169_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snapshotTasks_1158_);
lean_inc(v_infoState_1157_);
lean_inc(v_messages_1156_);
lean_inc(v_recordedDeps_1155_);
lean_inc(v_traceState_1154_);
lean_inc(v_auxDeclNGen_1153_);
lean_inc(v_ngen_1152_);
lean_inc(v_nextMacroScope_1151_);
lean_dec(v___x_1150_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1169_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1162_ = lean_box(0);
v___x_1163_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___closed__2);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 5, v___x_1163_);
lean_ctor_set(v___x_1160_, 0, v_env_1147_);
v___x_1165_ = v___x_1160_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_env_1147_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_nextMacroScope_1151_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_ngen_1152_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_auxDeclNGen_1153_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_traceState_1154_);
lean_ctor_set(v_reuseFailAlloc_1168_, 5, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1168_, 6, v_recordedDeps_1155_);
lean_ctor_set(v_reuseFailAlloc_1168_, 7, v_messages_1156_);
lean_ctor_set(v_reuseFailAlloc_1168_, 8, v_infoState_1157_);
lean_ctor_set(v_reuseFailAlloc_1168_, 9, v_snapshotTasks_1158_);
v___x_1165_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_st_ref_put(v___y_1148_, v___x_1165_);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1162_);
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg___boxed(lean_object* v_env_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg(v_env_1172_, v___y_1173_);
lean_dec(v___y_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(lean_object* v_env_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg(v_env_1176_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(lean_object* v_env_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_env_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(size_t v_sz_1194_, size_t v_i_1195_, lean_object* v_bs_1196_, uint8_t v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_usize_dec_lt(v_i_1195_, v_sz_1194_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_bs_1196_);
return v___x_1205_;
}
else
{
uint8_t v___x_1206_; lean_object* v_v_1207_; lean_object* v___x_1208_; lean_object* v_bs_x27_1209_; lean_object* v___x_1210_; 
v___x_1206_ = 0;
v_v_1207_ = lean_array_uget(v_bs_1196_, v_i_1195_);
v___x_1208_ = lean_unsigned_to_nat(0u);
v_bs_x27_1209_ = lean_array_uset(v_bs_1196_, v_i_1195_, v___x_1208_);
v___x_1210_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_1206_, v_v_1207_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = ((size_t)1ULL);
v___x_1213_ = lean_usize_add(v_i_1195_, v___x_1212_);
v___x_1214_ = lean_array_uset(v_bs_x27_1209_, v_i_1195_, v_a_1211_);
v_i_1195_ = v___x_1213_;
v_bs_1196_ = v___x_1214_;
goto _start;
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_bs_x27_1209_);
v_a_1216_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1210_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1210_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(lean_object* v_sz_1224_, lean_object* v_i_1225_, lean_object* v_bs_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
size_t v_sz_boxed_1234_; size_t v_i_boxed_1235_; uint8_t v___y_8258__boxed_1236_; lean_object* v_res_1237_; 
v_sz_boxed_1234_ = lean_unbox_usize(v_sz_1224_);
lean_dec(v_sz_1224_);
v_i_boxed_1235_ = lean_unbox_usize(v_i_1225_);
lean_dec(v_i_1225_);
v___y_8258__boxed_1236_ = lean_unbox(v___y_1227_);
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_sz_boxed_1234_, v_i_boxed_1235_, v_bs_1226_, v___y_8258__boxed_1236_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
return v_res_1237_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_unsigned_to_nat(16u);
v___x_1242_ = lean_mk_array(v___x_1241_, v___x_1240_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1244_);
lean_ctor_set(v___x_1245_, 1, v___x_1243_);
return v___x_1245_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3(void){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(lean_object* v_decl_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_type_1263_; lean_object* v_value_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v_type_1263_ = lean_ctor_get(v_decl_1255_, 2);
lean_inc_ref(v_type_1263_);
v_value_1264_ = lean_ctor_get(v_decl_1255_, 3);
v___x_1265_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0));
v___x_1266_ = lean_st_mk_ref(v___x_1265_);
v___x_1267_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_1264_, v___x_1266_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; size_t v_sz_1277_; size_t v___x_1278_; lean_object* v___x_1279_; 
lean_dec_ref_known(v___x_1267_, 1);
v___x_1268_ = lean_st_ref_get(v___x_1266_);
lean_dec(v___x_1266_);
v___x_1269_ = l_Array_reverse___redArg(v___x_1268_);
v___x_1270_ = 0;
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v_decl_1255_);
v___x_1272_ = lean_array_push(v___x_1269_, v___x_1271_);
v___x_1273_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_1274_ = 0;
v___x_1275_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3);
v___x_1276_ = lean_st_mk_ref(v___x_1273_);
v_sz_1277_ = lean_array_size(v___x_1272_);
v___x_1278_ = ((size_t)0ULL);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_sz_1277_, v___x_1278_, v___x_1272_, v___x_1274_, v___x_1276_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v_env_1292_; lean_object* v___x_1293_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = lean_st_ref_get(v___x_1276_);
lean_dec(v___x_1276_);
lean_dec(v___x_1281_);
v___x_1282_ = lean_array_get_size(v_a_1280_);
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_nat_sub(v___x_1282_, v___x_1283_);
v___x_1285_ = lean_array_get_borrowed(v___x_1275_, v_a_1280_, v___x_1284_);
lean_dec(v___x_1284_);
v___x_1286_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1285_);
v___x_1287_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
v___x_1288_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_a_1280_, v___x_1287_);
lean_dec(v_a_1280_);
v___x_1289_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4));
lean_inc_ref(v___x_1288_);
v___x_1290_ = l_Lean_Compiler_LCNF_Code_toExpr(v___x_1270_, v___x_1288_, v___x_1289_);
v___x_1291_ = lean_st_ref_get(v_a_1261_);
v_env_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc_ref_n(v_env_1292_, 2);
lean_dec(v___x_1291_);
v___x_1293_ = l_Lean_getClosedTermName_x3f(v_env_1292_, v___x_1290_);
if (lean_obj_tag(v___x_1293_) == 1)
{
lean_object* v_val_1294_; lean_object* v___x_1295_; 
lean_dec_ref(v_env_1292_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_type_1263_);
v_val_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_val_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1270_, v___x_1288_, v_a_1259_);
lean_dec_ref(v___x_1288_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v___x_1295_, 0);
lean_dec(v_unused_1303_);
v___x_1297_ = v___x_1295_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_dec(v___x_1295_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v_val_1294_);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1294_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_val_1294_);
v_a_1304_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1295_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1295_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v___x_1312_; lean_object* v_baseName_1313_; lean_object* v_decls_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v___x_1293_);
v___x_1312_ = lean_st_ref_get(v_a_1257_);
v_baseName_1313_ = lean_ctor_get(v_a_1256_, 0);
v_decls_1314_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_decls_1314_);
lean_dec(v___x_1312_);
v___x_1315_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6));
v___x_1316_ = lean_array_get_size(v_decls_1314_);
lean_dec_ref(v_decls_1314_);
v___x_1317_ = lean_name_append_index_after(v___x_1315_, v___x_1316_);
lean_inc(v_baseName_1313_);
v___x_1318_ = l_Lean_Name_append(v_baseName_1313_, v___x_1317_);
lean_inc(v___x_1318_);
v___x_1319_ = l_Lean_cacheClosedTermName(v_env_1292_, v___x_1290_, v___x_1318_);
v___x_1320_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___redArg(v___x_1319_, v_a_1261_);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v___x_1320_, 0);
lean_dec(v_unused_1362_);
v___x_1322_ = v___x_1320_;
v_isShared_1323_ = v_isSharedCheck_1361_;
goto v_resetjp_1321_;
}
else
{
lean_dec(v___x_1320_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1361_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = 1;
lean_inc(v___x_1318_);
v___x_1326_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1326_, 0, v___x_1318_);
lean_ctor_set(v___x_1326_, 1, v___x_1324_);
lean_ctor_set(v___x_1326_, 2, v_type_1263_);
lean_ctor_set(v___x_1326_, 3, v___x_1289_);
lean_ctor_set_uint8(v___x_1326_, sizeof(void*)*4, v___x_1325_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1288_);
v___x_1328_ = v___x_1322_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1288_);
v___x_1328_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7));
v___x_1330_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1330_, 0, v___x_1326_);
lean_ctor_set(v___x_1330_, 1, v___x_1328_);
lean_ctor_set(v___x_1330_, 2, v___x_1329_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*3, v___x_1274_);
lean_inc_ref(v___x_1330_);
v___x_1331_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1330_, v_a_1261_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1350_; 
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v___x_1331_, 0);
lean_dec(v_unused_1351_);
v___x_1333_ = v___x_1331_;
v_isShared_1334_ = v_isSharedCheck_1350_;
goto v_resetjp_1332_;
}
else
{
lean_dec(v___x_1331_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1350_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v_decls_1336_; lean_object* v_fvarDecisionCache_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1349_; 
v___x_1335_ = lean_st_ref_take(v_a_1257_);
v_decls_1336_ = lean_ctor_get(v___x_1335_, 0);
v_fvarDecisionCache_1337_ = lean_ctor_get(v___x_1335_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1339_ = v___x_1335_;
v_isShared_1340_ = v_isSharedCheck_1349_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_fvarDecisionCache_1337_);
lean_inc(v_decls_1336_);
lean_dec(v___x_1335_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1349_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1341_ = lean_array_push(v_decls_1336_, v___x_1330_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1341_);
v___x_1343_ = v___x_1339_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_fvarDecisionCache_1337_);
v___x_1343_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1344_ = lean_st_ref_put(v_a_1257_, v___x_1343_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1318_);
v___x_1346_ = v___x_1333_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1318_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref_known(v___x_1330_, 3);
lean_dec(v___x_1318_);
v_a_1352_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1331_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1331_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v___x_1276_);
lean_dec_ref(v_type_1263_);
v_a_1363_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1279_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1279_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v___x_1266_);
lean_dec_ref(v_type_1263_);
lean_dec_ref(v_decl_1255_);
v_a_1371_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1267_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1267_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___boxed(lean_object* v_decl_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec_ref(v_a_1380_);
return v_res_1387_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(lean_object* v_msg_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0);
v___x_1391_ = lean_panic_fn_borrowed(v___x_1390_, v_msg_1389_);
return v___x_1391_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1395_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2));
v___x_1396_ = lean_unsigned_to_nat(9u);
v___x_1397_ = lean_unsigned_to_nat(650u);
v___x_1398_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1));
v___x_1399_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0));
v___x_1400_ = l_mkPanicMessageWithDecl(v___x_1399_, v___x_1398_, v___x_1397_, v___x_1396_, v___x_1395_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* v_code_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_decl_1412_; lean_object* v_k_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; 
switch(lean_obj_tag(v_code_1403_))
{
case 0:
{
lean_object* v_decl_1527_; lean_object* v_k_1528_; lean_object* v_value_1529_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; 
v_decl_1527_ = lean_ctor_get(v_code_1403_, 0);
v_k_1528_ = lean_ctor_get(v_code_1403_, 1);
v_value_1529_ = lean_ctor_get(v_decl_1527_, 3);
lean_inc(v_value_1529_);
if (lean_obj_tag(v_value_1529_) == 3)
{
lean_object* v_declName_1726_; 
v_declName_1726_ = lean_ctor_get(v_value_1529_, 0);
if (lean_obj_tag(v_declName_1726_) == 1)
{
lean_object* v_pre_1727_; 
v_pre_1727_ = lean_ctor_get(v_declName_1726_, 0);
if (lean_obj_tag(v_pre_1727_) == 1)
{
lean_object* v_pre_1728_; 
v_pre_1728_ = lean_ctor_get(v_pre_1727_, 0);
if (lean_obj_tag(v_pre_1728_) == 0)
{
lean_object* v_args_1729_; lean_object* v_str_1730_; lean_object* v_str_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v_sizeId_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; 
v_args_1729_ = lean_ctor_get(v_value_1529_, 2);
v_str_1730_ = lean_ctor_get(v_declName_1726_, 1);
v_str_1731_ = lean_ctor_get(v_pre_1727_, 1);
v___x_1732_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1733_ = lean_string_dec_eq(v_str_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
v___y_1531_ = v_a_1404_;
v___y_1532_ = v_a_1405_;
v___y_1533_ = v_a_1406_;
v___y_1534_ = v_a_1407_;
v___y_1535_ = v_a_1408_;
v___y_1536_ = v_a_1409_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_2072_ = lean_string_dec_eq(v_str_1730_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_2074_ = lean_string_dec_eq(v_str_1730_, v___x_2073_);
if (v___x_2074_ == 0)
{
v___y_1531_ = v_a_1404_;
v___y_1532_ = v_a_1405_;
v___y_1533_ = v_a_1406_;
v___y_1534_ = v_a_1407_;
v___y_1535_ = v_a_1408_;
v___y_1536_ = v_a_1409_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2075_ = lean_array_get_size(v_args_1729_);
v___x_2076_ = lean_unsigned_to_nat(2u);
v___x_2077_ = lean_nat_dec_eq(v___x_2075_, v___x_2076_);
if (v___x_2077_ == 0)
{
v___y_1531_ = v_a_1404_;
v___y_1532_ = v_a_1405_;
v___y_1533_ = v_a_1406_;
v___y_1534_ = v_a_1407_;
v___y_1535_ = v_a_1408_;
v___y_1536_ = v_a_1409_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_unsigned_to_nat(1u);
v___x_2079_ = lean_array_fget_borrowed(v_args_1729_, v___x_2078_);
if (lean_obj_tag(v___x_2079_) == 1)
{
lean_object* v_fvarId_2080_; 
v_fvarId_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_fvarId_2080_);
v_sizeId_1939_ = v_fvarId_2080_;
v___y_1940_ = v_a_1404_;
v___y_1941_ = v_a_1405_;
v___y_1942_ = v_a_1406_;
v___y_1943_ = v_a_1407_;
v___y_1944_ = v_a_1408_;
v___y_1945_ = v_a_1409_;
goto v___jp_1938_;
}
else
{
v___y_1531_ = v_a_1404_;
v___y_1532_ = v_a_1405_;
v___y_1533_ = v_a_1406_;
v___y_1534_ = v_a_1407_;
v___y_1535_ = v_a_1408_;
v___y_1536_ = v_a_1409_;
goto v___jp_1530_;
}
}
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2081_ = lean_array_get_size(v_args_1729_);
v___x_2082_ = lean_unsigned_to_nat(2u);
v___x_2083_ = lean_nat_dec_eq(v___x_2081_, v___x_2082_);
if (v___x_2083_ == 0)
{
v___y_1531_ = v_a_1404_;
v___y_1532_ = v_a_1405_;
v___y_1533_ = v_a_1406_;
v___y_1534_ = v_a_1407_;
v___y_1535_ = v_a_1408_;
v___y_1536_ = v_a_1409_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_array_fget_borrowed(v_args_1729_, v___x_2084_);
if (lean_obj_tag(v___x_2085_) == 1)
{
lean_object* v_fvarId_2086_; 
v_fvarId_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_fvarId_2086_);
v_sizeId_1939_ = v_fvarId_2086_;
v___y_1940_ = v_a_1404_;
v___y_1941_ = v_a_1405_;
v___y_1942_ = v_a_1406_;
v___y_1943_ = v_a_1407_;
v___y_1944_ = v_a_1408_;
v___y_1945_ = v_a_1409_;
goto v___jp_1938_;
}
else
{
v___y_1531_ = v_a_1404_;
v___y_1532_ = v_a_1405_;
v___y_1533_ = v_a_1406_;
v___y_1534_ = v_a_1407_;
v___y_1535_ = v_a_1408_;
v___y_1536_ = v_a_1409_;
goto v___jp_1530_;
}
}
}
}
v___jp_1734_:
{
lean_object* v___x_1741_; 
lean_inc_ref(v_k_1528_);
lean_inc_ref(v_decl_1527_);
v___x_1741_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1527_, v_k_1528_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
if (lean_obj_tag(v_a_1742_) == 1)
{
lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1814_; 
v_isSharedCheck_1814_ = !lean_is_exclusive(v_value_1529_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; lean_object* v_unused_1816_; lean_object* v_unused_1817_; 
v_unused_1815_ = lean_ctor_get(v_value_1529_, 2);
lean_dec(v_unused_1815_);
v_unused_1816_ = lean_ctor_get(v_value_1529_, 1);
lean_dec(v_unused_1816_);
v_unused_1817_ = lean_ctor_get(v_value_1529_, 0);
lean_dec(v_unused_1817_);
v___x_1744_ = v_value_1529_;
v_isShared_1745_ = v_isSharedCheck_1814_;
goto v_resetjp_1743_;
}
else
{
lean_dec(v_value_1529_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1814_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v_val_1746_; lean_object* v_fst_1747_; lean_object* v_snd_1748_; lean_object* v___x_1749_; 
v_val_1746_ = lean_ctor_get(v_a_1742_, 0);
lean_inc(v_val_1746_);
lean_dec_ref_known(v_a_1742_, 1);
v_fst_1747_ = lean_ctor_get(v_val_1746_, 0);
lean_inc_n(v_fst_1747_, 2);
v_snd_1748_ = lean_ctor_get(v_val_1746_, 1);
lean_inc(v_snd_1748_);
lean_dec(v_val_1746_);
v___x_1749_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1747_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = 0;
v___x_1752_ = lean_box(0);
v___x_1753_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 2, v___x_1753_);
lean_ctor_set(v___x_1744_, 1, v___x_1752_);
lean_ctor_set(v___x_1744_, 0, v_a_1750_);
v___x_1755_ = v___x_1744_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1750_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1751_, v_fst_1747_, v___x_1755_, v___y_1738_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1756_, 1);
v___x_1758_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1748_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1796_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1796_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1796_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
size_t v___x_1763_; size_t v___x_1764_; uint8_t v___x_1765_; 
v___x_1763_ = lean_ptr_addr(v_k_1528_);
v___x_1764_ = lean_ptr_addr(v_a_1759_);
v___x_1765_ = lean_usize_dec_eq(v___x_1763_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1775_; 
v_isSharedCheck_1775_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; lean_object* v_unused_1777_; 
v_unused_1776_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1777_);
v___x_1767_ = v_code_1403_;
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
else
{
lean_dec(v_code_1403_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v_a_1759_);
lean_ctor_set(v___x_1767_, 0, v_a_1757_);
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1757_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_a_1759_);
v___x_1770_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1770_);
v___x_1772_ = v___x_1761_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
size_t v___x_1778_; size_t v___x_1779_; uint8_t v___x_1780_; 
v___x_1778_ = lean_ptr_addr(v_decl_1527_);
v___x_1779_ = lean_ptr_addr(v_a_1757_);
v___x_1780_ = lean_usize_dec_eq(v___x_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1790_; 
v_isSharedCheck_1790_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; lean_object* v_unused_1792_; 
v_unused_1791_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1791_);
v_unused_1792_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1792_);
v___x_1782_ = v_code_1403_;
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
else
{
lean_dec(v_code_1403_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 1, v_a_1759_);
lean_ctor_set(v___x_1782_, 0, v_a_1757_);
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1757_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_a_1759_);
v___x_1785_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1787_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1785_);
v___x_1787_ = v___x_1761_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
lean_object* v___x_1794_; 
lean_dec(v_a_1759_);
lean_dec(v_a_1757_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v_code_1403_);
v___x_1794_ = v___x_1761_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_code_1403_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
else
{
lean_dec(v_a_1757_);
lean_dec_ref_known(v_code_1403_, 2);
return v___x_1758_;
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_snd_1748_);
lean_dec_ref_known(v_code_1403_, 2);
v_a_1797_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1756_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1756_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_snd_1748_);
lean_dec(v_fst_1747_);
lean_del_object(v___x_1744_);
lean_dec_ref_known(v_code_1403_, 2);
v_a_1806_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1749_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1749_);
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
}
else
{
lean_object* v___x_1818_; 
lean_dec(v_a_1742_);
v___x_1818_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1733_, v_value_1529_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; uint8_t v___x_1820_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v___x_1820_ = lean_unbox(v_a_1819_);
lean_dec(v_a_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; 
lean_inc_ref(v_k_1528_);
v___x_1821_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1858_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1858_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1858_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
size_t v___x_1826_; size_t v___x_1827_; uint8_t v___x_1828_; 
v___x_1826_ = lean_ptr_addr(v_k_1528_);
v___x_1827_ = lean_ptr_addr(v_a_1822_);
v___x_1828_ = lean_usize_dec_eq(v___x_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1838_; 
lean_inc_ref(v_decl_1527_);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; lean_object* v_unused_1840_; 
v_unused_1839_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1840_);
v___x_1830_ = v_code_1403_;
v_isShared_1831_ = v_isSharedCheck_1838_;
goto v_resetjp_1829_;
}
else
{
lean_dec(v_code_1403_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1838_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v_a_1822_);
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_decl_1527_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_a_1822_);
v___x_1833_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1833_);
v___x_1835_ = v___x_1824_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
size_t v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = lean_ptr_addr(v_decl_1527_);
v___x_1842_ = lean_usize_dec_eq(v___x_1841_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1852_; 
lean_inc_ref(v_decl_1527_);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; lean_object* v_unused_1854_; 
v_unused_1853_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1854_);
v___x_1844_ = v_code_1403_;
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
else
{
lean_dec(v_code_1403_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1852_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 1, v_a_1822_);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_decl_1527_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_a_1822_);
v___x_1847_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1847_);
v___x_1849_ = v___x_1824_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v___x_1856_; 
lean_dec(v_a_1822_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v_code_1403_);
v___x_1856_ = v___x_1824_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_code_1403_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1403_, 2);
return v___x_1821_;
}
}
else
{
lean_object* v___x_1859_; 
lean_inc_ref(v_decl_1527_);
v___x_1859_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1527_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; uint8_t v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1859_, 1);
v___x_1861_ = 0;
v___x_1862_ = lean_box(0);
v___x_1863_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1864_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1864_, 0, v_a_1860_);
lean_ctor_set(v___x_1864_, 1, v___x_1862_);
lean_ctor_set(v___x_1864_, 2, v___x_1863_);
lean_inc_ref(v_decl_1527_);
v___x_1865_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1861_, v_decl_1527_, v___x_1864_, v___y_1738_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
lean_inc_ref(v_k_1528_);
v___x_1867_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1905_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1905_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1905_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
size_t v___x_1872_; size_t v___x_1873_; uint8_t v___x_1874_; 
v___x_1872_ = lean_ptr_addr(v_k_1528_);
v___x_1873_ = lean_ptr_addr(v_a_1868_);
v___x_1874_ = lean_usize_dec_eq(v___x_1872_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1884_; 
v_isSharedCheck_1884_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; lean_object* v_unused_1886_; 
v_unused_1885_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1885_);
v_unused_1886_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1886_);
v___x_1876_ = v_code_1403_;
v_isShared_1877_ = v_isSharedCheck_1884_;
goto v_resetjp_1875_;
}
else
{
lean_dec(v_code_1403_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1884_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v_a_1868_);
lean_ctor_set(v___x_1876_, 0, v_a_1866_);
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1866_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_a_1868_);
v___x_1879_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1879_);
v___x_1881_ = v___x_1870_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
size_t v___x_1887_; size_t v___x_1888_; uint8_t v___x_1889_; 
v___x_1887_ = lean_ptr_addr(v_decl_1527_);
v___x_1888_ = lean_ptr_addr(v_a_1866_);
v___x_1889_ = lean_usize_dec_eq(v___x_1887_, v___x_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1899_; 
v_isSharedCheck_1899_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; lean_object* v_unused_1901_; 
v_unused_1900_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1900_);
v_unused_1901_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1901_);
v___x_1891_ = v_code_1403_;
v_isShared_1892_ = v_isSharedCheck_1899_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v_code_1403_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1899_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v_a_1868_);
lean_ctor_set(v___x_1891_, 0, v_a_1866_);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1866_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_a_1868_);
v___x_1894_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1896_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1894_);
v___x_1896_ = v___x_1870_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v___x_1903_; 
lean_dec(v_a_1868_);
lean_dec(v_a_1866_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v_code_1403_);
v___x_1903_ = v___x_1870_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_code_1403_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
else
{
lean_dec(v_a_1866_);
lean_dec_ref_known(v_code_1403_, 2);
return v___x_1867_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec_ref_known(v_code_1403_, 2);
v_a_1906_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1865_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1865_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref_known(v_code_1403_, 2);
v_a_1914_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1859_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1859_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref_known(v_code_1403_, 2);
v_a_1922_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1818_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1818_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref_known(v_value_1529_, 3);
lean_dec_ref_known(v_code_1403_, 2);
v_a_1930_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1741_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1741_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
v___jp_1938_:
{
uint8_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = 0;
v___x_1947_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1946_, v_sizeId_1939_, v___y_1943_);
lean_dec(v_sizeId_1939_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
if (lean_obj_tag(v_a_1948_) == 1)
{
lean_object* v_val_1949_; 
v_val_1949_ = lean_ctor_get(v_a_1948_, 0);
lean_inc(v_val_1949_);
lean_dec_ref_known(v_a_1948_, 1);
if (lean_obj_tag(v_val_1949_) == 0)
{
lean_object* v_value_1950_; 
v_value_1950_ = lean_ctor_get(v_val_1949_, 0);
lean_inc_ref(v_value_1950_);
lean_dec_ref_known(v_val_1949_, 1);
if (lean_obj_tag(v_value_1950_) == 0)
{
lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_2059_; 
v_isSharedCheck_2059_ = !lean_is_exclusive(v_value_1529_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; lean_object* v_unused_2061_; lean_object* v_unused_2062_; 
v_unused_2060_ = lean_ctor_get(v_value_1529_, 2);
lean_dec(v_unused_2060_);
v_unused_2061_ = lean_ctor_get(v_value_1529_, 1);
lean_dec(v_unused_2061_);
v_unused_2062_ = lean_ctor_get(v_value_1529_, 0);
lean_dec(v_unused_2062_);
v___x_1952_ = v_value_1529_;
v_isShared_1953_ = v_isSharedCheck_2059_;
goto v_resetjp_1951_;
}
else
{
lean_dec(v_value_1529_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_2059_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v_val_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v_val_1954_ = lean_ctor_get(v_value_1950_, 0);
lean_inc(v_val_1954_);
lean_dec_ref_known(v_value_1950_, 1);
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = lean_nat_dec_eq(v_val_1954_, v___x_1955_);
lean_dec(v_val_1954_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; 
lean_del_object(v___x_1952_);
lean_inc_ref(v_k_1528_);
v___x_1957_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1994_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1994_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1994_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
size_t v___x_1962_; size_t v___x_1963_; uint8_t v___x_1964_; 
v___x_1962_ = lean_ptr_addr(v_k_1528_);
v___x_1963_ = lean_ptr_addr(v_a_1958_);
v___x_1964_ = lean_usize_dec_eq(v___x_1962_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1974_; 
lean_inc_ref(v_decl_1527_);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; lean_object* v_unused_1976_; 
v_unused_1975_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1976_);
v___x_1966_ = v_code_1403_;
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v_code_1403_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1974_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v_a_1958_);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_decl_1527_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_a_1958_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1969_);
v___x_1971_ = v___x_1960_;
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
}
else
{
size_t v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = lean_ptr_addr(v_decl_1527_);
v___x_1978_ = lean_usize_dec_eq(v___x_1977_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1988_; 
lean_inc_ref(v_decl_1527_);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; lean_object* v_unused_1990_; 
v_unused_1989_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1989_);
v_unused_1990_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1990_);
v___x_1980_ = v_code_1403_;
v_isShared_1981_ = v_isSharedCheck_1988_;
goto v_resetjp_1979_;
}
else
{
lean_dec(v_code_1403_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1988_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v_a_1958_);
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_decl_1527_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_a_1958_);
v___x_1983_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1985_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1983_);
v___x_1985_ = v___x_1960_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v___x_1992_; 
lean_dec(v_a_1958_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v_code_1403_);
v___x_1992_ = v___x_1960_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_code_1403_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1403_, 2);
return v___x_1957_;
}
}
else
{
lean_object* v___x_1995_; 
lean_inc_ref(v_decl_1527_);
v___x_1995_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1527_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = lean_box(0);
v___x_1998_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 2, v___x_1998_);
lean_ctor_set(v___x_1952_, 1, v___x_1997_);
lean_ctor_set(v___x_1952_, 0, v_a_1996_);
v___x_2000_ = v___x_1952_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_1996_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2050_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2001_; 
lean_inc_ref(v_decl_1527_);
v___x_2001_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1946_, v_decl_1527_, v___x_2000_, v___y_1943_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2003_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
lean_inc_ref(v_k_1528_);
v___x_2003_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2041_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2041_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2041_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
size_t v___x_2008_; size_t v___x_2009_; uint8_t v___x_2010_; 
v___x_2008_ = lean_ptr_addr(v_k_1528_);
v___x_2009_ = lean_ptr_addr(v_a_2004_);
v___x_2010_ = lean_usize_dec_eq(v___x_2008_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2020_; 
v_isSharedCheck_2020_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; lean_object* v_unused_2022_; 
v_unused_2021_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_2022_);
v___x_2012_ = v_code_1403_;
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
else
{
lean_dec(v_code_1403_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v_a_2004_);
lean_ctor_set(v___x_2012_, 0, v_a_2002_);
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2002_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_a_2004_);
v___x_2015_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2017_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2015_);
v___x_2017_ = v___x_2006_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
size_t v___x_2023_; size_t v___x_2024_; uint8_t v___x_2025_; 
v___x_2023_ = lean_ptr_addr(v_decl_1527_);
v___x_2024_ = lean_ptr_addr(v_a_2002_);
v___x_2025_ = lean_usize_dec_eq(v___x_2023_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2035_; 
v_isSharedCheck_2035_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; lean_object* v_unused_2037_; 
v_unused_2036_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_2037_);
v___x_2027_ = v_code_1403_;
v_isShared_2028_ = v_isSharedCheck_2035_;
goto v_resetjp_2026_;
}
else
{
lean_dec(v_code_1403_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2035_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v_a_2004_);
lean_ctor_set(v___x_2027_, 0, v_a_2002_);
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2002_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_a_2004_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2030_);
v___x_2032_ = v___x_2006_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v___x_2039_; 
lean_dec(v_a_2004_);
lean_dec(v_a_2002_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v_code_1403_);
v___x_2039_ = v___x_2006_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_code_1403_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
else
{
lean_dec(v_a_2002_);
lean_dec_ref_known(v_code_1403_, 2);
return v___x_2003_;
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref_known(v_code_1403_, 2);
v_a_2042_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2001_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2001_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_del_object(v___x_1952_);
lean_dec_ref_known(v_code_1403_, 2);
v_a_2051_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_1995_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_1995_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_1950_);
v___y_1735_ = v___y_1940_;
v___y_1736_ = v___y_1941_;
v___y_1737_ = v___y_1942_;
v___y_1738_ = v___y_1943_;
v___y_1739_ = v___y_1944_;
v___y_1740_ = v___y_1945_;
goto v___jp_1734_;
}
}
else
{
lean_dec(v_val_1949_);
v___y_1735_ = v___y_1940_;
v___y_1736_ = v___y_1941_;
v___y_1737_ = v___y_1942_;
v___y_1738_ = v___y_1943_;
v___y_1739_ = v___y_1944_;
v___y_1740_ = v___y_1945_;
goto v___jp_1734_;
}
}
else
{
lean_dec(v_a_1948_);
v___y_1735_ = v___y_1940_;
v___y_1736_ = v___y_1941_;
v___y_1737_ = v___y_1942_;
v___y_1738_ = v___y_1943_;
v___y_1739_ = v___y_1944_;
v___y_1740_ = v___y_1945_;
goto v___jp_1734_;
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref_known(v_value_1529_, 3);
lean_dec_ref_known(v_code_1403_, 2);
v_a_2063_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_1947_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_1947_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
else
{
v___y_1531_ = v_a_1404_;
v___y_1532_ = v_a_1405_;
v___y_1533_ = v_a_1406_;
v___y_1534_ = v_a_1407_;
v___y_1535_ = v_a_1408_;
v___y_1536_ = v_a_1409_;
goto v___jp_1530_;
}
}
else
{
v___y_1531_ = v_a_1404_;
v___y_1532_ = v_a_1405_;
v___y_1533_ = v_a_1406_;
v___y_1534_ = v_a_1407_;
v___y_1535_ = v_a_1408_;
v___y_1536_ = v_a_1409_;
goto v___jp_1530_;
}
}
else
{
v___y_1531_ = v_a_1404_;
v___y_1532_ = v_a_1405_;
v___y_1533_ = v_a_1406_;
v___y_1534_ = v_a_1407_;
v___y_1535_ = v_a_1408_;
v___y_1536_ = v_a_1409_;
goto v___jp_1530_;
}
}
else
{
v___y_1531_ = v_a_1404_;
v___y_1532_ = v_a_1405_;
v___y_1533_ = v_a_1406_;
v___y_1534_ = v_a_1407_;
v___y_1535_ = v_a_1408_;
v___y_1536_ = v_a_1409_;
goto v___jp_1530_;
}
v___jp_1530_:
{
lean_object* v___x_1537_; 
lean_inc_ref(v_k_1528_);
lean_inc_ref(v_decl_1527_);
v___x_1537_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1527_, v_k_1528_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
if (lean_obj_tag(v_a_1538_) == 1)
{
lean_object* v_val_1539_; lean_object* v_fst_1540_; lean_object* v_snd_1541_; lean_object* v___x_1542_; 
lean_dec(v_value_1529_);
v_val_1539_ = lean_ctor_get(v_a_1538_, 0);
lean_inc(v_val_1539_);
lean_dec_ref_known(v_a_1538_, 1);
v_fst_1540_ = lean_ctor_get(v_val_1539_, 0);
lean_inc_n(v_fst_1540_, 2);
v_snd_1541_ = lean_ctor_get(v_val_1539_, 1);
lean_inc(v_snd_1541_);
lean_dec(v_val_1539_);
v___x_1542_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1540_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = 0;
v___x_1545_ = lean_box(0);
v___x_1546_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1547_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1547_, 0, v_a_1543_);
lean_ctor_set(v___x_1547_, 1, v___x_1545_);
lean_ctor_set(v___x_1547_, 2, v___x_1546_);
v___x_1548_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1544_, v_fst_1540_, v___x_1547_, v___y_1534_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1541_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1588_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1588_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1588_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
size_t v___x_1555_; size_t v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = lean_ptr_addr(v_k_1528_);
v___x_1556_ = lean_ptr_addr(v_a_1551_);
v___x_1557_ = lean_usize_dec_eq(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1567_; 
v_isSharedCheck_1567_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; lean_object* v_unused_1569_; 
v_unused_1568_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1569_);
v___x_1559_ = v_code_1403_;
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
else
{
lean_dec(v_code_1403_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1567_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v_a_1551_);
lean_ctor_set(v___x_1559_, 0, v_a_1549_);
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1549_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_a_1551_);
v___x_1562_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1564_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1562_);
v___x_1564_ = v___x_1553_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
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
else
{
size_t v___x_1570_; size_t v___x_1571_; uint8_t v___x_1572_; 
v___x_1570_ = lean_ptr_addr(v_decl_1527_);
v___x_1571_ = lean_ptr_addr(v_a_1549_);
v___x_1572_ = lean_usize_dec_eq(v___x_1570_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1582_; 
v_isSharedCheck_1582_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; lean_object* v_unused_1584_; 
v_unused_1583_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1584_);
v___x_1574_ = v_code_1403_;
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
else
{
lean_dec(v_code_1403_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 1, v_a_1551_);
lean_ctor_set(v___x_1574_, 0, v_a_1549_);
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1549_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_a_1551_);
v___x_1577_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
lean_object* v___x_1579_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1577_);
v___x_1579_ = v___x_1553_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v___x_1586_; 
lean_dec(v_a_1551_);
lean_dec(v_a_1549_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v_code_1403_);
v___x_1586_ = v___x_1553_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_code_1403_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
else
{
lean_dec(v_a_1549_);
lean_dec_ref_known(v_code_1403_, 2);
return v___x_1550_;
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v_snd_1541_);
lean_dec_ref_known(v_code_1403_, 2);
v_a_1589_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1548_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1548_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec_ref_known(v_code_1403_, 2);
v_a_1597_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1542_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1542_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
else
{
uint8_t v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v_a_1538_);
v___x_1605_ = 1;
v___x_1606_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1605_, v_value_1529_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; uint8_t v___x_1608_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1608_ = lean_unbox(v_a_1607_);
lean_dec(v_a_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_inc_ref(v_k_1528_);
v___x_1609_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1646_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1646_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1646_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
size_t v___x_1614_; size_t v___x_1615_; uint8_t v___x_1616_; 
v___x_1614_ = lean_ptr_addr(v_k_1528_);
v___x_1615_ = lean_ptr_addr(v_a_1610_);
v___x_1616_ = lean_usize_dec_eq(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1626_; 
lean_inc_ref(v_decl_1527_);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; lean_object* v_unused_1628_; 
v_unused_1627_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1627_);
v_unused_1628_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1628_);
v___x_1618_ = v_code_1403_;
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v_code_1403_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v_a_1610_);
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_decl_1527_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_a_1610_);
v___x_1621_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1621_);
v___x_1623_ = v___x_1612_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
size_t v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = lean_ptr_addr(v_decl_1527_);
v___x_1630_ = lean_usize_dec_eq(v___x_1629_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1640_; 
lean_inc_ref(v_decl_1527_);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; 
v_unused_1641_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1642_);
v___x_1632_ = v_code_1403_;
v_isShared_1633_ = v_isSharedCheck_1640_;
goto v_resetjp_1631_;
}
else
{
lean_dec(v_code_1403_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1640_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 1, v_a_1610_);
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_decl_1527_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_a_1610_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1635_);
v___x_1637_ = v___x_1612_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v___x_1644_; 
lean_dec(v_a_1610_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v_code_1403_);
v___x_1644_ = v___x_1612_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_code_1403_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1403_, 2);
return v___x_1609_;
}
}
else
{
lean_object* v___x_1647_; 
lean_inc_ref(v_decl_1527_);
v___x_1647_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1527_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = 0;
v___x_1650_ = lean_box(0);
v___x_1651_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1652_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1652_, 0, v_a_1648_);
lean_ctor_set(v___x_1652_, 1, v___x_1650_);
lean_ctor_set(v___x_1652_, 2, v___x_1651_);
lean_inc_ref(v_decl_1527_);
v___x_1653_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1649_, v_decl_1527_, v___x_1652_, v___y_1534_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
lean_inc_ref(v_k_1528_);
v___x_1655_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1693_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1693_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1693_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
size_t v___x_1660_; size_t v___x_1661_; uint8_t v___x_1662_; 
v___x_1660_ = lean_ptr_addr(v_k_1528_);
v___x_1661_ = lean_ptr_addr(v_a_1656_);
v___x_1662_ = lean_usize_dec_eq(v___x_1660_, v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1672_; 
v_isSharedCheck_1672_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; lean_object* v_unused_1674_; 
v_unused_1673_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1674_);
v___x_1664_ = v_code_1403_;
v_isShared_1665_ = v_isSharedCheck_1672_;
goto v_resetjp_1663_;
}
else
{
lean_dec(v_code_1403_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1672_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v_a_1656_);
lean_ctor_set(v___x_1664_, 0, v_a_1654_);
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1654_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_a_1656_);
v___x_1667_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1669_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1667_);
v___x_1669_ = v___x_1658_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
size_t v___x_1675_; size_t v___x_1676_; uint8_t v___x_1677_; 
v___x_1675_ = lean_ptr_addr(v_decl_1527_);
v___x_1676_ = lean_ptr_addr(v_a_1654_);
v___x_1677_ = lean_usize_dec_eq(v___x_1675_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1687_; 
v_isSharedCheck_1687_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; lean_object* v_unused_1689_; 
v_unused_1688_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1689_);
v___x_1679_ = v_code_1403_;
v_isShared_1680_ = v_isSharedCheck_1687_;
goto v_resetjp_1678_;
}
else
{
lean_dec(v_code_1403_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1687_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v_a_1656_);
lean_ctor_set(v___x_1679_, 0, v_a_1654_);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1654_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_a_1656_);
v___x_1682_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1684_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1682_);
v___x_1684_ = v___x_1658_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v___x_1691_; 
lean_dec(v_a_1656_);
lean_dec(v_a_1654_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v_code_1403_);
v___x_1691_ = v___x_1658_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_code_1403_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
else
{
lean_dec(v_a_1654_);
lean_dec_ref_known(v_code_1403_, 2);
return v___x_1655_;
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref_known(v_code_1403_, 2);
v_a_1694_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1653_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1653_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref_known(v_code_1403_, 2);
v_a_1702_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1647_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1647_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec_ref_known(v_code_1403_, 2);
v_a_1710_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1606_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1606_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_value_1529_);
lean_dec_ref_known(v_code_1403_, 2);
v_a_1718_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1537_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1537_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2087_; lean_object* v_k_2088_; 
v_decl_2087_ = lean_ctor_get(v_code_1403_, 0);
v_k_2088_ = lean_ctor_get(v_code_1403_, 1);
lean_inc_ref(v_k_2088_);
lean_inc_ref(v_decl_2087_);
v_decl_1412_ = v_decl_2087_;
v_k_1413_ = v_k_2088_;
v___y_1414_ = v_a_1404_;
v___y_1415_ = v_a_1405_;
v___y_1416_ = v_a_1406_;
v___y_1417_ = v_a_1407_;
v___y_1418_ = v_a_1408_;
v___y_1419_ = v_a_1409_;
goto v___jp_1411_;
}
case 2:
{
lean_object* v_decl_2089_; lean_object* v_k_2090_; 
v_decl_2089_ = lean_ctor_get(v_code_1403_, 0);
v_k_2090_ = lean_ctor_get(v_code_1403_, 1);
lean_inc_ref(v_k_2090_);
lean_inc_ref(v_decl_2089_);
v_decl_1412_ = v_decl_2089_;
v_k_1413_ = v_k_2090_;
v___y_1414_ = v_a_1404_;
v___y_1415_ = v_a_1405_;
v___y_1416_ = v_a_1406_;
v___y_1417_ = v_a_1407_;
v___y_1418_ = v_a_1408_;
v___y_1419_ = v_a_1409_;
goto v___jp_1411_;
}
case 4:
{
lean_object* v_cases_2091_; lean_object* v_typeName_2092_; lean_object* v_resultType_2093_; lean_object* v_discr_2094_; lean_object* v_alts_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2134_; 
v_cases_2091_ = lean_ctor_get(v_code_1403_, 0);
lean_inc_ref(v_cases_2091_);
v_typeName_2092_ = lean_ctor_get(v_cases_2091_, 0);
v_resultType_2093_ = lean_ctor_get(v_cases_2091_, 1);
v_discr_2094_ = lean_ctor_get(v_cases_2091_, 2);
v_alts_2095_ = lean_ctor_get(v_cases_2091_, 3);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_cases_2091_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2097_ = v_cases_2091_;
v_isShared_2098_ = v_isSharedCheck_2134_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_alts_2095_);
lean_inc(v_discr_2094_);
lean_inc(v_resultType_2093_);
lean_inc(v_typeName_2092_);
lean_dec(v_cases_2091_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2134_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2095_);
v___x_2100_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v___x_2099_, v_alts_2095_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2125_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2125_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2125_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
size_t v___x_2105_; size_t v___x_2106_; uint8_t v___x_2107_; 
v___x_2105_ = lean_ptr_addr(v_alts_2095_);
lean_dec_ref(v_alts_2095_);
v___x_2106_ = lean_ptr_addr(v_a_2101_);
v___x_2107_ = lean_usize_dec_eq(v___x_2105_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2120_; 
v_isSharedCheck_2120_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_2121_);
v___x_2109_ = v_code_1403_;
v_isShared_2110_ = v_isSharedCheck_2120_;
goto v_resetjp_2108_;
}
else
{
lean_dec(v_code_1403_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2120_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 3, v_a_2101_);
v___x_2112_ = v___x_2097_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_typeName_2092_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_resultType_2093_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_discr_2094_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v_a_2101_);
v___x_2112_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2112_);
v___x_2114_ = v___x_2109_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2116_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2114_);
v___x_2116_ = v___x_2103_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
else
{
lean_object* v___x_2123_; 
lean_dec(v_a_2101_);
lean_del_object(v___x_2097_);
lean_dec(v_discr_2094_);
lean_dec_ref(v_resultType_2093_);
lean_dec(v_typeName_2092_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v_code_1403_);
v___x_2123_ = v___x_2103_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_code_1403_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_del_object(v___x_2097_);
lean_dec_ref(v_alts_2095_);
lean_dec(v_discr_2094_);
lean_dec_ref(v_resultType_2093_);
lean_dec(v_typeName_2092_);
lean_dec_ref_known(v_code_1403_, 1);
v_a_2126_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2100_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2100_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
default: 
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_code_1403_);
return v___x_2135_;
}
}
v___jp_1411_:
{
lean_object* v_params_1420_; lean_object* v_type_1421_; lean_object* v_value_1422_; uint8_t v___x_1423_; lean_object* v___x_1424_; 
v_params_1420_ = lean_ctor_get(v_decl_1412_, 2);
lean_inc_ref(v_params_1420_);
v_type_1421_ = lean_ctor_get(v_decl_1412_, 3);
lean_inc_ref(v_type_1421_);
v_value_1422_ = lean_ctor_get(v_decl_1412_, 4);
v___x_1423_ = 0;
lean_inc_ref(v_value_1422_);
v___x_1424_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_value_1422_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1423_, v_decl_1412_, v_type_1421_, v_params_1420_, v_a_1425_, v___y_1417_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
v___x_1428_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1428_) == 0)
{
switch(lean_obj_tag(v_code_1403_))
{
case 1:
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1468_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1468_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1468_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_decl_1433_; lean_object* v_k_1434_; size_t v___x_1435_; size_t v___x_1436_; uint8_t v___x_1437_; 
v_decl_1433_ = lean_ctor_get(v_code_1403_, 0);
v_k_1434_ = lean_ctor_get(v_code_1403_, 1);
v___x_1435_ = lean_ptr_addr(v_k_1434_);
v___x_1436_ = lean_ptr_addr(v_a_1429_);
v___x_1437_ = lean_usize_dec_eq(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1447_; 
v_isSharedCheck_1447_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1448_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1449_);
v___x_1439_ = v_code_1403_;
v_isShared_1440_ = v_isSharedCheck_1447_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v_code_1403_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1447_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v_a_1429_);
lean_ctor_set(v___x_1439_, 0, v_a_1427_);
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1427_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_a_1429_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1442_);
v___x_1444_ = v___x_1431_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
size_t v___x_1450_; size_t v___x_1451_; uint8_t v___x_1452_; 
v___x_1450_ = lean_ptr_addr(v_decl_1433_);
v___x_1451_ = lean_ptr_addr(v_a_1427_);
v___x_1452_ = lean_usize_dec_eq(v___x_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1462_; 
v_isSharedCheck_1462_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; lean_object* v_unused_1464_; 
v_unused_1463_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1464_);
v___x_1454_ = v_code_1403_;
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v_code_1403_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v_a_1429_);
lean_ctor_set(v___x_1454_, 0, v_a_1427_);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1427_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_a_1429_);
v___x_1457_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1459_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1457_);
v___x_1459_ = v___x_1431_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_object* v___x_1466_; 
lean_dec(v_a_1429_);
lean_dec(v_a_1427_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v_code_1403_);
v___x_1466_ = v___x_1431_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_code_1403_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
case 2:
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1508_; 
v_a_1469_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1471_ = v___x_1428_;
v_isShared_1472_ = v_isSharedCheck_1508_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1428_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1508_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v_decl_1473_; lean_object* v_k_1474_; size_t v___x_1475_; size_t v___x_1476_; uint8_t v___x_1477_; 
v_decl_1473_ = lean_ctor_get(v_code_1403_, 0);
v_k_1474_ = lean_ctor_get(v_code_1403_, 1);
v___x_1475_ = lean_ptr_addr(v_k_1474_);
v___x_1476_ = lean_ptr_addr(v_a_1469_);
v___x_1477_ = lean_usize_dec_eq(v___x_1475_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1487_; 
v_isSharedCheck_1487_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; lean_object* v_unused_1489_; 
v_unused_1488_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1489_);
v___x_1479_ = v_code_1403_;
v_isShared_1480_ = v_isSharedCheck_1487_;
goto v_resetjp_1478_;
}
else
{
lean_dec(v_code_1403_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1487_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 1, v_a_1469_);
lean_ctor_set(v___x_1479_, 0, v_a_1427_);
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1427_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_a_1469_);
v___x_1482_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1482_);
v___x_1484_ = v___x_1471_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
size_t v___x_1490_; size_t v___x_1491_; uint8_t v___x_1492_; 
v___x_1490_ = lean_ptr_addr(v_decl_1473_);
v___x_1491_ = lean_ptr_addr(v_a_1427_);
v___x_1492_ = lean_usize_dec_eq(v___x_1490_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1502_; 
v_isSharedCheck_1502_ = !lean_is_exclusive(v_code_1403_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; 
v_unused_1503_ = lean_ctor_get(v_code_1403_, 1);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_code_1403_, 0);
lean_dec(v_unused_1504_);
v___x_1494_ = v_code_1403_;
v_isShared_1495_ = v_isSharedCheck_1502_;
goto v_resetjp_1493_;
}
else
{
lean_dec(v_code_1403_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1502_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v_a_1469_);
lean_ctor_set(v___x_1494_, 0, v_a_1427_);
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1427_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_a_1469_);
v___x_1497_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1497_);
v___x_1499_ = v___x_1471_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_a_1469_);
lean_dec(v_a_1427_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v_code_1403_);
v___x_1506_ = v___x_1471_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_code_1403_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
}
default: 
{
lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1517_; 
lean_dec(v_a_1427_);
lean_dec_ref(v_code_1403_);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v___x_1428_, 0);
lean_dec(v_unused_1518_);
v___x_1510_ = v___x_1428_;
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
else
{
lean_dec(v___x_1428_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1512_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3, &l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3);
v___x_1513_ = l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(v___x_1512_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1513_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
else
{
lean_dec(v_a_1427_);
lean_dec_ref(v_code_1403_);
return v___x_1428_;
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v_k_1413_);
lean_dec_ref(v_code_1403_);
v_a_1519_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1426_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1426_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_dec_ref(v_type_1421_);
lean_dec_ref(v_params_1420_);
lean_dec_ref(v_k_1413_);
lean_dec_ref(v_decl_1412_);
lean_dec_ref(v_code_1403_);
return v___x_1424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object* v_i_2136_, lean_object* v_as_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2145_ = lean_array_get_size(v_as_2137_);
v___x_2146_ = lean_nat_dec_lt(v_i_2136_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_dec(v_i_2136_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v_as_2137_);
return v___x_2147_;
}
else
{
lean_object* v_a_2148_; lean_object* v___y_2150_; 
v_a_2148_ = lean_array_fget_borrowed(v_as_2137_, v_i_2136_);
switch(lean_obj_tag(v_a_2148_))
{
case 0:
{
lean_object* v_code_2172_; 
v_code_2172_ = lean_ctor_get(v_a_2148_, 2);
lean_inc_ref(v_code_2172_);
v___y_2150_ = v_code_2172_;
goto v___jp_2149_;
}
case 1:
{
lean_object* v_code_2173_; 
v_code_2173_ = lean_ctor_get(v_a_2148_, 1);
lean_inc_ref(v_code_2173_);
v___y_2150_ = v_code_2173_;
goto v___jp_2149_;
}
default: 
{
lean_object* v_code_2174_; 
v_code_2174_ = lean_ctor_get(v_a_2148_, 0);
lean_inc_ref(v_code_2174_);
v___y_2150_ = v_code_2174_;
goto v___jp_2149_;
}
}
v___jp_2149_:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v___y_2150_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2153_; size_t v___x_2154_; size_t v___x_2155_; uint8_t v___x_2156_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
lean_inc(v_a_2148_);
v___x_2153_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2148_, v_a_2152_);
v___x_2154_ = lean_ptr_addr(v_a_2148_);
v___x_2155_ = lean_ptr_addr(v___x_2153_);
v___x_2156_ = lean_usize_dec_eq(v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_unsigned_to_nat(1u);
v___x_2158_ = lean_nat_add(v_i_2136_, v___x_2157_);
v___x_2159_ = lean_array_fset(v_as_2137_, v_i_2136_, v___x_2153_);
lean_dec(v_i_2136_);
v_i_2136_ = v___x_2158_;
v_as_2137_ = v___x_2159_;
goto _start;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref(v___x_2153_);
v___x_2161_ = lean_unsigned_to_nat(1u);
v___x_2162_ = lean_nat_add(v_i_2136_, v___x_2161_);
lean_dec(v_i_2136_);
v_i_2136_ = v___x_2162_;
goto _start;
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v_as_2137_);
lean_dec(v_i_2136_);
v_a_2164_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2151_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2151_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object* v_i_2175_, lean_object* v_as_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_2175_, v_as_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object* v_code_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_code_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(lean_object* v_f_2194_, lean_object* v_v_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
if (lean_obj_tag(v_v_2195_) == 0)
{
lean_object* v_code_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2227_; 
v_code_2203_ = lean_ctor_get(v_v_2195_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_v_2195_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2205_ = v_v_2195_;
v_isShared_2206_ = v_isSharedCheck_2227_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_code_2203_);
lean_dec(v_v_2195_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2227_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; 
lean_inc(v___y_2201_);
lean_inc_ref(v___y_2200_);
lean_inc(v___y_2199_);
lean_inc_ref(v___y_2198_);
lean_inc(v___y_2197_);
lean_inc_ref(v___y_2196_);
v___x_2207_ = lean_apply_8(v_f_2194_, v_code_2203_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, lean_box(0));
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2218_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2218_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2218_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v_a_2208_);
v___x_2213_ = v___x_2205_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2215_; 
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2213_);
v___x_2215_ = v___x_2210_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_del_object(v___x_2205_);
v_a_2219_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2207_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2207_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
else
{
lean_object* v___x_2228_; 
lean_dec_ref(v_f_2194_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v_v_2195_);
return v___x_2228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(lean_object* v_f_2229_, lean_object* v_v_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2229_, v_v_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(uint8_t v_pu_2239_, lean_object* v_f_2240_, lean_object* v_v_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2240_, v_v_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(lean_object* v_pu_2250_, lean_object* v_f_2251_, lean_object* v_v_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v_pu_boxed_2260_; lean_object* v_res_2261_; 
v_pu_boxed_2260_ = lean_unbox(v_pu_2250_);
v_res_2261_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_boxed_2260_, v_f_2251_, v_v_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object* v_decl_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_toSignature_2271_; lean_object* v_value_2272_; uint8_t v_recursive_2273_; lean_object* v_inlineAttr_x3f_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2299_; 
v_toSignature_2271_ = lean_ctor_get(v_decl_2263_, 0);
v_value_2272_ = lean_ctor_get(v_decl_2263_, 1);
v_recursive_2273_ = lean_ctor_get_uint8(v_decl_2263_, sizeof(void*)*3);
v_inlineAttr_x3f_2274_ = lean_ctor_get(v_decl_2263_, 2);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_decl_2263_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2276_ = v_decl_2263_;
v_isShared_2277_ = v_isSharedCheck_2299_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_inlineAttr_x3f_2274_);
lean_inc(v_value_2272_);
lean_inc(v_toSignature_2271_);
lean_dec(v_decl_2263_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2299_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0));
v___x_2279_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v___x_2278_, v_value_2272_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2290_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2277_ == 0)
{
lean_ctor_set(v___x_2276_, 1, v_a_2280_);
v___x_2285_ = v___x_2276_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_toSignature_2271_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_a_2280_);
lean_ctor_set(v_reuseFailAlloc_2289_, 2, v_inlineAttr_x3f_2274_);
lean_ctor_set_uint8(v_reuseFailAlloc_2289_, sizeof(void*)*3, v_recursive_2273_);
v___x_2285_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2287_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2285_);
v___x_2287_ = v___x_2282_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_del_object(v___x_2276_);
lean_dec(v_inlineAttr_x3f_2274_);
lean_dec_ref(v_toSignature_2271_);
v_a_2291_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2279_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2279_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(lean_object* v_decl_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
lean_dec_ref(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
return v_res_2308_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_2312_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0));
v___x_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set(v___x_2313_, 1, v___x_2311_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* v_decl_2314_, lean_object* v_sccDecls_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_toSignature_2321_; lean_object* v_name_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v_toSignature_2321_ = lean_ctor_get(v_decl_2314_, 0);
v_name_2322_ = lean_ctor_get(v_toSignature_2321_, 0);
lean_inc(v_name_2322_);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_name_2322_);
lean_ctor_set(v___x_2323_, 1, v_sccDecls_2315_);
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1);
v___x_2326_ = lean_st_mk_ref(v___x_2325_);
v___x_2327_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2314_, v___x_2323_, v___x_2326_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
lean_dec_ref_known(v___x_2323_, 2);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2353_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2353_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2353_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v_decls_2333_; lean_object* v_decl_2335_; lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2332_ = lean_st_ref_get(v___x_2326_);
lean_dec(v___x_2326_);
v_decls_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc_ref(v_decls_2333_);
lean_dec(v___x_2332_);
v___x_2340_ = lean_array_get_size(v_decls_2333_);
v___x_2341_ = lean_nat_dec_eq(v___x_2340_, v___x_2324_);
if (v___x_2341_ == 0)
{
uint8_t v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = 0;
v___x_2343_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2342_, v_a_2328_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v_decl_2335_ = v_a_2344_;
goto v___jp_2334_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v_decls_2333_);
lean_del_object(v___x_2330_);
v_a_2345_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2343_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2343_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
v_decl_2335_ = v_a_2328_;
goto v___jp_2334_;
}
v___jp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2336_ = lean_array_push(v_decls_2333_, v_decl_2335_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2336_);
v___x_2338_ = v___x_2330_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v___x_2326_);
v_a_2354_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2327_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2327_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(lean_object* v_decl_2362_, lean_object* v_sccDecls_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v_decl_2362_, v_sccDecls_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(lean_object* v_decls_2370_, lean_object* v_as_2371_, size_t v_i_2372_, size_t v_stop_2373_, lean_object* v_b_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
uint8_t v___x_2380_; 
v___x_2380_ = lean_usize_dec_eq(v_i_2372_, v_stop_2373_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_array_uget_borrowed(v_as_2371_, v_i_2372_);
lean_inc_ref(v_decls_2370_);
lean_inc(v___x_2381_);
v___x_2382_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v___x_2381_, v_decls_2370_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; size_t v___x_2385_; size_t v___x_2386_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2384_ = l_Array_append___redArg(v_b_2374_, v_a_2383_);
lean_dec(v_a_2383_);
v___x_2385_ = ((size_t)1ULL);
v___x_2386_ = lean_usize_add(v_i_2372_, v___x_2385_);
v_i_2372_ = v___x_2386_;
v_b_2374_ = v___x_2384_;
goto _start;
}
else
{
lean_dec_ref(v_b_2374_);
lean_dec_ref(v_decls_2370_);
return v___x_2382_;
}
}
else
{
lean_object* v___x_2388_; 
lean_dec_ref(v_decls_2370_);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_b_2374_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object* v_decls_2389_, lean_object* v_as_2390_, lean_object* v_i_2391_, lean_object* v_stop_2392_, lean_object* v_b_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
size_t v_i_boxed_2399_; size_t v_stop_boxed_2400_; lean_object* v_res_2401_; 
v_i_boxed_2399_ = lean_unbox_usize(v_i_2391_);
lean_dec(v_i_2391_);
v_stop_boxed_2400_ = lean_unbox_usize(v_stop_2392_);
lean_dec(v_stop_2392_);
v_res_2401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2389_, v_as_2390_, v_i_boxed_2399_, v_stop_boxed_2400_, v_b_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec_ref(v_as_2390_);
return v_res_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* v___x_2402_, lean_object* v_decls_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_2404_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2427_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2427_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2427_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
uint8_t v_extractClosed_2414_; 
v_extractClosed_2414_ = lean_ctor_get_uint8(v_a_2410_, sizeof(void*)*4 + 1);
lean_dec(v_a_2410_);
if (v_extractClosed_2414_ == 0)
{
lean_object* v___x_2416_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v_decls_2403_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_decls_2403_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2418_ = lean_mk_empty_array_with_capacity(v___x_2402_);
v___x_2419_ = lean_array_get_size(v_decls_2403_);
v___x_2420_ = lean_nat_dec_lt(v___x_2402_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2422_; 
lean_dec_ref(v_decls_2403_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2418_);
v___x_2422_ = v___x_2412_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2418_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
else
{
size_t v___x_2424_; size_t v___x_2425_; lean_object* v___x_2426_; 
lean_del_object(v___x_2412_);
v___x_2424_ = ((size_t)0ULL);
v___x_2425_ = lean_usize_of_nat(v___x_2419_);
lean_inc_ref(v_decls_2403_);
v___x_2426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2403_, v_decls_2403_, v___x_2424_, v___x_2425_, v___x_2418_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec_ref(v_decls_2403_);
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec_ref(v_decls_2403_);
v_a_2428_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2409_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2409_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object* v___x_2436_, lean_object* v_decls_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(v___x_2436_, v_decls_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___x_2436_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2526_; uint8_t v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2526_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2527_ = 1;
v___x_2528_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2529_ = l_Lean_registerTraceClass(v___x_2526_, v___x_2527_, v___x_2528_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(lean_object* v_a_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
return v_res_2531_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExtractClosed(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_ClosedTermCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NeverExtractAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_FloatArray_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ExtractClosed(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_FloatArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin);
lean_object* initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
lean_object* initialize_Init_Data_FloatArray_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ExtractClosed(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ClosedTermCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NeverExtractAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_FloatArray_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExtractClosed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ExtractClosed(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ExtractClosed(builtin);
}
#ifdef __cplusplus
}
#endif
