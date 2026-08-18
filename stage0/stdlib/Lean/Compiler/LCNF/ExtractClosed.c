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
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
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
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object*);
uint8_t l_Lean_hasNeverExtractAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(uint8_t);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toExpr(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_getClosedTermName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_cacheClosedTermName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4;
static const lean_array_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_closed"};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6_value),LEAN_SCALAR_PTR_LITERAL(29, 126, 0, 54, 34, 229, 13, 211)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__8_value;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_extractClosed___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_extractClosed___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___closed__3;
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
case 0:
{
lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_33_; 
v_isSharedCheck_33_ = !lean_is_exclusive(v_v_19_);
if (v_isSharedCheck_33_ == 0)
{
lean_object* v_unused_34_; 
v_unused_34_ = lean_ctor_get(v_v_19_, 0);
lean_dec(v_unused_34_);
v___x_27_ = v_v_19_;
v_isShared_28_ = v_isSharedCheck_33_;
goto v_resetjp_26_;
}
else
{
lean_dec(v_v_19_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_33_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_29_ = lean_box(0);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_29_);
v___x_31_ = v___x_27_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_29_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
case 1:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_box(0);
v___x_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
case 2:
{
lean_object* v_struct_37_; lean_object* v___x_38_; 
v_struct_37_ = lean_ctor_get(v_v_19_, 2);
lean_inc(v_struct_37_);
lean_dec_ref_known(v_v_19_, 3);
v___x_38_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_struct_37_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec(v_struct_37_);
return v___x_38_;
}
case 3:
{
lean_object* v_args_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_args_39_ = lean_ctor_get(v_v_19_, 2);
lean_inc_ref(v_args_39_);
lean_dec_ref_known(v_v_19_, 3);
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = lean_array_get_size(v_args_39_);
v___x_42_ = lean_box(0);
v___x_43_ = lean_nat_dec_lt(v___x_40_, v___x_41_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; 
lean_dec_ref(v_args_39_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_42_);
return v___x_44_;
}
else
{
uint8_t v___x_45_; 
v___x_45_ = lean_nat_dec_le(v___x_41_, v___x_41_);
if (v___x_45_ == 0)
{
if (v___x_43_ == 0)
{
lean_object* v___x_46_; 
lean_dec_ref(v_args_39_);
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_42_);
return v___x_46_;
}
else
{
size_t v___x_47_; size_t v___x_48_; lean_object* v___x_49_; 
v___x_47_ = ((size_t)0ULL);
v___x_48_ = lean_usize_of_nat(v___x_41_);
v___x_49_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_39_, v___x_47_, v___x_48_, v___x_42_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec_ref(v_args_39_);
return v___x_49_;
}
}
else
{
size_t v___x_50_; size_t v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((size_t)0ULL);
v___x_51_ = lean_usize_of_nat(v___x_41_);
v___x_52_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_39_, v___x_50_, v___x_51_, v___x_42_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec_ref(v_args_39_);
return v___x_52_;
}
}
}
default: 
{
lean_object* v_fvarId_53_; lean_object* v_args_54_; lean_object* v___x_55_; 
v_fvarId_53_ = lean_ctor_get(v_v_19_, 0);
lean_inc(v_fvarId_53_);
v_args_54_ = lean_ctor_get(v_v_19_, 1);
lean_inc_ref(v_args_54_);
lean_dec_ref_known(v_v_19_, 2);
v___x_55_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_53_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec(v_fvarId_53_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_76_; 
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_76_ == 0)
{
lean_object* v_unused_77_; 
v_unused_77_ = lean_ctor_get(v___x_55_, 0);
lean_dec(v_unused_77_);
v___x_57_ = v___x_55_;
v_isShared_58_ = v_isSharedCheck_76_;
goto v_resetjp_56_;
}
else
{
lean_dec(v___x_55_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_76_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = lean_array_get_size(v_args_54_);
v___x_61_ = lean_box(0);
v___x_62_ = lean_nat_dec_lt(v___x_59_, v___x_60_);
if (v___x_62_ == 0)
{
lean_object* v___x_64_; 
lean_dec_ref(v_args_54_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_61_);
v___x_64_ = v___x_57_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_61_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
else
{
uint8_t v___x_66_; 
v___x_66_ = lean_nat_dec_le(v___x_60_, v___x_60_);
if (v___x_66_ == 0)
{
if (v___x_62_ == 0)
{
lean_object* v___x_68_; 
lean_dec_ref(v_args_54_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_61_);
v___x_68_ = v___x_57_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_61_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
else
{
size_t v___x_70_; size_t v___x_71_; lean_object* v___x_72_; 
lean_del_object(v___x_57_);
v___x_70_ = ((size_t)0ULL);
v___x_71_ = lean_usize_of_nat(v___x_60_);
v___x_72_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_54_, v___x_70_, v___x_71_, v___x_61_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec_ref(v_args_54_);
return v___x_72_;
}
}
else
{
size_t v___x_73_; size_t v___x_74_; lean_object* v___x_75_; 
lean_del_object(v___x_57_);
v___x_73_ = ((size_t)0ULL);
v___x_74_ = lean_usize_of_nat(v___x_60_);
v___x_75_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_54_, v___x_73_, v___x_74_, v___x_61_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec_ref(v_args_54_);
return v___x_75_;
}
}
}
}
else
{
lean_dec_ref(v_args_54_);
return v___x_55_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(lean_object* v_fvarId_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
uint8_t v___x_85_; lean_object* v___x_86_; 
v___x_85_ = 0;
v___x_86_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_85_, v_fvarId_78_, v_a_81_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_108_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_108_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_108_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_108_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
if (lean_obj_tag(v_a_87_) == 1)
{
lean_object* v_val_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_103_; 
lean_del_object(v___x_89_);
v_val_91_ = lean_ctor_get(v_a_87_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v_a_87_);
if (v_isSharedCheck_103_ == 0)
{
v___x_93_ = v_a_87_;
v_isShared_94_ = v_isSharedCheck_103_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_val_91_);
lean_dec(v_a_87_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_103_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_95_ = lean_st_ref_take(v_a_79_);
lean_inc(v_val_91_);
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 0);
v___x_97_ = v___x_93_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_val_91_);
v___x_97_ = v_reuseFailAlloc_102_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_value_100_; lean_object* v___x_101_; 
v___x_98_ = lean_array_push(v___x_95_, v___x_97_);
v___x_99_ = lean_st_ref_put(v_a_79_, v___x_98_);
v_value_100_ = lean_ctor_get(v_val_91_, 3);
lean_inc(v_value_100_);
lean_dec(v_val_91_);
v___x_101_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_100_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
return v___x_101_;
}
}
}
else
{
lean_object* v___x_104_; lean_object* v___x_106_; 
lean_dec(v_a_87_);
v___x_104_ = lean_box(0);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_104_);
v___x_106_ = v___x_89_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
v_a_109_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v___x_86_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_86_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg(lean_object* v_arg_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
if (lean_obj_tag(v_arg_117_) == 1)
{
lean_object* v_fvarId_124_; lean_object* v___x_125_; 
v_fvarId_124_ = lean_ctor_get(v_arg_117_, 0);
v___x_125_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_124_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_box(0);
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg___boxed(lean_object* v_arg_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(v_arg_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec(v_arg_128_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0___boxed(lean_object* v_as_136_, lean_object* v_i_137_, lean_object* v_stop_138_, lean_object* v_b_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
size_t v_i_boxed_146_; size_t v_stop_boxed_147_; lean_object* v_res_148_; 
v_i_boxed_146_ = lean_unbox_usize(v_i_137_);
lean_dec(v_i_137_);
v_stop_boxed_147_ = lean_unbox_usize(v_stop_138_);
lean_dec(v_stop_138_);
v_res_148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_as_136_, v_i_boxed_146_, v_stop_boxed_147_, v_b_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v_as_136_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar___boxed(lean_object* v_fvarId_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec(v_fvarId_149_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___boxed(lean_object* v_v_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_v_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
return v_res_164_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(lean_object* v_arg_165_){
_start:
{
if (lean_obj_tag(v_arg_165_) == 1)
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
else
{
uint8_t v___x_167_; 
v___x_167_ = 1;
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg___boxed(lean_object* v_arg_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v_arg_168_);
lean_dec(v_arg_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(lean_object* v_m_171_, lean_object* v_query_172_, lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_zero_176_; uint8_t v_isZero_177_; 
v_zero_176_ = lean_unsigned_to_nat(0u);
v_isZero_177_ = lean_nat_dec_eq(v_x_174_, v_zero_176_);
if (v_isZero_177_ == 1)
{
lean_dec(v_x_175_);
lean_dec(v_x_174_);
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(2);
return v___x_178_;
}
else
{
lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_val_179_ = lean_ctor_get(v_x_173_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v_x_173_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_dec(v_x_173_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_val_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v_keyArray_187_; lean_object* v_valueArray_188_; lean_object* v___x_189_; uint8_t v_isSome_190_; 
v_keyArray_187_ = lean_ctor_get(v_m_171_, 1);
v_valueArray_188_ = lean_ctor_get(v_m_171_, 2);
v___x_189_ = lean_array_fget_borrowed(v_keyArray_187_, v_x_175_);
v_isSome_190_ = lean_noption_is_some(v___x_189_);
if (v_isSome_190_ == 0)
{
lean_dec(v_x_174_);
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v_x_175_);
return v___x_191_;
}
else
{
lean_object* v_val_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec(v_x_175_);
v_val_192_ = lean_ctor_get(v_x_173_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v_x_173_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_val_192_);
lean_dec(v_x_173_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_val_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_one_200_; lean_object* v_n_201_; lean_object* v___y_203_; 
v_one_200_ = lean_unsigned_to_nat(1u);
v_n_201_ = lean_nat_sub(v_x_174_, v_one_200_);
lean_dec(v_x_174_);
if (v_isSome_190_ == 0)
{
goto v___jp_209_;
}
else
{
lean_object* v___x_211_; uint8_t v_isSome_212_; 
v___x_211_ = lean_array_fget_borrowed(v_valueArray_188_, v_x_175_);
v_isSome_212_ = lean_noption_is_some(v___x_211_);
if (v_isSome_212_ == 0)
{
goto v___jp_209_;
}
else
{
lean_object* v_val_213_; uint8_t v___x_214_; 
lean_inc(v___x_189_);
v_val_213_ = lean_noption_get(v___x_189_);
v___x_214_ = l_Lean_instBEqFVarId_beq(v_val_213_, v_query_172_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
lean_dec(v_val_213_);
v___x_215_ = lean_array_get_size(v_keyArray_187_);
v___x_216_ = lean_nat_add(v_x_175_, v_one_200_);
lean_dec(v_x_175_);
v___x_217_ = lean_nat_dec_lt(v___x_216_, v___x_215_);
if (v___x_217_ == 0)
{
lean_dec(v___x_216_);
v_x_174_ = v_n_201_;
v_x_175_ = v_zero_176_;
goto _start;
}
else
{
v_x_174_ = v_n_201_;
v_x_175_ = v___x_216_;
goto _start;
}
}
else
{
lean_object* v_val_220_; lean_object* v___x_221_; 
lean_dec(v_n_201_);
lean_dec(v_x_173_);
lean_inc(v___x_211_);
v_val_220_ = lean_noption_get(v___x_211_);
v___x_221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_221_, 0, v_x_175_);
lean_ctor_set(v___x_221_, 1, v_val_213_);
lean_ctor_set(v___x_221_, 2, v_val_220_);
return v___x_221_;
}
}
}
v___jp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_204_ = lean_array_get_size(v_keyArray_187_);
v___x_205_ = lean_nat_add(v_x_175_, v_one_200_);
lean_dec(v_x_175_);
v___x_206_ = lean_nat_dec_lt(v___x_205_, v___x_204_);
if (v___x_206_ == 0)
{
lean_dec(v___x_205_);
v_x_173_ = v___y_203_;
v_x_174_ = v_n_201_;
v_x_175_ = v_zero_176_;
goto _start;
}
else
{
v_x_173_ = v___y_203_;
v_x_174_ = v_n_201_;
v_x_175_ = v___x_205_;
goto _start;
}
}
v___jp_209_:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_210_; 
lean_inc(v_x_175_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v_x_175_);
v___y_203_ = v___x_210_;
goto v___jp_202_;
}
else
{
v___y_203_ = v_x_173_;
goto v___jp_202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg___boxed(lean_object* v_m_222_, lean_object* v_query_223_, lean_object* v_x_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_m_222_, v_query_223_, v_x_224_, v_x_225_, v_x_226_);
lean_dec(v_query_223_);
lean_dec_ref(v_m_222_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(lean_object* v_m_228_, lean_object* v_query_229_){
_start:
{
lean_object* v_keyArray_230_; lean_object* v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v_fold_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_keyArray_230_ = lean_ctor_get(v_m_228_, 1);
v___x_231_ = lean_array_get_size(v_keyArray_230_);
v___x_232_ = l_Lean_instHashableFVarId_hash(v_query_229_);
v___x_233_ = 32ULL;
v___x_234_ = lean_uint64_shift_right(v___x_232_, v___x_233_);
v_fold_235_ = lean_uint64_xor(v___x_232_, v___x_234_);
v___x_236_ = 16ULL;
v___x_237_ = lean_uint64_shift_right(v_fold_235_, v___x_236_);
v___x_238_ = lean_uint64_xor(v_fold_235_, v___x_237_);
v___x_239_ = lean_uint64_to_usize(v___x_238_);
v___x_240_ = lean_usize_of_nat(v___x_231_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_sub(v___x_240_, v___x_241_);
v___x_243_ = lean_usize_land(v___x_239_, v___x_242_);
v___x_244_ = lean_usize_to_nat(v___x_243_);
v___x_245_ = lean_box(0);
v___x_246_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_m_228_, v_query_229_, v___x_245_, v___x_231_, v___x_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg___boxed(lean_object* v_m_247_, lean_object* v_query_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_m_247_, v_query_248_);
lean_dec(v_query_248_);
lean_dec_ref(v_m_247_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(lean_object* v_m_250_, lean_object* v_query_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_m_250_, v_query_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_index_253_; lean_object* v_key_254_; lean_object* v_value_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_index_253_ = lean_ctor_get(v___x_252_, 0);
v_key_254_ = lean_ctor_get(v___x_252_, 1);
v_value_255_ = lean_ctor_get(v___x_252_, 2);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_252_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_value_255_);
lean_inc(v_key_254_);
lean_inc(v_index_253_);
lean_dec(v___x_252_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_index_253_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_key_254_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_value_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v___x_263_; 
lean_dec(v___x_252_);
v___x_263_ = lean_box(1);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg___boxed(lean_object* v_m_264_, lean_object* v_query_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_m_264_, v_query_265_);
lean_dec(v_query_265_);
lean_dec_ref(v_m_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_m_267_, v_a_268_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_value_270_; lean_object* v___x_271_; 
v_value_270_ = lean_ctor_get(v___x_269_, 2);
lean_inc(v_value_270_);
lean_dec_ref_known(v___x_269_, 3);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v_value_270_);
return v___x_271_;
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg___boxed(lean_object* v_m_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_m_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12___redArg(lean_object* v_b_276_, lean_object* v_acc_277_, lean_object* v_i_278_){
_start:
{
lean_object* v___y_280_; lean_object* v_keyArray_288_; lean_object* v_valueArray_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_keyArray_288_ = lean_ctor_get(v_b_276_, 1);
v_valueArray_289_ = lean_ctor_get(v_b_276_, 2);
v___x_290_ = lean_array_get_size(v_keyArray_288_);
v___x_291_ = lean_nat_dec_lt(v_i_278_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec(v_i_278_);
return v_acc_277_;
}
else
{
lean_object* v___x_292_; uint8_t v_isSome_293_; 
v___x_292_ = lean_array_fget_borrowed(v_keyArray_288_, v_i_278_);
v_isSome_293_ = lean_noption_is_some(v___x_292_);
if (v_isSome_293_ == 0)
{
goto v___jp_284_;
}
else
{
lean_object* v___x_294_; uint8_t v_isSome_295_; 
v___x_294_ = lean_array_fget_borrowed(v_valueArray_289_, v_i_278_);
v_isSome_295_ = lean_noption_is_some(v___x_294_);
if (v_isSome_295_ == 0)
{
goto v___jp_284_;
}
else
{
lean_object* v_val_296_; lean_object* v_val_297_; lean_object* v_i_299_; lean_object* v___x_304_; 
lean_inc(v___x_292_);
v_val_296_ = lean_noption_get(v___x_292_);
lean_inc(v___x_294_);
v_val_297_ = lean_noption_get(v___x_294_);
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_acc_277_, v_val_296_);
switch(lean_obj_tag(v___x_304_))
{
case 0:
{
lean_object* v_index_305_; lean_object* v_size_306_; lean_object* v___x_307_; 
v_index_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_index_305_);
lean_dec_ref_known(v___x_304_, 3);
v_size_306_ = lean_ctor_get(v_acc_277_, 0);
lean_inc(v_size_306_);
v___x_307_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_277_, v_size_306_, v_index_305_, v_val_296_, v_val_297_);
lean_dec(v_index_305_);
v___y_280_ = v___x_307_;
goto v___jp_279_;
}
case 1:
{
lean_object* v_index_308_; 
v_index_308_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_index_308_);
lean_dec_ref_known(v___x_304_, 1);
v_i_299_ = v_index_308_;
goto v___jp_298_;
}
default: 
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_277_, v___x_309_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_index_311_; 
v_index_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_index_311_);
lean_dec_ref_known(v___x_310_, 1);
v_i_299_ = v_index_311_;
goto v___jp_298_;
}
else
{
lean_dec(v_val_297_);
lean_dec(v_val_296_);
v___y_280_ = v_acc_277_;
goto v___jp_279_;
}
}
}
v___jp_298_:
{
lean_object* v_size_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_size_300_ = lean_ctor_get(v_acc_277_, 0);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_size_300_, v___x_301_);
v___x_303_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_277_, v___x_302_, v_i_299_, v_val_296_, v_val_297_);
lean_dec(v_i_299_);
v___y_280_ = v___x_303_;
goto v___jp_279_;
}
}
}
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1u);
v___x_282_ = lean_nat_add(v_i_278_, v___x_281_);
lean_dec(v_i_278_);
v_acc_277_ = v___y_280_;
v_i_278_ = v___x_282_;
goto _start;
}
v___jp_284_:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_i_278_, v___x_285_);
lean_dec(v_i_278_);
v_i_278_ = v___x_286_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12___redArg___boxed(lean_object* v_b_312_, lean_object* v_acc_313_, lean_object* v_i_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12___redArg(v_b_312_, v_acc_313_, v_i_314_);
lean_dec_ref(v_b_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11___redArg(lean_object* v_init_316_, lean_object* v_b_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12___redArg(v_b_317_, v_init_316_, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11___redArg___boxed(lean_object* v_init_320_, lean_object* v_b_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11___redArg(v_init_320_, v_b_321_);
lean_dec_ref(v_b_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___redArg(lean_object* v_m_323_){
_start:
{
lean_object* v_keyArray_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_cellCount_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_target_331_; lean_object* v___x_332_; 
v_keyArray_324_ = lean_ctor_get(v_m_323_, 1);
v___x_325_ = lean_array_get_size(v_keyArray_324_);
v___x_326_ = lean_unsigned_to_nat(2u);
v_cellCount_327_ = lean_nat_mul(v___x_325_, v___x_326_);
v___x_328_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_327_);
v___x_329_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_327_);
v___x_330_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_327_);
v_target_331_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_331_, 0, v___x_328_);
lean_ctor_set(v_target_331_, 1, v___x_329_);
lean_ctor_set(v_target_331_, 2, v___x_330_);
v___x_332_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11___redArg(v_target_331_, v_m_323_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___redArg___boxed(lean_object* v_m_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___redArg(v_m_333_);
lean_dec_ref(v_m_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t v_____do__lift_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
if (v_____do__lift_335_ == 0)
{
uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = 1;
v___x_344_ = lean_box(v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
else
{
uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = 0;
v___x_347_ = lean_box(v___x_346_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object* v_____do__lift_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
uint8_t v_____do__lift_20392__boxed_357_; lean_object* v_res_358_; 
v_____do__lift_20392__boxed_357_ = lean_unbox(v_____do__lift_349_);
v_res_358_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v_____do__lift_20392__boxed_357_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_358_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(lean_object* v_declName_359_, lean_object* v_as_360_, size_t v_i_361_, size_t v_stop_362_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_eq(v_i_361_, v_stop_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v_toSignature_365_; lean_object* v_name_366_; uint8_t v___x_367_; 
v___x_364_ = lean_array_uget_borrowed(v_as_360_, v_i_361_);
v_toSignature_365_ = lean_ctor_get(v___x_364_, 0);
v_name_366_ = lean_ctor_get(v_toSignature_365_, 0);
v___x_367_ = lean_name_eq(v_name_366_, v_declName_359_);
if (v___x_367_ == 0)
{
size_t v___x_368_; size_t v___x_369_; 
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_add(v_i_361_, v___x_368_);
v_i_361_ = v___x_369_;
goto _start;
}
else
{
return v___x_367_;
}
}
else
{
uint8_t v___x_371_; 
v___x_371_ = 0;
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3___boxed(lean_object* v_declName_372_, lean_object* v_as_373_, lean_object* v_i_374_, lean_object* v_stop_375_){
_start:
{
size_t v_i_boxed_376_; size_t v_stop_boxed_377_; uint8_t v_res_378_; lean_object* v_r_379_; 
v_i_boxed_376_ = lean_unbox_usize(v_i_374_);
lean_dec(v_i_374_);
v_stop_boxed_377_ = lean_unbox_usize(v_stop_375_);
lean_dec(v_stop_375_);
v_res_378_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_372_, v_as_373_, v_i_boxed_376_, v_stop_boxed_377_);
lean_dec_ref(v_as_373_);
lean_dec(v_declName_372_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(uint8_t v_isRoot_380_, uint8_t v___x_381_, lean_object* v_as_382_, size_t v_i_383_, size_t v_stop_384_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = lean_usize_dec_eq(v_i_383_, v_stop_384_);
if (v___x_385_ == 0)
{
uint8_t v___x_386_; uint8_t v___y_388_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_386_ = 1;
v___x_392_ = lean_array_uget_borrowed(v_as_382_, v_i_383_);
v___x_393_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v___x_392_);
if (v___x_393_ == 0)
{
v___y_388_ = v_isRoot_380_;
goto v___jp_387_;
}
else
{
v___y_388_ = v___x_381_;
goto v___jp_387_;
}
v___jp_387_:
{
if (v___y_388_ == 0)
{
size_t v___x_389_; size_t v___x_390_; 
v___x_389_ = ((size_t)1ULL);
v___x_390_ = lean_usize_add(v_i_383_, v___x_389_);
v_i_383_ = v___x_390_;
goto _start;
}
else
{
return v___x_386_;
}
}
}
else
{
uint8_t v___x_394_; 
v___x_394_ = 0;
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object* v_isRoot_395_, lean_object* v___x_396_, lean_object* v_as_397_, lean_object* v_i_398_, lean_object* v_stop_399_){
_start:
{
uint8_t v_isRoot_boxed_400_; uint8_t v___x_20445__boxed_401_; size_t v_i_boxed_402_; size_t v_stop_boxed_403_; uint8_t v_res_404_; lean_object* v_r_405_; 
v_isRoot_boxed_400_ = lean_unbox(v_isRoot_395_);
v___x_20445__boxed_401_ = lean_unbox(v___x_396_);
v_i_boxed_402_ = lean_unbox_usize(v_i_398_);
lean_dec(v_i_398_);
v_stop_boxed_403_ = lean_unbox_usize(v_stop_399_);
lean_dec(v_stop_399_);
v_res_404_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_boxed_400_, v___x_20445__boxed_401_, v_as_397_, v_i_boxed_402_, v_stop_boxed_403_);
lean_dec_ref(v_as_397_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0(void){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_cstr_to_nat("9223372036854775808");
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(uint8_t v___x_407_, lean_object* v_as_408_, size_t v_i_409_, size_t v_stop_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_eq(v_i_409_, v_stop_410_);
if (v___x_418_ == 0)
{
uint8_t v___x_419_; uint8_t v_a_421_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_419_ = 1;
v___x_427_ = lean_array_uget_borrowed(v_as_408_, v_i_409_);
lean_inc(v___x_427_);
v___x_428_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_427_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_438_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_438_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_438_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_438_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
uint8_t v___x_433_; 
v___x_433_ = lean_unbox(v_a_429_);
lean_dec(v_a_429_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = lean_box(v___x_419_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_434_);
v___x_436_ = v___x_431_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
else
{
lean_del_object(v___x_431_);
v_a_421_ = v___x_407_;
goto v___jp_420_;
}
}
}
else
{
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_439_; uint8_t v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_428_, 1);
v___x_440_ = lean_unbox(v_a_439_);
lean_dec(v_a_439_);
v_a_421_ = v___x_440_;
goto v___jp_420_;
}
else
{
return v___x_428_;
}
}
v___jp_420_:
{
if (v_a_421_ == 0)
{
size_t v___x_422_; size_t v___x_423_; 
v___x_422_ = ((size_t)1ULL);
v___x_423_ = lean_usize_add(v_i_409_, v___x_422_);
v_i_409_ = v___x_423_;
goto _start;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_box(v___x_419_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
}
else
{
uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = 0;
v___x_442_ = lean_box(v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(lean_object* v_as_444_, size_t v_i_445_, size_t v_stop_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = lean_usize_dec_eq(v_i_445_, v_stop_446_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; uint8_t v_a_457_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_455_ = 1;
v___x_463_ = lean_array_uget_borrowed(v_as_444_, v_i_445_);
lean_inc(v___x_463_);
v___x_464_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_463_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_474_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_474_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_474_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
uint8_t v___x_469_; 
v___x_469_ = lean_unbox(v_a_465_);
lean_dec(v_a_465_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = lean_box(v___x_455_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_470_);
v___x_472_ = v___x_467_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
else
{
lean_del_object(v___x_467_);
v_a_457_ = v___x_454_;
goto v___jp_456_;
}
}
}
else
{
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_475_; uint8_t v___x_476_; 
v_a_475_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_464_, 1);
v___x_476_ = lean_unbox(v_a_475_);
lean_dec(v_a_475_);
v_a_457_ = v___x_476_;
goto v___jp_456_;
}
else
{
return v___x_464_;
}
}
v___jp_456_:
{
if (v_a_457_ == 0)
{
size_t v___x_458_; size_t v___x_459_; 
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_add(v_i_445_, v___x_458_);
v_i_445_ = v___x_459_;
goto _start;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_box(v___x_455_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
}
else
{
uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = 0;
v___x_478_ = lean_box(v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t v_isRoot_480_, lean_object* v_v_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
uint8_t v___y_490_; uint8_t v_____do__lift_491_; 
switch(lean_obj_tag(v_v_481_))
{
case 0:
{
lean_object* v_value_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_542_; 
v_value_497_ = lean_ctor_get(v_v_481_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v_v_481_);
if (v_isSharedCheck_542_ == 0)
{
v___x_499_ = v_v_481_;
v_isShared_500_ = v_isSharedCheck_542_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_value_497_);
lean_dec(v_v_481_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_542_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
switch(lean_obj_tag(v_value_497_))
{
case 1:
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_509_; 
lean_del_object(v___x_499_);
v_isSharedCheck_509_ = !lean_is_exclusive(v_value_497_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v_value_497_, 0);
lean_dec(v_unused_510_);
v___x_502_ = v_value_497_;
v_isShared_503_ = v_isSharedCheck_509_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_value_497_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_509_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = 1;
v___x_505_ = lean_box(v___x_504_);
if (v_isShared_503_ == 0)
{
lean_ctor_set_tag(v___x_502_, 0);
lean_ctor_set(v___x_502_, 0, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
case 0:
{
lean_del_object(v___x_499_);
if (v_isRoot_480_ == 0)
{
lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_519_; 
v_isSharedCheck_519_ = !lean_is_exclusive(v_value_497_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v_value_497_, 0);
lean_dec(v_unused_520_);
v___x_512_ = v_value_497_;
v_isShared_513_ = v_isSharedCheck_519_;
goto v_resetjp_511_;
}
else
{
lean_dec(v_value_497_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_519_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_514_ = 1;
v___x_515_ = lean_box(v___x_514_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_515_);
v___x_517_ = v___x_512_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
else
{
lean_object* v_val_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_531_; 
v_val_521_ = lean_ctor_get(v_value_497_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_value_497_);
if (v_isSharedCheck_531_ == 0)
{
v___x_523_ = v_value_497_;
v_isShared_524_ = v_isSharedCheck_531_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_val_521_);
lean_dec(v_value_497_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_531_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_525_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0, &l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0);
v___x_526_ = lean_nat_dec_le(v___x_525_, v_val_521_);
lean_dec(v_val_521_);
v___x_527_ = lean_box(v___x_526_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_527_);
v___x_529_ = v___x_523_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
default: 
{
lean_dec_ref(v_value_497_);
if (v_isRoot_480_ == 0)
{
uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = 1;
v___x_533_ = lean_box(v___x_532_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_533_);
v___x_535_ = v___x_499_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = 0;
v___x_538_ = lean_box(v___x_537_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_538_);
v___x_540_ = v___x_499_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
case 1:
{
if (v_isRoot_480_ == 0)
{
uint8_t v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = 1;
v___x_544_ = lean_box(v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
else
{
uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = 0;
v___x_547_ = lean_box(v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
case 2:
{
lean_object* v_struct_549_; lean_object* v___x_550_; 
v_struct_549_ = lean_ctor_get(v_v_481_, 2);
lean_inc(v_struct_549_);
lean_dec_ref_known(v_v_481_, 3);
v___x_550_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_struct_549_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
return v___x_550_;
}
case 3:
{
lean_object* v_declName_551_; lean_object* v_args_552_; lean_object* v_sccDecls_553_; lean_object* v___x_554_; uint8_t v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; uint8_t v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; uint8_t v___y_600_; uint8_t v___y_604_; uint8_t v___y_605_; uint8_t v___y_609_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_declName_551_ = lean_ctor_get(v_v_481_, 0);
lean_inc(v_declName_551_);
v_args_552_ = lean_ctor_get(v_v_481_, 2);
lean_inc_ref(v_args_552_);
lean_dec_ref_known(v_v_481_, 3);
v_sccDecls_553_ = lean_ctor_get(v_a_482_, 1);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_array_get_size(v_sccDecls_553_);
v___x_629_ = lean_nat_dec_lt(v___x_554_, v___x_628_);
if (v___x_629_ == 0)
{
v___y_609_ = v___x_629_;
goto v___jp_608_;
}
else
{
if (v___x_629_ == 0)
{
v___y_609_ = v___x_629_;
goto v___jp_608_;
}
else
{
size_t v___x_630_; size_t v___x_631_; uint8_t v___x_632_; 
v___x_630_ = ((size_t)0ULL);
v___x_631_ = lean_usize_of_nat(v___x_628_);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_551_, v_sccDecls_553_, v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
v___y_609_ = v___x_632_;
goto v___jp_608_;
}
else
{
uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v_args_552_);
lean_dec(v_declName_551_);
v___x_633_ = 0;
v___x_634_ = lean_box(v___x_633_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
}
}
v___jp_555_:
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = lean_array_get_size(v_args_552_);
v___x_564_ = lean_nat_dec_lt(v___x_554_, v___x_563_);
if (v___x_564_ == 0)
{
lean_dec_ref(v_args_552_);
v___y_490_ = v___y_556_;
v_____do__lift_491_ = v___y_556_;
goto v___jp_489_;
}
else
{
if (v___x_564_ == 0)
{
lean_dec_ref(v_args_552_);
v___y_490_ = v___y_556_;
v_____do__lift_491_ = v___y_556_;
goto v___jp_489_;
}
else
{
size_t v___x_565_; size_t v___x_566_; lean_object* v___x_567_; 
v___x_565_ = ((size_t)0ULL);
v___x_566_ = lean_usize_of_nat(v___x_563_);
v___x_567_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___y_556_, v_args_552_, v___x_565_, v___x_566_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec_ref(v_args_552_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; uint8_t v___x_569_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_567_, 1);
v___x_569_ = lean_unbox(v_a_568_);
lean_dec(v_a_568_);
v___y_490_ = v___y_556_;
v_____do__lift_491_ = v___x_569_;
goto v___jp_489_;
}
else
{
return v___x_567_;
}
}
}
}
v___jp_570_:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_551_, v___y_577_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_590_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_590_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_590_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_590_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
if (lean_obj_tag(v_a_579_) == 1)
{
lean_object* v_val_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_val_583_ = lean_ctor_get(v_a_579_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v_a_579_, 1);
v___x_584_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_583_);
lean_dec(v_val_583_);
v___x_585_ = lean_nat_dec_eq(v___x_584_, v___x_554_);
lean_dec(v___x_584_);
if (v___x_585_ == 0)
{
lean_del_object(v___x_581_);
v___y_556_ = v___y_571_;
v___y_557_ = v___y_572_;
v___y_558_ = v___y_573_;
v___y_559_ = v___y_574_;
v___y_560_ = v___y_575_;
v___y_561_ = v___y_576_;
v___y_562_ = v___y_577_;
goto v___jp_555_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_588_; 
lean_dec_ref(v_args_552_);
v___x_586_ = lean_box(v___y_571_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_586_);
v___x_588_ = v___x_581_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_del_object(v___x_581_);
lean_dec(v_a_579_);
v___y_556_ = v___y_571_;
v___y_557_ = v___y_572_;
v___y_558_ = v___y_573_;
v___y_559_ = v___y_574_;
v___y_560_ = v___y_575_;
v___y_561_ = v___y_576_;
v___y_562_ = v___y_577_;
goto v___jp_555_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref(v_args_552_);
v_a_591_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_578_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_578_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
v___jp_599_:
{
if (v___y_600_ == 0)
{
v___y_571_ = v___y_600_;
v___y_572_ = v_a_482_;
v___y_573_ = v_a_483_;
v___y_574_ = v_a_484_;
v___y_575_ = v_a_485_;
v___y_576_ = v_a_486_;
v___y_577_ = v_a_487_;
goto v___jp_570_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec_ref(v_args_552_);
lean_dec(v_declName_551_);
v___x_601_ = lean_box(v___y_600_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
v___jp_603_:
{
if (v___y_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec_ref(v_args_552_);
lean_dec(v_declName_551_);
v___x_606_ = lean_box(v___y_604_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
else
{
v___y_600_ = v___y_604_;
goto v___jp_599_;
}
}
v___jp_608_:
{
lean_object* v___x_610_; lean_object* v_env_611_; uint8_t v___x_612_; 
v___x_610_ = lean_st_ref_get(v_a_487_);
v_env_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc_ref(v_env_611_);
lean_dec(v___x_610_);
lean_inc(v_declName_551_);
v___x_612_ = l_Lean_hasNeverExtractAttribute(v_env_611_, v_declName_551_);
if (v___x_612_ == 0)
{
if (v_isRoot_480_ == 0)
{
lean_dec(v_declName_551_);
v___y_556_ = v___x_612_;
v___y_557_ = v_a_482_;
v___y_558_ = v_a_483_;
v___y_559_ = v_a_484_;
v___y_560_ = v_a_485_;
v___y_561_ = v_a_486_;
v___y_562_ = v_a_487_;
goto v___jp_555_;
}
else
{
lean_object* v___x_613_; lean_object* v_env_614_; lean_object* v___x_615_; 
v___x_613_ = lean_st_ref_get(v_a_487_);
v_env_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_613_);
lean_inc(v_declName_551_);
v___x_615_ = l_Lean_Environment_find_x3f(v_env_614_, v_declName_551_, v___x_612_);
if (lean_obj_tag(v___x_615_) == 1)
{
lean_object* v_val_616_; 
v_val_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_val_616_);
lean_dec_ref_known(v___x_615_, 1);
switch(lean_obj_tag(v_val_616_))
{
case 1:
{
lean_object* v_val_617_; lean_object* v_toConstantVal_618_; lean_object* v_type_619_; uint8_t v___x_620_; 
v_val_617_ = lean_ctor_get(v_val_616_, 0);
lean_inc_ref(v_val_617_);
lean_dec_ref_known(v_val_616_, 1);
v_toConstantVal_618_ = lean_ctor_get(v_val_617_, 0);
lean_inc_ref(v_toConstantVal_618_);
lean_dec_ref(v_val_617_);
v_type_619_ = lean_ctor_get(v_toConstantVal_618_, 2);
lean_inc_ref(v_type_619_);
lean_dec_ref(v_toConstantVal_618_);
v___x_620_ = l_Lean_Expr_isForall(v_type_619_);
lean_dec_ref(v_type_619_);
v___y_604_ = v___x_612_;
v___y_605_ = v___x_620_;
goto v___jp_603_;
}
case 6:
{
lean_object* v___x_621_; uint8_t v___x_622_; 
lean_dec_ref_known(v_val_616_, 1);
v___x_621_ = lean_array_get_size(v_args_552_);
v___x_622_ = lean_nat_dec_lt(v___x_554_, v___x_621_);
if (v___x_622_ == 0)
{
v___y_604_ = v___x_612_;
v___y_605_ = v___x_612_;
goto v___jp_603_;
}
else
{
if (v___x_622_ == 0)
{
v___y_604_ = v___x_612_;
v___y_605_ = v___x_612_;
goto v___jp_603_;
}
else
{
size_t v___x_623_; size_t v___x_624_; uint8_t v___x_625_; 
v___x_623_ = ((size_t)0ULL);
v___x_624_ = lean_usize_of_nat(v___x_621_);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_480_, v___x_612_, v_args_552_, v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
v___y_604_ = v___x_612_;
v___y_605_ = v___x_612_;
goto v___jp_603_;
}
else
{
v___y_604_ = v___x_612_;
v___y_605_ = v___x_625_;
goto v___jp_603_;
}
}
}
}
default: 
{
lean_dec(v_val_616_);
v___y_600_ = v___x_612_;
goto v___jp_599_;
}
}
}
else
{
lean_dec(v___x_615_);
v___y_571_ = v___x_612_;
v___y_572_ = v_a_482_;
v___y_573_ = v_a_483_;
v___y_574_ = v_a_484_;
v___y_575_ = v_a_485_;
v___y_576_ = v_a_486_;
v___y_577_ = v_a_487_;
goto v___jp_570_;
}
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v_args_552_);
lean_dec(v_declName_551_);
v___x_626_ = lean_box(v___y_609_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
}
default: 
{
lean_object* v_fvarId_636_; lean_object* v_args_637_; lean_object* v___x_638_; 
v_fvarId_636_ = lean_ctor_get(v_v_481_, 0);
lean_inc(v_fvarId_636_);
v_args_637_ = lean_ctor_get(v_v_481_, 1);
lean_inc_ref(v_args_637_);
lean_dec_ref_known(v_v_481_, 2);
v___x_638_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_636_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___y_641_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_array_get_size(v_args_637_);
v___x_653_ = lean_nat_dec_lt(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref(v_args_637_);
v___x_654_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_653_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
v___y_641_ = v___x_654_;
goto v___jp_640_;
}
else
{
if (v___x_653_ == 0)
{
lean_object* v___x_655_; 
lean_dec_ref(v_args_637_);
v___x_655_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_653_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
v___y_641_ = v___x_655_;
goto v___jp_640_;
}
else
{
size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_of_nat(v___x_652_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_args_637_, v___x_656_, v___x_657_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
lean_dec_ref(v_args_637_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; uint8_t v___x_660_; lean_object* v___x_661_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = lean_unbox(v_a_659_);
lean_dec(v_a_659_);
v___x_661_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_660_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
v___y_641_ = v___x_661_;
goto v___jp_640_;
}
else
{
v___y_641_ = v___x_658_;
goto v___jp_640_;
}
}
}
v___jp_640_:
{
if (lean_obj_tag(v___y_641_) == 0)
{
uint8_t v___x_642_; 
v___x_642_ = lean_unbox(v_a_639_);
if (v___x_642_ == 0)
{
lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
v_isSharedCheck_649_ = !lean_is_exclusive(v___y_641_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v___y_641_, 0);
lean_dec(v_unused_650_);
v___x_644_ = v___y_641_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_dec(v___y_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_a_639_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_639_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_dec(v_a_639_);
return v___y_641_;
}
}
else
{
lean_dec(v_a_639_);
return v___y_641_;
}
}
}
else
{
lean_dec_ref(v_args_637_);
return v___x_638_;
}
}
}
v___jp_489_:
{
if (v_____do__lift_491_ == 0)
{
uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = 1;
v___x_493_ = lean_box(v___x_492_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_box(v___y_490_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(lean_object* v_fvarId_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
uint8_t v___x_670_; lean_object* v___x_671_; 
v___x_670_ = 0;
v___x_671_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_670_, v_fvarId_662_, v_a_666_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_685_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_685_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_685_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_685_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
if (lean_obj_tag(v_a_672_) == 1)
{
lean_object* v_val_676_; lean_object* v_value_677_; uint8_t v___x_678_; lean_object* v___x_679_; 
lean_del_object(v___x_674_);
v_val_676_ = lean_ctor_get(v_a_672_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v_a_672_, 1);
v_value_677_ = lean_ctor_get(v_val_676_, 3);
lean_inc(v_value_677_);
lean_dec(v_val_676_);
v___x_678_ = 0;
v___x_679_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_678_, v_value_677_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_);
return v___x_679_;
}
else
{
uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
lean_dec(v_a_672_);
v___x_680_ = 0;
v___x_681_ = lean_box(v___x_680_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_681_);
v___x_683_ = v___x_674_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
v_a_686_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_671_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_671_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object* v_fvarId_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___x_702_; lean_object* v_fvarDecisionCache_703_; lean_object* v___x_704_; 
v___x_702_ = lean_st_ref_get(v_a_696_);
v_fvarDecisionCache_703_ = lean_ctor_get(v___x_702_, 1);
lean_inc_ref(v_fvarDecisionCache_703_);
lean_dec(v___x_702_);
v___x_704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_fvarDecisionCache_703_, v_fvarId_694_);
lean_dec_ref(v_fvarDecisionCache_703_);
if (lean_obj_tag(v___x_704_) == 1)
{
lean_object* v_val_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_fvarId_694_);
v_val_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_val_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set_tag(v___x_707_, 0);
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_val_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
else
{
lean_object* v___x_713_; 
lean_dec(v___x_704_);
v___x_713_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_798_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_798_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_798_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_798_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v_decls_719_; lean_object* v_fvarDecisionCache_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_797_; 
v___x_718_ = lean_st_ref_take(v_a_696_);
v_decls_719_ = lean_ctor_get(v___x_718_, 0);
v_fvarDecisionCache_720_ = lean_ctor_get(v___x_718_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_797_ == 0)
{
v___x_722_ = v___x_718_;
v_isShared_723_ = v_isSharedCheck_797_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_fvarDecisionCache_720_);
lean_inc(v_decls_719_);
lean_dec(v___x_718_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_797_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___y_725_; lean_object* v___y_734_; lean_object* v_i_735_; lean_object* v___y_751_; lean_object* v_i_752_; lean_object* v___y_758_; lean_object* v___x_767_; 
v___x_767_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_fvarDecisionCache_720_, v_fvarId_694_);
switch(lean_obj_tag(v___x_767_))
{
case 0:
{
lean_object* v_index_768_; lean_object* v_size_769_; lean_object* v___x_770_; 
v_index_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_index_768_);
lean_dec_ref_known(v___x_767_, 3);
v_size_769_ = lean_ctor_get(v_fvarDecisionCache_720_, 0);
lean_inc(v_size_769_);
lean_inc(v_a_714_);
v___x_770_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fvarDecisionCache_720_, v_size_769_, v_index_768_, v_fvarId_694_, v_a_714_);
lean_dec(v_index_768_);
v___y_725_ = v___x_770_;
goto v___jp_724_;
}
case 1:
{
lean_object* v_index_771_; lean_object* v_size_772_; lean_object* v_keyArray_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_index_771_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_index_771_);
lean_dec_ref_known(v___x_767_, 1);
v_size_772_ = lean_ctor_get(v_fvarDecisionCache_720_, 0);
v_keyArray_773_ = lean_ctor_get(v_fvarDecisionCache_720_, 1);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_nat_add(v_size_772_, v___x_774_);
v___x_776_ = lean_array_get_size(v_keyArray_773_);
v___x_777_ = lean_nat_dec_lt(v___x_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_dec(v___x_775_);
lean_dec(v_index_771_);
goto v___jp_740_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_778_ = lean_unsigned_to_nat(4u);
v___x_779_ = lean_nat_mul(v___x_775_, v___x_778_);
v___x_780_ = lean_unsigned_to_nat(3u);
v___x_781_ = lean_nat_mul(v___x_776_, v___x_780_);
v___x_782_ = lean_nat_dec_le(v___x_779_, v___x_781_);
lean_dec(v___x_781_);
lean_dec(v___x_779_);
if (v___x_782_ == 0)
{
lean_dec(v___x_775_);
lean_dec(v_index_771_);
goto v___jp_740_;
}
else
{
lean_object* v___x_783_; 
lean_inc(v_a_714_);
v___x_783_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fvarDecisionCache_720_, v___x_775_, v_index_771_, v_fvarId_694_, v_a_714_);
lean_dec(v_index_771_);
v___y_725_ = v___x_783_;
goto v___jp_724_;
}
}
}
default: 
{
lean_object* v_size_784_; lean_object* v_keyArray_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_size_784_ = lean_ctor_get(v_fvarDecisionCache_720_, 0);
v_keyArray_785_ = lean_ctor_get(v_fvarDecisionCache_720_, 1);
v___x_786_ = lean_unsigned_to_nat(1u);
v___x_787_ = lean_nat_add(v_size_784_, v___x_786_);
v___x_788_ = lean_array_get_size(v_keyArray_785_);
v___x_789_ = lean_nat_dec_lt(v___x_787_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec(v___x_787_);
v___x_790_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___redArg(v_fvarDecisionCache_720_);
lean_dec_ref(v_fvarDecisionCache_720_);
v___y_758_ = v___x_790_;
goto v___jp_757_;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_791_ = lean_unsigned_to_nat(4u);
v___x_792_ = lean_nat_mul(v___x_787_, v___x_791_);
lean_dec(v___x_787_);
v___x_793_ = lean_unsigned_to_nat(3u);
v___x_794_ = lean_nat_mul(v___x_788_, v___x_793_);
v___x_795_ = lean_nat_dec_le(v___x_792_, v___x_794_);
lean_dec(v___x_794_);
lean_dec(v___x_792_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___redArg(v_fvarDecisionCache_720_);
lean_dec_ref(v_fvarDecisionCache_720_);
v___y_758_ = v___x_796_;
goto v___jp_757_;
}
else
{
v___y_758_ = v_fvarDecisionCache_720_;
goto v___jp_757_;
}
}
}
}
v___jp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 1, v___y_725_);
v___x_727_ = v___x_722_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_decls_719_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___y_725_);
v___x_727_ = v_reuseFailAlloc_732_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = lean_st_ref_put(v_a_696_, v___x_727_);
if (v_isShared_717_ == 0)
{
v___x_730_ = v___x_716_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_714_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
v___jp_733_:
{
lean_object* v_size_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_size_736_ = lean_ctor_get(v___y_734_, 0);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_size_736_, v___x_737_);
lean_inc(v_a_714_);
v___x_739_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_734_, v___x_738_, v_i_735_, v_fvarId_694_, v_a_714_);
lean_dec(v_i_735_);
v___y_725_ = v___x_739_;
goto v___jp_724_;
}
v___jp_740_:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___redArg(v_fvarDecisionCache_720_);
lean_dec_ref(v_fvarDecisionCache_720_);
v___x_742_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v___x_741_, v_fvarId_694_);
switch(lean_obj_tag(v___x_742_))
{
case 0:
{
lean_object* v_index_743_; lean_object* v_size_744_; lean_object* v___x_745_; 
v_index_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_index_743_);
lean_dec_ref_known(v___x_742_, 3);
v_size_744_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_size_744_);
lean_inc(v_a_714_);
v___x_745_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_741_, v_size_744_, v_index_743_, v_fvarId_694_, v_a_714_);
lean_dec(v_index_743_);
v___y_725_ = v___x_745_;
goto v___jp_724_;
}
case 1:
{
lean_object* v_index_746_; 
v_index_746_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_index_746_);
lean_dec_ref_known(v___x_742_, 1);
v___y_734_ = v___x_741_;
v_i_735_ = v_index_746_;
goto v___jp_733_;
}
default: 
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_741_, v___x_747_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_index_749_; 
v_index_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_index_749_);
lean_dec_ref_known(v___x_748_, 1);
v___y_734_ = v___x_741_;
v_i_735_ = v_index_749_;
goto v___jp_733_;
}
else
{
lean_dec(v_fvarId_694_);
v___y_725_ = v___x_741_;
goto v___jp_724_;
}
}
}
}
v___jp_750_:
{
lean_object* v_size_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_size_753_ = lean_ctor_get(v___y_751_, 0);
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_size_753_, v___x_754_);
lean_inc(v_a_714_);
v___x_756_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_751_, v___x_755_, v_i_752_, v_fvarId_694_, v_a_714_);
lean_dec(v_i_752_);
v___y_725_ = v___x_756_;
goto v___jp_724_;
}
v___jp_757_:
{
lean_object* v___x_759_; 
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v___y_758_, v_fvarId_694_);
switch(lean_obj_tag(v___x_759_))
{
case 0:
{
lean_object* v_index_760_; lean_object* v_size_761_; lean_object* v___x_762_; 
v_index_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_index_760_);
lean_dec_ref_known(v___x_759_, 3);
v_size_761_ = lean_ctor_get(v___y_758_, 0);
lean_inc(v_size_761_);
lean_inc(v_a_714_);
v___x_762_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_758_, v_size_761_, v_index_760_, v_fvarId_694_, v_a_714_);
lean_dec(v_index_760_);
v___y_725_ = v___x_762_;
goto v___jp_724_;
}
case 1:
{
lean_object* v_index_763_; 
v_index_763_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_index_763_);
lean_dec_ref_known(v___x_759_, 1);
v___y_751_ = v___y_758_;
v_i_752_ = v_index_763_;
goto v___jp_750_;
}
default: 
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_758_, v___x_764_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_index_766_; 
v_index_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_index_766_);
lean_dec_ref_known(v___x_765_, 1);
v___y_751_ = v___y_758_;
v_i_752_ = v_index_766_;
goto v___jp_750_;
}
else
{
lean_dec(v_fvarId_694_);
v___y_725_ = v___y_758_;
goto v___jp_724_;
}
}
}
}
}
}
}
else
{
lean_dec(v_fvarId_694_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object* v_arg_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
if (lean_obj_tag(v_arg_799_) == 1)
{
lean_object* v_fvarId_807_; lean_object* v___x_808_; 
v_fvarId_807_ = lean_ctor_get(v_arg_799_, 0);
lean_inc(v_fvarId_807_);
lean_dec_ref_known(v_arg_799_, 1);
v___x_808_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_807_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_808_;
}
else
{
uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v_arg_799_);
v___x_809_ = 1;
v___x_810_ = lean_box(v___x_809_);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object* v_arg_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v_arg_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(lean_object* v_fvarId_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_fvarId_821_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object* v___x_830_, lean_object* v_as_831_, lean_object* v_i_832_, lean_object* v_stop_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
uint8_t v___x_20485__boxed_841_; size_t v_i_boxed_842_; size_t v_stop_boxed_843_; lean_object* v_res_844_; 
v___x_20485__boxed_841_ = lean_unbox(v___x_830_);
v_i_boxed_842_ = lean_unbox_usize(v_i_832_);
lean_dec(v_i_832_);
v_stop_boxed_843_ = lean_unbox_usize(v_stop_833_);
lean_dec(v_stop_833_);
v_res_844_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___x_20485__boxed_841_, v_as_831_, v_i_boxed_842_, v_stop_boxed_843_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec_ref(v_as_831_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(lean_object* v_as_845_, lean_object* v_i_846_, lean_object* v_stop_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
size_t v_i_boxed_855_; size_t v_stop_boxed_856_; lean_object* v_res_857_; 
v_i_boxed_855_ = lean_unbox_usize(v_i_846_);
lean_dec(v_i_846_);
v_stop_boxed_856_ = lean_unbox_usize(v_stop_847_);
lean_dec(v_stop_847_);
v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_as_845_, v_i_boxed_855_, v_stop_boxed_856_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec_ref(v_as_845_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object* v_fvarId_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object* v_isRoot_867_, lean_object* v_v_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
uint8_t v_isRoot_boxed_876_; lean_object* v_res_877_; 
v_isRoot_boxed_876_ = lean_unbox(v_isRoot_867_);
v_res_877_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v_isRoot_boxed_876_, v_v_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object* v_00_u03b2_878_, lean_object* v_m_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_879_, v_a_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___boxed(lean_object* v_00_u03b2_882_, lean_object* v_m_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(v_00_u03b2_882_, v_m_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_m_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(lean_object* v_00_u03b2_886_, lean_object* v_m_887_, lean_object* v_query_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_m_887_, v_query_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___boxed(lean_object* v_00_u03b2_890_, lean_object* v_m_891_, lean_object* v_query_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(v_00_u03b2_890_, v_m_891_, v_query_892_);
lean_dec(v_query_892_);
lean_dec_ref(v_m_891_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8(lean_object* v_00_u03b2_894_, lean_object* v_m_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___redArg(v_m_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8___boxed(lean_object* v_00_u03b2_897_, lean_object* v_m_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8(v_00_u03b2_897_, v_m_898_);
lean_dec_ref(v_m_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(lean_object* v_00_u03b2_900_, lean_object* v_m_901_, lean_object* v_query_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_m_901_, v_query_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___boxed(lean_object* v_00_u03b2_904_, lean_object* v_m_905_, lean_object* v_query_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(v_00_u03b2_904_, v_m_905_, v_query_906_);
lean_dec(v_query_906_);
lean_dec_ref(v_m_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(lean_object* v_00_u03b2_908_, lean_object* v_m_909_, lean_object* v_query_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_m_909_, v_query_910_, v_x_911_, v_x_912_, v_x_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___boxed(lean_object* v_00_u03b2_916_, lean_object* v_m_917_, lean_object* v_query_918_, lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(v_00_u03b2_916_, v_m_917_, v_query_918_, v_x_919_, v_x_920_, v_x_921_, v_x_922_);
lean_dec(v_query_918_);
lean_dec_ref(v_m_917_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11(lean_object* v_00_u03b2_924_, lean_object* v_init_925_, lean_object* v_b_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11___redArg(v_init_925_, v_b_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11___boxed(lean_object* v_00_u03b2_928_, lean_object* v_init_929_, lean_object* v_b_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11(v_00_u03b2_928_, v_init_929_, v_b_930_);
lean_dec_ref(v_b_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_932_, lean_object* v_b_933_, lean_object* v_acc_934_, lean_object* v_i_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12___redArg(v_b_933_, v_acc_934_, v_i_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12___boxed(lean_object* v_00_u03b2_937_, lean_object* v_b_938_, lean_object* v_acc_939_, lean_object* v_i_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__8_spec__11_spec__12(v_00_u03b2_937_, v_b_938_, v_acc_939_, v_i_940_);
lean_dec_ref(v_b_938_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(lean_object* v_prevArrayId_947_, lean_object* v_decl_948_, lean_object* v_k_949_, lean_object* v_illegalSet_950_, lean_object* v_size_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_decl_963_; lean_object* v_k_964_; lean_object* v_illegalSet_965_; lean_object* v_zero_973_; uint8_t v_isZero_974_; 
v_zero_973_ = lean_unsigned_to_nat(0u);
v_isZero_974_ = lean_nat_dec_eq(v_size_951_, v_zero_973_);
if (v_isZero_974_ == 1)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
lean_dec(v_prevArrayId_947_);
v___x_975_ = lean_box(0);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
else
{
lean_object* v_value_977_; 
v_value_977_ = lean_ctor_get(v_decl_948_, 3);
if (lean_obj_tag(v_value_977_) == 3)
{
lean_object* v_declName_978_; 
v_declName_978_ = lean_ctor_get(v_value_977_, 0);
if (lean_obj_tag(v_declName_978_) == 1)
{
lean_object* v_pre_979_; 
v_pre_979_ = lean_ctor_get(v_declName_978_, 0);
if (lean_obj_tag(v_pre_979_) == 1)
{
lean_object* v_pre_980_; 
v_pre_980_ = lean_ctor_get(v_pre_979_, 0);
if (lean_obj_tag(v_pre_980_) == 0)
{
lean_object* v_fvarId_981_; lean_object* v_args_982_; lean_object* v_str_983_; lean_object* v_str_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_fvarId_981_ = lean_ctor_get(v_decl_948_, 0);
v_args_982_ = lean_ctor_get(v_value_977_, 2);
v_str_983_ = lean_ctor_get(v_declName_978_, 1);
v_str_984_ = lean_ctor_get(v_pre_979_, 1);
v___x_985_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_986_ = lean_string_dec_eq(v_str_984_, v___x_985_);
if (v___x_986_ == 0)
{
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
lean_dec(v_prevArrayId_947_);
goto v___jp_959_;
}
else
{
lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_988_ = lean_string_dec_eq(v_str_983_, v___x_987_);
if (v___x_988_ == 0)
{
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
lean_dec(v_prevArrayId_947_);
goto v___jp_959_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_989_ = lean_array_get_size(v_args_982_);
v___x_990_ = lean_unsigned_to_nat(3u);
v___x_991_ = lean_nat_dec_eq(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
lean_dec(v_prevArrayId_947_);
goto v___jp_959_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_unsigned_to_nat(1u);
v___x_993_ = lean_array_fget(v_args_982_, v___x_992_);
if (lean_obj_tag(v___x_993_) == 1)
{
lean_object* v_fvarId_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1111_; 
v_fvarId_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1111_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_fvarId_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1111_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___x_998_; 
v___x_998_ = l_Lean_instBEqFVarId_beq(v_fvarId_994_, v_prevArrayId_947_);
lean_dec(v_prevArrayId_947_);
lean_dec(v_fvarId_994_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
v___x_999_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 0);
lean_ctor_set(v___x_996_, 0, v___x_999_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_del_object(v___x_996_);
v___x_1003_ = lean_unsigned_to_nat(2u);
v___x_1004_ = lean_array_fget_borrowed(v_args_982_, v___x_1003_);
lean_inc(v___x_1004_);
v___x_1005_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_1004_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1102_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1102_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1102_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_unbox(v_a_1006_);
lean_dec(v_a_1006_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
v___x_1011_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1011_);
v___x_1013_ = v___x_1008_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
else
{
lean_object* v_n_1015_; uint8_t v___x_1016_; 
v_n_1015_ = lean_nat_sub(v_size_951_, v___x_992_);
lean_dec(v_size_951_);
v___x_1016_ = lean_nat_dec_eq(v_n_1015_, v_zero_973_);
if (v___x_1016_ == 0)
{
lean_inc(v_fvarId_981_);
lean_dec_ref(v_decl_948_);
if (lean_obj_tag(v_k_949_) == 0)
{
lean_object* v_decl_1017_; lean_object* v_k_1018_; lean_object* v___x_1019_; 
lean_del_object(v___x_1008_);
v_decl_1017_ = lean_ctor_get(v_k_949_, 0);
lean_inc_ref(v_decl_1017_);
v_k_1018_ = lean_ctor_get(v_k_949_, 1);
lean_inc_ref(v_k_1018_);
lean_dec_ref_known(v_k_949_, 2);
lean_inc(v_fvarId_981_);
v___x_1019_ = l_Lean_FVarIdSet_insert(v_illegalSet_950_, v_fvarId_981_);
v_prevArrayId_947_ = v_fvarId_981_;
v_decl_948_ = v_decl_1017_;
v_k_949_ = v_k_1018_;
v_illegalSet_950_ = v___x_1019_;
v_size_951_ = v_n_1015_;
goto _start;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
lean_dec(v_n_1015_);
lean_dec(v_fvarId_981_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
v___x_1021_ = lean_box(0);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1021_);
v___x_1023_ = v___x_1008_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
else
{
lean_dec(v_n_1015_);
lean_del_object(v___x_1008_);
if (lean_obj_tag(v_k_949_) == 0)
{
lean_object* v_decl_1025_; lean_object* v_value_1026_; 
v_decl_1025_ = lean_ctor_get(v_k_949_, 0);
lean_inc_ref(v_decl_1025_);
v_value_1026_ = lean_ctor_get(v_decl_1025_, 3);
lean_inc(v_value_1026_);
if (lean_obj_tag(v_value_1026_) == 3)
{
lean_object* v_declName_1027_; 
v_declName_1027_ = lean_ctor_get(v_value_1026_, 0);
lean_inc(v_declName_1027_);
if (lean_obj_tag(v_declName_1027_) == 1)
{
lean_object* v_pre_1028_; 
v_pre_1028_ = lean_ctor_get(v_declName_1027_, 0);
lean_inc(v_pre_1028_);
if (lean_obj_tag(v_pre_1028_) == 1)
{
lean_object* v_pre_1029_; 
v_pre_1029_ = lean_ctor_get(v_pre_1028_, 0);
lean_inc(v_pre_1029_);
if (lean_obj_tag(v_pre_1029_) == 0)
{
lean_object* v_k_1030_; lean_object* v_fvarId_1031_; lean_object* v_binderName_1032_; lean_object* v_type_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1100_; 
v_k_1030_ = lean_ctor_get(v_k_949_, 1);
v_fvarId_1031_ = lean_ctor_get(v_decl_1025_, 0);
v_binderName_1032_ = lean_ctor_get(v_decl_1025_, 1);
v_type_1033_ = lean_ctor_get(v_decl_1025_, 2);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_decl_1025_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v_decl_1025_, 3);
lean_dec(v_unused_1101_);
v___x_1035_ = v_decl_1025_;
v_isShared_1036_ = v_isSharedCheck_1100_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_type_1033_);
lean_inc(v_binderName_1032_);
lean_inc(v_fvarId_1031_);
lean_dec(v_decl_1025_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1100_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_us_1037_; lean_object* v_args_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1098_; 
v_us_1037_ = lean_ctor_get(v_value_1026_, 1);
v_args_1038_ = lean_ctor_get(v_value_1026_, 2);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_value_1026_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v_value_1026_, 0);
lean_dec(v_unused_1099_);
v___x_1040_ = v_value_1026_;
v_isShared_1041_ = v_isSharedCheck_1098_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_args_1038_);
lean_inc(v_us_1037_);
lean_dec(v_value_1026_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1098_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_str_1042_; lean_object* v_str_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_str_1042_ = lean_ctor_get(v_declName_1027_, 1);
lean_inc_ref(v_str_1042_);
lean_dec_ref_known(v_declName_1027_, 2);
v_str_1043_ = lean_ctor_get(v_pre_1028_, 1);
lean_inc_ref(v_str_1043_);
lean_dec_ref_known(v_pre_1028_, 2);
v___x_1044_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2));
v___x_1045_ = lean_string_dec_eq(v_str_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3));
v___x_1047_ = lean_string_dec_eq(v_str_1043_, v___x_1046_);
lean_dec_ref(v_str_1043_);
if (v___x_1047_ == 0)
{
lean_dec_ref(v_str_1042_);
lean_del_object(v___x_1040_);
lean_dec_ref(v_args_1038_);
lean_dec(v_us_1037_);
lean_del_object(v___x_1035_);
lean_dec_ref(v_type_1033_);
lean_dec(v_binderName_1032_);
lean_dec(v_fvarId_1031_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_1049_ = lean_string_dec_eq(v_str_1042_, v___x_1048_);
lean_dec_ref(v_str_1042_);
if (v___x_1049_ == 0)
{
lean_del_object(v___x_1040_);
lean_dec_ref(v_args_1038_);
lean_dec(v_us_1037_);
lean_del_object(v___x_1035_);
lean_dec_ref(v_type_1033_);
lean_dec(v_binderName_1032_);
lean_dec(v_fvarId_1031_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_array_get_size(v_args_1038_);
v___x_1051_ = lean_nat_dec_eq(v___x_1050_, v___x_992_);
if (v___x_1051_ == 0)
{
lean_del_object(v___x_1040_);
lean_dec_ref(v_args_1038_);
lean_dec(v_us_1037_);
lean_del_object(v___x_1035_);
lean_dec_ref(v_type_1033_);
lean_dec(v_binderName_1032_);
lean_dec(v_fvarId_1031_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_array_fget(v_args_1038_, v_zero_973_);
lean_dec_ref(v_args_1038_);
if (lean_obj_tag(v___x_1052_) == 1)
{
lean_object* v_fvarId_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1072_; 
v_fvarId_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1072_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_fvarId_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1072_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
uint8_t v___x_1057_; 
v___x_1057_ = l_Lean_instBEqFVarId_beq(v_fvarId_1053_, v_fvarId_981_);
if (v___x_1057_ == 0)
{
lean_del_object(v___x_1055_);
lean_dec(v_fvarId_1053_);
lean_del_object(v___x_1040_);
lean_dec(v_us_1037_);
lean_del_object(v___x_1035_);
lean_dec_ref(v_type_1033_);
lean_dec(v_binderName_1032_);
lean_dec(v_fvarId_1031_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_inc_ref(v_k_1030_);
lean_inc(v_fvarId_981_);
lean_dec_ref_known(v_k_949_, 2);
lean_dec_ref(v_decl_948_);
v___x_1058_ = l_Lean_Name_str___override(v_pre_1029_, v___x_1046_);
v___x_1059_ = l_Lean_Name_str___override(v___x_1058_, v___x_1048_);
if (v_isShared_1056_ == 0)
{
v___x_1061_ = v___x_1055_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_fvarId_1053_);
v___x_1061_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1062_ = lean_mk_empty_array_with_capacity(v___x_992_);
v___x_1063_ = lean_array_push(v___x_1062_, v___x_1061_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 2, v___x_1063_);
lean_ctor_set(v___x_1040_, 0, v___x_1059_);
v___x_1065_ = v___x_1040_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_us_1037_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1067_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 3, v___x_1065_);
v___x_1067_ = v___x_1035_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_fvarId_1031_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_binderName_1032_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_type_1033_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_FVarIdSet_insert(v_illegalSet_950_, v_fvarId_981_);
v_decl_963_ = v___x_1067_;
v_k_964_ = v_k_1030_;
v_illegalSet_965_ = v___x_1068_;
goto v___jp_962_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1052_);
lean_del_object(v___x_1040_);
lean_dec(v_us_1037_);
lean_del_object(v___x_1035_);
lean_dec_ref(v_type_1033_);
lean_dec(v_binderName_1032_);
lean_dec(v_fvarId_1031_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
}
}
}
}
else
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
lean_dec_ref(v_str_1043_);
v___x_1073_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_1074_ = lean_string_dec_eq(v_str_1042_, v___x_1073_);
lean_dec_ref(v_str_1042_);
if (v___x_1074_ == 0)
{
lean_del_object(v___x_1040_);
lean_dec_ref(v_args_1038_);
lean_dec(v_us_1037_);
lean_del_object(v___x_1035_);
lean_dec_ref(v_type_1033_);
lean_dec(v_binderName_1032_);
lean_dec(v_fvarId_1031_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = lean_array_get_size(v_args_1038_);
v___x_1076_ = lean_nat_dec_eq(v___x_1075_, v___x_992_);
if (v___x_1076_ == 0)
{
lean_del_object(v___x_1040_);
lean_dec_ref(v_args_1038_);
lean_dec(v_us_1037_);
lean_del_object(v___x_1035_);
lean_dec_ref(v_type_1033_);
lean_dec(v_binderName_1032_);
lean_dec(v_fvarId_1031_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_array_fget(v_args_1038_, v_zero_973_);
lean_dec_ref(v_args_1038_);
if (lean_obj_tag(v___x_1077_) == 1)
{
lean_object* v_fvarId_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1097_; 
v_fvarId_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1097_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_fvarId_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1097_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
uint8_t v___x_1082_; 
v___x_1082_ = l_Lean_instBEqFVarId_beq(v_fvarId_1078_, v_fvarId_981_);
if (v___x_1082_ == 0)
{
lean_del_object(v___x_1080_);
lean_dec(v_fvarId_1078_);
lean_del_object(v___x_1040_);
lean_dec(v_us_1037_);
lean_del_object(v___x_1035_);
lean_dec_ref(v_type_1033_);
lean_dec(v_binderName_1032_);
lean_dec(v_fvarId_1031_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_inc_ref(v_k_1030_);
lean_inc(v_fvarId_981_);
lean_dec_ref_known(v_k_949_, 2);
lean_dec_ref(v_decl_948_);
v___x_1083_ = l_Lean_Name_str___override(v_pre_1029_, v___x_1044_);
v___x_1084_ = l_Lean_Name_str___override(v___x_1083_, v___x_1073_);
if (v_isShared_1081_ == 0)
{
v___x_1086_ = v___x_1080_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_fvarId_1078_);
v___x_1086_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1087_ = lean_mk_empty_array_with_capacity(v___x_992_);
v___x_1088_ = lean_array_push(v___x_1087_, v___x_1086_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 2, v___x_1088_);
lean_ctor_set(v___x_1040_, 0, v___x_1084_);
v___x_1090_ = v___x_1040_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_us_1037_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1092_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 3, v___x_1090_);
v___x_1092_ = v___x_1035_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_fvarId_1031_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_binderName_1032_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_type_1033_);
lean_ctor_set(v_reuseFailAlloc_1094_, 3, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_FVarIdSet_insert(v_illegalSet_950_, v_fvarId_981_);
v_decl_963_ = v___x_1092_;
v_k_964_ = v_k_1030_;
v_illegalSet_965_ = v___x_1093_;
goto v___jp_962_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1077_);
lean_del_object(v___x_1040_);
lean_dec(v_us_1037_);
lean_del_object(v___x_1035_);
lean_dec_ref(v_type_1033_);
lean_dec(v_binderName_1032_);
lean_dec(v_fvarId_1031_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1028_, 2);
lean_dec(v_pre_1029_);
lean_dec_ref_known(v_declName_1027_, 2);
lean_dec_ref_known(v_value_1026_, 3);
lean_dec_ref(v_decl_1025_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
}
else
{
lean_dec_ref_known(v_declName_1027_, 2);
lean_dec(v_pre_1028_);
lean_dec_ref_known(v_value_1026_, 3);
lean_dec_ref(v_decl_1025_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
}
else
{
lean_dec(v_declName_1027_);
lean_dec_ref_known(v_value_1026_, 3);
lean_dec_ref(v_decl_1025_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
}
else
{
lean_dec(v_value_1026_);
lean_dec_ref(v_decl_1025_);
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
}
else
{
v_decl_963_ = v_decl_948_;
v_k_964_ = v_k_949_;
v_illegalSet_965_ = v_illegalSet_950_;
goto v___jp_962_;
}
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
v_a_1103_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1005_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1005_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
else
{
lean_dec(v___x_993_);
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
lean_dec(v_prevArrayId_947_);
goto v___jp_959_;
}
}
}
}
}
else
{
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
lean_dec(v_prevArrayId_947_);
goto v___jp_959_;
}
}
else
{
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
lean_dec(v_prevArrayId_947_);
goto v___jp_959_;
}
}
else
{
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
lean_dec(v_prevArrayId_947_);
goto v___jp_959_;
}
}
else
{
lean_dec(v_size_951_);
lean_dec(v_illegalSet_950_);
lean_dec_ref(v_k_949_);
lean_dec_ref(v_decl_948_);
lean_dec(v_prevArrayId_947_);
goto v___jp_959_;
}
}
v___jp_959_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_box(0);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
v___jp_962_:
{
uint8_t v___x_966_; uint8_t v___x_967_; 
v___x_966_ = 0;
v___x_967_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_966_, v_k_964_, v_illegalSet_965_);
lean_dec(v_illegalSet_965_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_decl_963_);
lean_ctor_set(v___x_968_, 1, v_k_964_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec_ref(v_k_964_);
lean_dec_ref(v_decl_963_);
v___x_971_ = lean_box(0);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___boxed(lean_object* v_prevArrayId_1112_, lean_object* v_decl_1113_, lean_object* v_k_1114_, lean_object* v_illegalSet_1115_, lean_object* v_size_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_prevArrayId_1112_, v_decl_1113_, v_k_1114_, v_illegalSet_1115_, v_size_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(lean_object* v_decl_1127_, lean_object* v_k_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_value_1145_; 
v_value_1145_ = lean_ctor_get(v_decl_1127_, 3);
if (lean_obj_tag(v_value_1145_) == 3)
{
lean_object* v_declName_1146_; 
v_declName_1146_ = lean_ctor_get(v_value_1145_, 0);
if (lean_obj_tag(v_declName_1146_) == 1)
{
lean_object* v_pre_1147_; 
v_pre_1147_ = lean_ctor_get(v_declName_1146_, 0);
if (lean_obj_tag(v_pre_1147_) == 1)
{
lean_object* v_pre_1148_; 
v_pre_1148_ = lean_ctor_get(v_pre_1147_, 0);
if (lean_obj_tag(v_pre_1148_) == 0)
{
lean_object* v_args_1149_; lean_object* v_str_1150_; lean_object* v_str_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_args_1149_ = lean_ctor_get(v_value_1145_, 2);
v_str_1150_ = lean_ctor_get(v_declName_1146_, 1);
v_str_1151_ = lean_ctor_get(v_pre_1147_, 1);
v___x_1152_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1153_ = lean_string_dec_eq(v_str_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1142_;
}
else
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_1155_ = lean_string_dec_eq(v_str_1150_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1142_;
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = lean_array_get_size(v_args_1149_);
v___x_1157_ = lean_unsigned_to_nat(3u);
v___x_1158_ = lean_nat_dec_eq(v___x_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1142_;
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_unsigned_to_nat(1u);
v___x_1160_ = lean_array_fget_borrowed(v_args_1149_, v___x_1159_);
if (lean_obj_tag(v___x_1160_) == 1)
{
lean_object* v_fvarId_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; 
v_fvarId_1161_ = lean_ctor_get(v___x_1160_, 0);
v___x_1162_ = 0;
v___x_1163_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_1162_, v_fvarId_1161_, v_a_1132_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1219_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1219_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1219_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
if (lean_obj_tag(v_a_1164_) == 1)
{
lean_object* v_val_1168_; lean_object* v_value_1169_; 
lean_del_object(v___x_1166_);
v_val_1168_ = lean_ctor_get(v_a_1164_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v_a_1164_, 1);
v_value_1169_ = lean_ctor_get(v_val_1168_, 3);
lean_inc(v_value_1169_);
if (lean_obj_tag(v_value_1169_) == 3)
{
lean_object* v_declName_1170_; 
v_declName_1170_ = lean_ctor_get(v_value_1169_, 0);
lean_inc(v_declName_1170_);
if (lean_obj_tag(v_declName_1170_) == 1)
{
lean_object* v_pre_1171_; 
v_pre_1171_ = lean_ctor_get(v_declName_1170_, 0);
lean_inc(v_pre_1171_);
if (lean_obj_tag(v_pre_1171_) == 1)
{
lean_object* v_pre_1172_; 
v_pre_1172_ = lean_ctor_get(v_pre_1171_, 0);
if (lean_obj_tag(v_pre_1172_) == 0)
{
lean_object* v_fvarId_1173_; lean_object* v_args_1174_; lean_object* v_str_1175_; lean_object* v_str_1176_; uint8_t v___x_1177_; 
v_fvarId_1173_ = lean_ctor_get(v_val_1168_, 0);
lean_inc(v_fvarId_1173_);
lean_dec(v_val_1168_);
v_args_1174_ = lean_ctor_get(v_value_1169_, 2);
lean_inc_ref(v_args_1174_);
lean_dec_ref_known(v_value_1169_, 3);
v_str_1175_ = lean_ctor_get(v_declName_1170_, 1);
lean_inc_ref(v_str_1175_);
lean_dec_ref_known(v_declName_1170_, 2);
v_str_1176_ = lean_ctor_get(v_pre_1171_, 1);
lean_inc_ref(v_str_1176_);
lean_dec_ref_known(v_pre_1171_, 2);
v___x_1177_ = lean_string_dec_eq(v_str_1176_, v___x_1152_);
lean_dec_ref(v_str_1176_);
if (v___x_1177_ == 0)
{
lean_dec_ref(v_str_1175_);
lean_dec_ref(v_args_1174_);
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1139_;
}
else
{
lean_object* v___x_1178_; lean_object* v_sizeFVar_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1178_ = lean_box(1);
v___x_1201_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1202_ = lean_string_dec_eq(v_str_1175_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1204_ = lean_string_dec_eq(v_str_1175_, v___x_1203_);
lean_dec_ref(v_str_1175_);
if (v___x_1204_ == 0)
{
lean_dec_ref(v_args_1174_);
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1139_;
}
else
{
lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1205_ = lean_array_get_size(v_args_1174_);
v___x_1206_ = lean_unsigned_to_nat(2u);
v___x_1207_ = lean_nat_dec_eq(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_dec_ref(v_args_1174_);
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1139_;
}
else
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_array_fget(v_args_1174_, v___x_1159_);
lean_dec_ref(v_args_1174_);
if (lean_obj_tag(v___x_1208_) == 1)
{
lean_object* v_fvarId_1209_; 
v_fvarId_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_fvarId_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v_sizeFVar_1180_ = v_fvarId_1209_;
v___y_1181_ = v_a_1129_;
v___y_1182_ = v_a_1130_;
v___y_1183_ = v_a_1131_;
v___y_1184_ = v_a_1132_;
v___y_1185_ = v_a_1133_;
v___y_1186_ = v_a_1134_;
goto v___jp_1179_;
}
else
{
lean_dec(v___x_1208_);
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1139_;
}
}
}
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
lean_dec_ref(v_str_1175_);
v___x_1210_ = lean_array_get_size(v_args_1174_);
v___x_1211_ = lean_unsigned_to_nat(2u);
v___x_1212_ = lean_nat_dec_eq(v___x_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_dec_ref(v_args_1174_);
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1139_;
}
else
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_array_fget(v_args_1174_, v___x_1159_);
lean_dec_ref(v_args_1174_);
if (lean_obj_tag(v___x_1213_) == 1)
{
lean_object* v_fvarId_1214_; 
v_fvarId_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_fvarId_1214_);
lean_dec_ref_known(v___x_1213_, 1);
v_sizeFVar_1180_ = v_fvarId_1214_;
v___y_1181_ = v_a_1129_;
v___y_1182_ = v_a_1130_;
v___y_1183_ = v_a_1131_;
v___y_1184_ = v_a_1132_;
v___y_1185_ = v_a_1133_;
v___y_1186_ = v_a_1134_;
goto v___jp_1179_;
}
else
{
lean_dec(v___x_1213_);
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1139_;
}
}
}
v___jp_1179_:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1162_, v_sizeFVar_1180_, v___y_1184_);
lean_dec(v_sizeFVar_1180_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
if (lean_obj_tag(v_a_1188_) == 1)
{
lean_object* v_val_1189_; 
v_val_1189_ = lean_ctor_get(v_a_1188_, 0);
lean_inc(v_val_1189_);
lean_dec_ref_known(v_a_1188_, 1);
if (lean_obj_tag(v_val_1189_) == 0)
{
lean_object* v_value_1190_; 
v_value_1190_ = lean_ctor_get(v_val_1189_, 0);
lean_inc_ref(v_value_1190_);
lean_dec_ref_known(v_val_1189_, 1);
if (lean_obj_tag(v_value_1190_) == 0)
{
lean_object* v_val_1191_; lean_object* v___x_1192_; 
v_val_1191_ = lean_ctor_get(v_value_1190_, 0);
lean_inc(v_val_1191_);
lean_dec_ref_known(v_value_1190_, 1);
v___x_1192_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_fvarId_1173_, v_decl_1127_, v_k_1128_, v___x_1178_, v_val_1191_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1192_;
}
else
{
lean_dec_ref(v_value_1190_);
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1136_;
}
}
else
{
lean_dec(v_val_1189_);
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1136_;
}
}
else
{
lean_dec(v_a_1188_);
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1136_;
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_fvarId_1173_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
v_a_1193_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1187_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1187_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1171_, 2);
lean_dec_ref_known(v_declName_1170_, 2);
lean_dec_ref_known(v_value_1169_, 3);
lean_dec(v_val_1168_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1139_;
}
}
else
{
lean_dec_ref_known(v_declName_1170_, 2);
lean_dec(v_pre_1171_);
lean_dec_ref_known(v_value_1169_, 3);
lean_dec(v_val_1168_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1139_;
}
}
else
{
lean_dec(v_declName_1170_);
lean_dec_ref_known(v_value_1169_, 3);
lean_dec(v_val_1168_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1139_;
}
}
else
{
lean_dec(v_value_1169_);
lean_dec(v_val_1168_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1139_;
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_dec(v_a_1164_);
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
v___x_1215_ = lean_box(0);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1215_);
v___x_1217_ = v___x_1166_;
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
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
v_a_1220_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1163_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1163_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1142_;
}
}
}
}
}
else
{
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1142_;
}
}
else
{
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1142_;
}
}
else
{
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1142_;
}
}
else
{
lean_dec_ref(v_k_1128_);
lean_dec_ref(v_decl_1127_);
goto v___jp_1142_;
}
v___jp_1136_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
v___jp_1139_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
v___jp_1142_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_box(0);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___boxed(lean_object* v_decl_1228_, lean_object* v_k_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1228_, v_k_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
return v_res_1237_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1238_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(lean_object* v_env_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; lean_object* v_nextMacroScope_1247_; lean_object* v_ngen_1248_; lean_object* v_auxDeclNGen_1249_; lean_object* v_traceState_1250_; lean_object* v_messages_1251_; lean_object* v_infoState_1252_; lean_object* v_snapshotTasks_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1264_; 
v___x_1246_ = lean_st_ref_take(v___y_1244_);
v_nextMacroScope_1247_ = lean_ctor_get(v___x_1246_, 1);
v_ngen_1248_ = lean_ctor_get(v___x_1246_, 2);
v_auxDeclNGen_1249_ = lean_ctor_get(v___x_1246_, 3);
v_traceState_1250_ = lean_ctor_get(v___x_1246_, 4);
v_messages_1251_ = lean_ctor_get(v___x_1246_, 6);
v_infoState_1252_ = lean_ctor_get(v___x_1246_, 7);
v_snapshotTasks_1253_ = lean_ctor_get(v___x_1246_, 8);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; lean_object* v_unused_1266_; 
v_unused_1265_ = lean_ctor_get(v___x_1246_, 5);
lean_dec(v_unused_1265_);
v_unused_1266_ = lean_ctor_get(v___x_1246_, 0);
lean_dec(v_unused_1266_);
v___x_1255_ = v___x_1246_;
v_isShared_1256_ = v_isSharedCheck_1264_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_snapshotTasks_1253_);
lean_inc(v_infoState_1252_);
lean_inc(v_messages_1251_);
lean_inc(v_traceState_1250_);
lean_inc(v_auxDeclNGen_1249_);
lean_inc(v_ngen_1248_);
lean_inc(v_nextMacroScope_1247_);
lean_dec(v___x_1246_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1264_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 5, v___x_1257_);
lean_ctor_set(v___x_1255_, 0, v_env_1243_);
v___x_1259_ = v___x_1255_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_env_1243_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_nextMacroScope_1247_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_ngen_1248_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_auxDeclNGen_1249_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_traceState_1250_);
lean_ctor_set(v_reuseFailAlloc_1263_, 5, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1263_, 6, v_messages_1251_);
lean_ctor_set(v_reuseFailAlloc_1263_, 7, v_infoState_1252_);
lean_ctor_set(v_reuseFailAlloc_1263_, 8, v_snapshotTasks_1253_);
v___x_1259_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_st_ref_put(v___y_1244_, v___x_1259_);
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___boxed(lean_object* v_env_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1267_, v___y_1268_);
lean_dec(v___y_1268_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(lean_object* v_env_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1271_, v___y_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(lean_object* v_env_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_env_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(size_t v_sz_1289_, size_t v_i_1290_, lean_object* v_bs_1291_, uint8_t v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_usize_dec_lt(v_i_1290_, v_sz_1289_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1300_, 0, v_bs_1291_);
return v___x_1300_;
}
else
{
uint8_t v___x_1301_; lean_object* v_v_1302_; lean_object* v___x_1303_; 
v___x_1301_ = 0;
v_v_1302_ = lean_array_uget_borrowed(v_bs_1291_, v_i_1290_);
lean_inc(v_v_1302_);
v___x_1303_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_1301_, v_v_1302_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1305_; lean_object* v_bs_x27_1306_; size_t v___x_1307_; size_t v___x_1308_; lean_object* v___x_1309_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1305_ = lean_unsigned_to_nat(0u);
v_bs_x27_1306_ = lean_array_uset(v_bs_1291_, v_i_1290_, v___x_1305_);
v___x_1307_ = ((size_t)1ULL);
v___x_1308_ = lean_usize_add(v_i_1290_, v___x_1307_);
v___x_1309_ = lean_array_uset(v_bs_x27_1306_, v_i_1290_, v_a_1304_);
v_i_1290_ = v___x_1308_;
v_bs_1291_ = v___x_1309_;
goto _start;
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v_bs_1291_);
v_a_1311_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1303_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1303_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(lean_object* v_sz_1319_, lean_object* v_i_1320_, lean_object* v_bs_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
size_t v_sz_boxed_1329_; size_t v_i_boxed_1330_; uint8_t v___y_8198__boxed_1331_; lean_object* v_res_1332_; 
v_sz_boxed_1329_ = lean_unbox_usize(v_sz_1319_);
lean_dec(v_sz_1319_);
v_i_boxed_1330_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v___y_8198__boxed_1331_ = lean_unbox(v___y_1322_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_boxed_1329_, v_i_boxed_1330_, v_bs_1321_, v___y_8198__boxed_1331_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
return v_res_1332_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1(void){
_start:
{
lean_object* v_cellCount_1335_; lean_object* v___x_1336_; 
v_cellCount_1335_ = lean_unsigned_to_nat(16u);
v___x_1336_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1335_);
return v___x_1336_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2(void){
_start:
{
lean_object* v_cellCount_1337_; lean_object* v___x_1338_; 
v_cellCount_1337_ = lean_unsigned_to_nat(16u);
v___x_1338_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1339_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_1340_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1);
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v___x_1340_);
lean_ctor_set(v___x_1342_, 2, v___x_1339_);
return v___x_1342_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4(void){
_start:
{
uint8_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = 0;
v___x_1344_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(lean_object* v_decl_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_type_1363_; lean_object* v_value_1364_; lean_object* v___x_1365_; 
v___x_1361_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0));
v___x_1362_ = lean_st_mk_ref(v___x_1361_);
v_type_1363_ = lean_ctor_get(v_decl_1353_, 2);
lean_inc_ref(v_type_1363_);
v_value_1364_ = lean_ctor_get(v_decl_1353_, 3);
lean_inc(v_value_1364_);
v___x_1365_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_1364_, v___x_1362_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v_a_1376_; size_t v_sz_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
lean_dec_ref_known(v___x_1365_, 1);
v___x_1366_ = lean_st_ref_get(v___x_1362_);
lean_dec(v___x_1362_);
v___x_1367_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3);
v___x_1368_ = lean_st_mk_ref(v___x_1367_);
v___x_1369_ = 0;
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v_decl_1353_);
v___x_1371_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4);
v___x_1372_ = l_Array_reverse___redArg(v___x_1366_);
v___x_1373_ = lean_array_push(v___x_1372_, v___x_1370_);
v___x_1374_ = 0;
v_sz_1458_ = lean_array_size(v___x_1373_);
v___x_1459_ = ((size_t)0ULL);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_1458_, v___x_1459_, v___x_1373_, v___x_1374_, v___x_1368_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = lean_st_ref_get(v___x_1368_);
lean_dec(v___x_1368_);
lean_dec(v___x_1462_);
v_a_1376_ = v_a_1461_;
goto v___jp_1375_;
}
else
{
lean_dec(v___x_1368_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1463_; 
v_a_1463_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1460_, 1);
v_a_1376_ = v_a_1463_;
goto v___jp_1375_;
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v_type_1363_);
v_a_1464_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1460_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1460_);
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
v___jp_1375_:
{
lean_object* v___x_1377_; lean_object* v_env_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1377_ = lean_st_ref_get(v_a_1359_);
v_env_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc_ref_n(v_env_1378_, 2);
lean_dec(v___x_1377_);
v___x_1379_ = lean_array_get_size(v_a_1376_);
v___x_1380_ = lean_unsigned_to_nat(1u);
v___x_1381_ = lean_nat_sub(v___x_1379_, v___x_1380_);
v___x_1382_ = lean_array_get_borrowed(v___x_1371_, v_a_1376_, v___x_1381_);
lean_dec(v___x_1381_);
v___x_1383_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1382_);
v___x_1384_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
v___x_1385_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1369_, v_a_1376_, v___x_1384_);
lean_dec_ref(v_a_1376_);
v___x_1386_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5));
lean_inc_ref(v___x_1385_);
v___x_1387_ = l_Lean_Compiler_LCNF_Code_toExpr(v___x_1369_, v___x_1385_, v___x_1386_);
v___x_1388_ = l_Lean_getClosedTermName_x3f(v_env_1378_, v___x_1387_);
if (lean_obj_tag(v___x_1388_) == 1)
{
lean_object* v_val_1389_; lean_object* v___x_1390_; 
lean_dec_ref(v___x_1387_);
lean_dec_ref(v_env_1378_);
lean_dec_ref(v_type_1363_);
v_val_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_val_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1369_, v___x_1385_, v_a_1357_);
lean_dec_ref(v___x_1385_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1390_, 0);
lean_dec(v_unused_1398_);
v___x_1392_ = v___x_1390_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v___x_1390_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v_val_1389_);
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_val_1389_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec(v_val_1389_);
v_a_1399_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1390_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1390_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v___x_1407_; lean_object* v_baseName_1408_; lean_object* v_decls_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v___x_1388_);
v___x_1407_ = lean_st_ref_get(v_a_1355_);
v_baseName_1408_ = lean_ctor_get(v_a_1354_, 0);
v_decls_1409_ = lean_ctor_get(v___x_1407_, 0);
lean_inc_ref(v_decls_1409_);
lean_dec(v___x_1407_);
v___x_1410_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7));
v___x_1411_ = lean_array_get_size(v_decls_1409_);
lean_dec_ref(v_decls_1409_);
v___x_1412_ = lean_name_append_index_after(v___x_1410_, v___x_1411_);
lean_inc(v_baseName_1408_);
v___x_1413_ = l_Lean_Name_append(v_baseName_1408_, v___x_1412_);
lean_inc(v___x_1413_);
v___x_1414_ = l_Lean_cacheClosedTermName(v_env_1378_, v___x_1387_, v___x_1413_);
v___x_1415_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v___x_1414_, v_a_1359_);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v___x_1415_, 0);
lean_dec(v_unused_1457_);
v___x_1417_ = v___x_1415_;
v_isShared_1418_ = v_isSharedCheck_1456_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v___x_1415_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1456_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = 1;
lean_inc(v___x_1413_);
v___x_1421_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1421_, 0, v___x_1413_);
lean_ctor_set(v___x_1421_, 1, v___x_1419_);
lean_ctor_set(v___x_1421_, 2, v_type_1363_);
lean_ctor_set(v___x_1421_, 3, v___x_1386_);
lean_ctor_set_uint8(v___x_1421_, sizeof(void*)*4, v___x_1420_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1385_);
v___x_1423_ = v___x_1417_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1385_);
v___x_1423_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__8));
v___x_1425_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1425_, 0, v___x_1421_);
lean_ctor_set(v___x_1425_, 1, v___x_1423_);
lean_ctor_set(v___x_1425_, 2, v___x_1424_);
lean_ctor_set_uint8(v___x_1425_, sizeof(void*)*3, v___x_1374_);
lean_inc_ref(v___x_1425_);
v___x_1426_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1425_, v_a_1359_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1445_; 
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v___x_1426_, 0);
lean_dec(v_unused_1446_);
v___x_1428_ = v___x_1426_;
v_isShared_1429_ = v_isSharedCheck_1445_;
goto v_resetjp_1427_;
}
else
{
lean_dec(v___x_1426_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1445_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v_decls_1431_; lean_object* v_fvarDecisionCache_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1444_; 
v___x_1430_ = lean_st_ref_take(v_a_1355_);
v_decls_1431_ = lean_ctor_get(v___x_1430_, 0);
v_fvarDecisionCache_1432_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1434_ = v___x_1430_;
v_isShared_1435_ = v_isSharedCheck_1444_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_fvarDecisionCache_1432_);
lean_inc(v_decls_1431_);
lean_dec(v___x_1430_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1444_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_array_push(v_decls_1431_, v___x_1425_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_fvarDecisionCache_1432_);
v___x_1438_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_st_ref_put(v_a_1355_, v___x_1438_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1413_);
v___x_1441_ = v___x_1428_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1413_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref_known(v___x_1425_, 3);
lean_dec(v___x_1413_);
v_a_1447_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1426_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1426_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
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
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref(v_type_1363_);
lean_dec(v___x_1362_);
lean_dec_ref(v_decl_1353_);
v_a_1472_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1365_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1365_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___boxed(lean_object* v_decl_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
return v_res_1488_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0(void){
_start:
{
uint8_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = 0;
v___x_1490_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(lean_object* v_msg_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0);
v___x_1493_ = lean_panic_fn_borrowed(v___x_1492_, v_msg_1491_);
return v___x_1493_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1497_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2));
v___x_1498_ = lean_unsigned_to_nat(9u);
v___x_1499_ = lean_unsigned_to_nat(641u);
v___x_1500_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1));
v___x_1501_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0));
v___x_1502_ = l_mkPanicMessageWithDecl(v___x_1501_, v___x_1500_, v___x_1499_, v___x_1498_, v___x_1497_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* v_code_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v___y_1514_; lean_object* v___y_1515_; uint8_t v___y_1516_; lean_object* v___y_1521_; lean_object* v___y_1522_; uint8_t v___y_1523_; lean_object* v_decl_1528_; lean_object* v_k_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1582_; lean_object* v___y_1583_; uint8_t v___y_1584_; lean_object* v___y_1589_; lean_object* v___y_1590_; uint8_t v___y_1591_; lean_object* v___y_1596_; lean_object* v___y_1597_; uint8_t v___y_1598_; lean_object* v___y_1603_; lean_object* v___y_1604_; uint8_t v___y_1605_; lean_object* v___y_1610_; lean_object* v___y_1611_; uint8_t v___y_1612_; 
switch(lean_obj_tag(v_code_1505_))
{
case 0:
{
lean_object* v_decl_1616_; lean_object* v_k_1617_; lean_object* v___y_1619_; uint8_t v___y_1620_; lean_object* v___y_1633_; uint8_t v___y_1634_; lean_object* v___y_1647_; uint8_t v___y_1648_; lean_object* v_value_1660_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; 
v_decl_1616_ = lean_ctor_get(v_code_1505_, 0);
v_k_1617_ = lean_ctor_get(v_code_1505_, 1);
v_value_1660_ = lean_ctor_get(v_decl_1616_, 3);
lean_inc(v_value_1660_);
if (lean_obj_tag(v_value_1660_) == 3)
{
lean_object* v_declName_1764_; 
v_declName_1764_ = lean_ctor_get(v_value_1660_, 0);
if (lean_obj_tag(v_declName_1764_) == 1)
{
lean_object* v_pre_1765_; 
v_pre_1765_ = lean_ctor_get(v_declName_1764_, 0);
if (lean_obj_tag(v_pre_1765_) == 1)
{
lean_object* v_pre_1766_; 
v_pre_1766_ = lean_ctor_get(v_pre_1765_, 0);
if (lean_obj_tag(v_pre_1766_) == 0)
{
lean_object* v_args_1767_; lean_object* v_str_1768_; lean_object* v_str_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v_sizeId_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; 
v_args_1767_ = lean_ctor_get(v_value_1660_, 2);
v_str_1768_ = lean_ctor_get(v_declName_1764_, 1);
v_str_1769_ = lean_ctor_get(v_pre_1765_, 1);
v___x_1770_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1771_ = lean_string_dec_eq(v_str_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
v___y_1662_ = v_a_1506_;
v___y_1663_ = v_a_1507_;
v___y_1664_ = v_a_1508_;
v___y_1665_ = v_a_1509_;
v___y_1666_ = v_a_1510_;
v___y_1667_ = v_a_1511_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1955_ = lean_string_dec_eq(v_str_1768_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1957_ = lean_string_dec_eq(v_str_1768_, v___x_1956_);
if (v___x_1957_ == 0)
{
v___y_1662_ = v_a_1506_;
v___y_1663_ = v_a_1507_;
v___y_1664_ = v_a_1508_;
v___y_1665_ = v_a_1509_;
v___y_1666_ = v_a_1510_;
v___y_1667_ = v_a_1511_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = lean_array_get_size(v_args_1767_);
v___x_1959_ = lean_unsigned_to_nat(2u);
v___x_1960_ = lean_nat_dec_eq(v___x_1958_, v___x_1959_);
if (v___x_1960_ == 0)
{
v___y_1662_ = v_a_1506_;
v___y_1663_ = v_a_1507_;
v___y_1664_ = v_a_1508_;
v___y_1665_ = v_a_1509_;
v___y_1666_ = v_a_1510_;
v___y_1667_ = v_a_1511_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_array_fget_borrowed(v_args_1767_, v___x_1961_);
if (lean_obj_tag(v___x_1962_) == 1)
{
lean_object* v_fvarId_1963_; 
v_fvarId_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_fvarId_1963_);
v_sizeId_1884_ = v_fvarId_1963_;
v___y_1885_ = v_a_1506_;
v___y_1886_ = v_a_1507_;
v___y_1887_ = v_a_1508_;
v___y_1888_ = v_a_1509_;
v___y_1889_ = v_a_1510_;
v___y_1890_ = v_a_1511_;
goto v___jp_1883_;
}
else
{
v___y_1662_ = v_a_1506_;
v___y_1663_ = v_a_1507_;
v___y_1664_ = v_a_1508_;
v___y_1665_ = v_a_1509_;
v___y_1666_ = v_a_1510_;
v___y_1667_ = v_a_1511_;
goto v___jp_1661_;
}
}
}
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1964_ = lean_array_get_size(v_args_1767_);
v___x_1965_ = lean_unsigned_to_nat(2u);
v___x_1966_ = lean_nat_dec_eq(v___x_1964_, v___x_1965_);
if (v___x_1966_ == 0)
{
v___y_1662_ = v_a_1506_;
v___y_1663_ = v_a_1507_;
v___y_1664_ = v_a_1508_;
v___y_1665_ = v_a_1509_;
v___y_1666_ = v_a_1510_;
v___y_1667_ = v_a_1511_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_unsigned_to_nat(1u);
v___x_1968_ = lean_array_fget_borrowed(v_args_1767_, v___x_1967_);
if (lean_obj_tag(v___x_1968_) == 1)
{
lean_object* v_fvarId_1969_; 
v_fvarId_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_fvarId_1969_);
v_sizeId_1884_ = v_fvarId_1969_;
v___y_1885_ = v_a_1506_;
v___y_1886_ = v_a_1507_;
v___y_1887_ = v_a_1508_;
v___y_1888_ = v_a_1509_;
v___y_1889_ = v_a_1510_;
v___y_1890_ = v_a_1511_;
goto v___jp_1883_;
}
else
{
v___y_1662_ = v_a_1506_;
v___y_1663_ = v_a_1507_;
v___y_1664_ = v_a_1508_;
v___y_1665_ = v_a_1509_;
v___y_1666_ = v_a_1510_;
v___y_1667_ = v_a_1511_;
goto v___jp_1661_;
}
}
}
}
v___jp_1772_:
{
lean_object* v___x_1779_; 
lean_inc_ref(v_k_1617_);
lean_inc_ref(v_decl_1616_);
v___x_1779_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1616_, v_k_1617_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1779_, 1);
if (lean_obj_tag(v_a_1780_) == 1)
{
lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1821_; 
v_isSharedCheck_1821_ = !lean_is_exclusive(v_value_1660_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; lean_object* v_unused_1823_; lean_object* v_unused_1824_; 
v_unused_1822_ = lean_ctor_get(v_value_1660_, 2);
lean_dec(v_unused_1822_);
v_unused_1823_ = lean_ctor_get(v_value_1660_, 1);
lean_dec(v_unused_1823_);
v_unused_1824_ = lean_ctor_get(v_value_1660_, 0);
lean_dec(v_unused_1824_);
v___x_1782_ = v_value_1660_;
v_isShared_1783_ = v_isSharedCheck_1821_;
goto v_resetjp_1781_;
}
else
{
lean_dec(v_value_1660_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1821_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v_val_1784_; lean_object* v_fst_1785_; lean_object* v_snd_1786_; lean_object* v___x_1787_; 
v_val_1784_ = lean_ctor_get(v_a_1780_, 0);
lean_inc(v_val_1784_);
lean_dec_ref_known(v_a_1780_, 1);
v_fst_1785_ = lean_ctor_get(v_val_1784_, 0);
lean_inc_n(v_fst_1785_, 2);
v_snd_1786_ = lean_ctor_get(v_val_1784_, 1);
lean_inc(v_snd_1786_);
lean_dec(v_val_1784_);
v___x_1787_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1785_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v___x_1789_ = 0;
v___x_1790_ = lean_box(0);
v___x_1791_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 2, v___x_1791_);
lean_ctor_set(v___x_1782_, 1, v___x_1790_);
lean_ctor_set(v___x_1782_, 0, v_a_1788_);
v___x_1793_ = v___x_1782_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1788_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1812_, 2, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1789_, v_fst_1785_, v___x_1793_, v___y_1776_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1796_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___x_1796_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1786_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; size_t v___x_1798_; size_t v___x_1799_; uint8_t v___x_1800_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = lean_ptr_addr(v_k_1617_);
v___x_1799_ = lean_ptr_addr(v_a_1797_);
v___x_1800_ = lean_usize_dec_eq(v___x_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
v___y_1610_ = v_a_1795_;
v___y_1611_ = v_a_1797_;
v___y_1612_ = v___x_1800_;
goto v___jp_1609_;
}
else
{
size_t v___x_1801_; size_t v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = lean_ptr_addr(v_decl_1616_);
v___x_1802_ = lean_ptr_addr(v_a_1795_);
v___x_1803_ = lean_usize_dec_eq(v___x_1801_, v___x_1802_);
v___y_1610_ = v_a_1795_;
v___y_1611_ = v_a_1797_;
v___y_1612_ = v___x_1803_;
goto v___jp_1609_;
}
}
else
{
lean_dec(v_a_1795_);
lean_dec_ref_known(v_code_1505_, 2);
return v___x_1796_;
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v_snd_1786_);
lean_dec_ref_known(v_code_1505_, 2);
v_a_1804_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1794_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1794_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec(v_snd_1786_);
lean_dec(v_fst_1785_);
lean_del_object(v___x_1782_);
lean_dec_ref_known(v_code_1505_, 2);
v_a_1813_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1787_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1787_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
else
{
lean_object* v___x_1825_; 
lean_dec(v_a_1780_);
v___x_1825_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1771_, v_value_1660_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; uint8_t v___x_1827_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___x_1827_ = lean_unbox(v_a_1826_);
lean_dec(v_a_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; 
lean_inc_ref(v_k_1617_);
v___x_1828_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1617_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; size_t v___x_1830_; size_t v___x_1831_; uint8_t v___x_1832_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
v___x_1830_ = lean_ptr_addr(v_k_1617_);
v___x_1831_ = lean_ptr_addr(v_a_1829_);
v___x_1832_ = lean_usize_dec_eq(v___x_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
v___y_1647_ = v_a_1829_;
v___y_1648_ = v___x_1832_;
goto v___jp_1646_;
}
else
{
size_t v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_ptr_addr(v_decl_1616_);
v___x_1834_ = lean_usize_dec_eq(v___x_1833_, v___x_1833_);
v___y_1647_ = v_a_1829_;
v___y_1648_ = v___x_1834_;
goto v___jp_1646_;
}
}
else
{
lean_dec_ref_known(v_code_1505_, 2);
return v___x_1828_;
}
}
else
{
lean_object* v___x_1835_; 
lean_inc_ref(v_decl_1616_);
v___x_1835_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1616_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; uint8_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = 0;
v___x_1838_ = lean_box(0);
v___x_1839_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1840_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1840_, 0, v_a_1836_);
lean_ctor_set(v___x_1840_, 1, v___x_1838_);
lean_ctor_set(v___x_1840_, 2, v___x_1839_);
lean_inc_ref(v_decl_1616_);
v___x_1841_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1837_, v_decl_1616_, v___x_1840_, v___y_1776_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
lean_inc_ref(v_k_1617_);
v___x_1843_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1617_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; size_t v___x_1845_; size_t v___x_1846_; uint8_t v___x_1847_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = lean_ptr_addr(v_k_1617_);
v___x_1846_ = lean_ptr_addr(v_a_1844_);
v___x_1847_ = lean_usize_dec_eq(v___x_1845_, v___x_1846_);
if (v___x_1847_ == 0)
{
v___y_1603_ = v_a_1842_;
v___y_1604_ = v_a_1844_;
v___y_1605_ = v___x_1847_;
goto v___jp_1602_;
}
else
{
size_t v___x_1848_; size_t v___x_1849_; uint8_t v___x_1850_; 
v___x_1848_ = lean_ptr_addr(v_decl_1616_);
v___x_1849_ = lean_ptr_addr(v_a_1842_);
v___x_1850_ = lean_usize_dec_eq(v___x_1848_, v___x_1849_);
v___y_1603_ = v_a_1842_;
v___y_1604_ = v_a_1844_;
v___y_1605_ = v___x_1850_;
goto v___jp_1602_;
}
}
else
{
lean_dec(v_a_1842_);
lean_dec_ref_known(v_code_1505_, 2);
return v___x_1843_;
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref_known(v_code_1505_, 2);
v_a_1851_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1841_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1841_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
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
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref_known(v_code_1505_, 2);
v_a_1859_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1835_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1835_);
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
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec_ref_known(v_code_1505_, 2);
v_a_1867_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1825_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1825_);
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
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec_ref_known(v_value_1660_, 3);
lean_dec_ref_known(v_code_1505_, 2);
v_a_1875_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1779_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1779_);
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
v___jp_1883_:
{
uint8_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = 0;
v___x_1892_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1891_, v_sizeId_1884_, v___y_1888_);
lean_dec(v_sizeId_1884_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref_known(v___x_1892_, 1);
if (lean_obj_tag(v_a_1893_) == 1)
{
lean_object* v_val_1894_; 
v_val_1894_ = lean_ctor_get(v_a_1893_, 0);
lean_inc(v_val_1894_);
lean_dec_ref_known(v_a_1893_, 1);
if (lean_obj_tag(v_val_1894_) == 0)
{
lean_object* v_value_1895_; 
v_value_1895_ = lean_ctor_get(v_val_1894_, 0);
lean_inc_ref(v_value_1895_);
lean_dec_ref_known(v_val_1894_, 1);
if (lean_obj_tag(v_value_1895_) == 0)
{
lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1942_; 
v_isSharedCheck_1942_ = !lean_is_exclusive(v_value_1660_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; lean_object* v_unused_1944_; lean_object* v_unused_1945_; 
v_unused_1943_ = lean_ctor_get(v_value_1660_, 2);
lean_dec(v_unused_1943_);
v_unused_1944_ = lean_ctor_get(v_value_1660_, 1);
lean_dec(v_unused_1944_);
v_unused_1945_ = lean_ctor_get(v_value_1660_, 0);
lean_dec(v_unused_1945_);
v___x_1897_ = v_value_1660_;
v_isShared_1898_ = v_isSharedCheck_1942_;
goto v_resetjp_1896_;
}
else
{
lean_dec(v_value_1660_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1942_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_val_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v_val_1899_ = lean_ctor_get(v_value_1895_, 0);
lean_inc(v_val_1899_);
lean_dec_ref_known(v_value_1895_, 1);
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = lean_nat_dec_eq(v_val_1899_, v___x_1900_);
lean_dec(v_val_1899_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; 
lean_del_object(v___x_1897_);
lean_inc_ref(v_k_1617_);
v___x_1902_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1617_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; size_t v___x_1904_; size_t v___x_1905_; uint8_t v___x_1906_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = lean_ptr_addr(v_k_1617_);
v___x_1905_ = lean_ptr_addr(v_a_1903_);
v___x_1906_ = lean_usize_dec_eq(v___x_1904_, v___x_1905_);
if (v___x_1906_ == 0)
{
v___y_1633_ = v_a_1903_;
v___y_1634_ = v___x_1906_;
goto v___jp_1632_;
}
else
{
size_t v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = lean_ptr_addr(v_decl_1616_);
v___x_1908_ = lean_usize_dec_eq(v___x_1907_, v___x_1907_);
v___y_1633_ = v_a_1903_;
v___y_1634_ = v___x_1908_;
goto v___jp_1632_;
}
}
else
{
lean_dec_ref_known(v_code_1505_, 2);
return v___x_1902_;
}
}
else
{
lean_object* v___x_1909_; 
lean_inc_ref(v_decl_1616_);
v___x_1909_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1616_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1909_, 1);
v___x_1911_ = lean_box(0);
v___x_1912_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 2, v___x_1912_);
lean_ctor_set(v___x_1897_, 1, v___x_1911_);
lean_ctor_set(v___x_1897_, 0, v_a_1910_);
v___x_1914_ = v___x_1897_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1910_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; 
lean_inc_ref(v_decl_1616_);
v___x_1915_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1891_, v_decl_1616_, v___x_1914_, v___y_1888_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
lean_inc_ref(v_k_1617_);
v___x_1917_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1617_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; size_t v___x_1919_; size_t v___x_1920_; uint8_t v___x_1921_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = lean_ptr_addr(v_k_1617_);
v___x_1920_ = lean_ptr_addr(v_a_1918_);
v___x_1921_ = lean_usize_dec_eq(v___x_1919_, v___x_1920_);
if (v___x_1921_ == 0)
{
v___y_1596_ = v_a_1916_;
v___y_1597_ = v_a_1918_;
v___y_1598_ = v___x_1921_;
goto v___jp_1595_;
}
else
{
size_t v___x_1922_; size_t v___x_1923_; uint8_t v___x_1924_; 
v___x_1922_ = lean_ptr_addr(v_decl_1616_);
v___x_1923_ = lean_ptr_addr(v_a_1916_);
v___x_1924_ = lean_usize_dec_eq(v___x_1922_, v___x_1923_);
v___y_1596_ = v_a_1916_;
v___y_1597_ = v_a_1918_;
v___y_1598_ = v___x_1924_;
goto v___jp_1595_;
}
}
else
{
lean_dec(v_a_1916_);
lean_dec_ref_known(v_code_1505_, 2);
return v___x_1917_;
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec_ref_known(v_code_1505_, 2);
v_a_1925_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1915_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1915_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_del_object(v___x_1897_);
lean_dec_ref_known(v_code_1505_, 2);
v_a_1934_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1909_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1909_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_1895_);
v___y_1773_ = v___y_1885_;
v___y_1774_ = v___y_1886_;
v___y_1775_ = v___y_1887_;
v___y_1776_ = v___y_1888_;
v___y_1777_ = v___y_1889_;
v___y_1778_ = v___y_1890_;
goto v___jp_1772_;
}
}
else
{
lean_dec(v_val_1894_);
v___y_1773_ = v___y_1885_;
v___y_1774_ = v___y_1886_;
v___y_1775_ = v___y_1887_;
v___y_1776_ = v___y_1888_;
v___y_1777_ = v___y_1889_;
v___y_1778_ = v___y_1890_;
goto v___jp_1772_;
}
}
else
{
lean_dec(v_a_1893_);
v___y_1773_ = v___y_1885_;
v___y_1774_ = v___y_1886_;
v___y_1775_ = v___y_1887_;
v___y_1776_ = v___y_1888_;
v___y_1777_ = v___y_1889_;
v___y_1778_ = v___y_1890_;
goto v___jp_1772_;
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref_known(v_value_1660_, 3);
lean_dec_ref_known(v_code_1505_, 2);
v_a_1946_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1892_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1892_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
else
{
v___y_1662_ = v_a_1506_;
v___y_1663_ = v_a_1507_;
v___y_1664_ = v_a_1508_;
v___y_1665_ = v_a_1509_;
v___y_1666_ = v_a_1510_;
v___y_1667_ = v_a_1511_;
goto v___jp_1661_;
}
}
else
{
v___y_1662_ = v_a_1506_;
v___y_1663_ = v_a_1507_;
v___y_1664_ = v_a_1508_;
v___y_1665_ = v_a_1509_;
v___y_1666_ = v_a_1510_;
v___y_1667_ = v_a_1511_;
goto v___jp_1661_;
}
}
else
{
v___y_1662_ = v_a_1506_;
v___y_1663_ = v_a_1507_;
v___y_1664_ = v_a_1508_;
v___y_1665_ = v_a_1509_;
v___y_1666_ = v_a_1510_;
v___y_1667_ = v_a_1511_;
goto v___jp_1661_;
}
}
else
{
v___y_1662_ = v_a_1506_;
v___y_1663_ = v_a_1507_;
v___y_1664_ = v_a_1508_;
v___y_1665_ = v_a_1509_;
v___y_1666_ = v_a_1510_;
v___y_1667_ = v_a_1511_;
goto v___jp_1661_;
}
v___jp_1618_:
{
if (v___y_1620_ == 0)
{
lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1628_; 
lean_inc_ref(v_decl_1616_);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_code_1505_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; lean_object* v_unused_1630_; 
v_unused_1629_ = lean_ctor_get(v_code_1505_, 1);
lean_dec(v_unused_1629_);
v_unused_1630_ = lean_ctor_get(v_code_1505_, 0);
lean_dec(v_unused_1630_);
v___x_1622_ = v_code_1505_;
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v_code_1505_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1628_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v___y_1619_);
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_decl_1616_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v___y_1619_);
v___x_1625_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
return v___x_1626_;
}
}
}
else
{
lean_object* v___x_1631_; 
lean_dec_ref(v___y_1619_);
v___x_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1631_, 0, v_code_1505_);
return v___x_1631_;
}
}
v___jp_1632_:
{
if (v___y_1634_ == 0)
{
lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1642_; 
lean_inc_ref(v_decl_1616_);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_code_1505_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; lean_object* v_unused_1644_; 
v_unused_1643_ = lean_ctor_get(v_code_1505_, 1);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_code_1505_, 0);
lean_dec(v_unused_1644_);
v___x_1636_ = v_code_1505_;
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
else
{
lean_dec(v_code_1505_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 1, v___y_1633_);
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_decl_1616_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v___y_1633_);
v___x_1639_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
}
else
{
lean_object* v___x_1645_; 
lean_dec_ref(v___y_1633_);
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v_code_1505_);
return v___x_1645_;
}
}
v___jp_1646_:
{
if (v___y_1648_ == 0)
{
lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1656_; 
lean_inc_ref(v_decl_1616_);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_code_1505_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; lean_object* v_unused_1658_; 
v_unused_1657_ = lean_ctor_get(v_code_1505_, 1);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_code_1505_, 0);
lean_dec(v_unused_1658_);
v___x_1650_ = v_code_1505_;
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
else
{
lean_dec(v_code_1505_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 1, v___y_1647_);
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_decl_1616_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v___y_1647_);
v___x_1653_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
}
else
{
lean_object* v___x_1659_; 
lean_dec_ref(v___y_1647_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_code_1505_);
return v___x_1659_;
}
}
v___jp_1661_:
{
lean_object* v___x_1668_; 
lean_inc_ref(v_k_1617_);
lean_inc_ref(v_decl_1616_);
v___x_1668_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1616_, v_k_1617_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
if (lean_obj_tag(v_a_1669_) == 1)
{
lean_object* v_val_1670_; lean_object* v_fst_1671_; lean_object* v_snd_1672_; lean_object* v___x_1673_; 
lean_dec(v_value_1660_);
v_val_1670_ = lean_ctor_get(v_a_1669_, 0);
lean_inc(v_val_1670_);
lean_dec_ref_known(v_a_1669_, 1);
v_fst_1671_ = lean_ctor_get(v_val_1670_, 0);
lean_inc_n(v_fst_1671_, 2);
v_snd_1672_ = lean_ctor_get(v_val_1670_, 1);
lean_inc(v_snd_1672_);
lean_dec(v_val_1670_);
v___x_1673_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1671_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v___x_1675_ = 0;
v___x_1676_ = lean_box(0);
v___x_1677_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1678_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1678_, 0, v_a_1674_);
lean_ctor_set(v___x_1678_, 1, v___x_1676_);
lean_ctor_set(v___x_1678_, 2, v___x_1677_);
v___x_1679_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1675_, v_fst_1671_, v___x_1678_, v___y_1665_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1681_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1672_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; size_t v___x_1683_; size_t v___x_1684_; uint8_t v___x_1685_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v___x_1683_ = lean_ptr_addr(v_k_1617_);
v___x_1684_ = lean_ptr_addr(v_a_1682_);
v___x_1685_ = lean_usize_dec_eq(v___x_1683_, v___x_1684_);
if (v___x_1685_ == 0)
{
v___y_1589_ = v_a_1680_;
v___y_1590_ = v_a_1682_;
v___y_1591_ = v___x_1685_;
goto v___jp_1588_;
}
else
{
size_t v___x_1686_; size_t v___x_1687_; uint8_t v___x_1688_; 
v___x_1686_ = lean_ptr_addr(v_decl_1616_);
v___x_1687_ = lean_ptr_addr(v_a_1680_);
v___x_1688_ = lean_usize_dec_eq(v___x_1686_, v___x_1687_);
v___y_1589_ = v_a_1680_;
v___y_1590_ = v_a_1682_;
v___y_1591_ = v___x_1688_;
goto v___jp_1588_;
}
}
else
{
lean_dec(v_a_1680_);
lean_dec_ref_known(v_code_1505_, 2);
return v___x_1681_;
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_snd_1672_);
lean_dec_ref_known(v_code_1505_, 2);
v_a_1689_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1679_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1679_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_snd_1672_);
lean_dec(v_fst_1671_);
lean_dec_ref_known(v_code_1505_, 2);
v_a_1697_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1673_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1673_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
uint8_t v___x_1705_; lean_object* v___x_1706_; 
lean_dec(v_a_1669_);
v___x_1705_ = 1;
v___x_1706_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1705_, v_value_1660_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; uint8_t v___x_1708_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v___x_1708_ = lean_unbox(v_a_1707_);
lean_dec(v_a_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
lean_inc_ref(v_k_1617_);
v___x_1709_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1617_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; size_t v___x_1711_; size_t v___x_1712_; uint8_t v___x_1713_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v___x_1711_ = lean_ptr_addr(v_k_1617_);
v___x_1712_ = lean_ptr_addr(v_a_1710_);
v___x_1713_ = lean_usize_dec_eq(v___x_1711_, v___x_1712_);
if (v___x_1713_ == 0)
{
v___y_1619_ = v_a_1710_;
v___y_1620_ = v___x_1713_;
goto v___jp_1618_;
}
else
{
size_t v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = lean_ptr_addr(v_decl_1616_);
v___x_1715_ = lean_usize_dec_eq(v___x_1714_, v___x_1714_);
v___y_1619_ = v_a_1710_;
v___y_1620_ = v___x_1715_;
goto v___jp_1618_;
}
}
else
{
lean_dec_ref_known(v_code_1505_, 2);
return v___x_1709_;
}
}
else
{
lean_object* v___x_1716_; 
lean_inc_ref(v_decl_1616_);
v___x_1716_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1616_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v___x_1718_ = 0;
v___x_1719_ = lean_box(0);
v___x_1720_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1721_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1721_, 0, v_a_1717_);
lean_ctor_set(v___x_1721_, 1, v___x_1719_);
lean_ctor_set(v___x_1721_, 2, v___x_1720_);
lean_inc_ref(v_decl_1616_);
v___x_1722_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1718_, v_decl_1616_, v___x_1721_, v___y_1665_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
lean_inc_ref(v_k_1617_);
v___x_1724_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1617_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; size_t v___x_1726_; size_t v___x_1727_; uint8_t v___x_1728_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = lean_ptr_addr(v_k_1617_);
v___x_1727_ = lean_ptr_addr(v_a_1725_);
v___x_1728_ = lean_usize_dec_eq(v___x_1726_, v___x_1727_);
if (v___x_1728_ == 0)
{
v___y_1582_ = v_a_1725_;
v___y_1583_ = v_a_1723_;
v___y_1584_ = v___x_1728_;
goto v___jp_1581_;
}
else
{
size_t v___x_1729_; size_t v___x_1730_; uint8_t v___x_1731_; 
v___x_1729_ = lean_ptr_addr(v_decl_1616_);
v___x_1730_ = lean_ptr_addr(v_a_1723_);
v___x_1731_ = lean_usize_dec_eq(v___x_1729_, v___x_1730_);
v___y_1582_ = v_a_1725_;
v___y_1583_ = v_a_1723_;
v___y_1584_ = v___x_1731_;
goto v___jp_1581_;
}
}
else
{
lean_dec(v_a_1723_);
lean_dec_ref_known(v_code_1505_, 2);
return v___x_1724_;
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec_ref_known(v_code_1505_, 2);
v_a_1732_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1722_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1722_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref_known(v_code_1505_, 2);
v_a_1740_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1716_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1716_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec_ref_known(v_code_1505_, 2);
v_a_1748_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1706_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1706_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_value_1660_);
lean_dec_ref_known(v_code_1505_, 2);
v_a_1756_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1668_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1668_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1970_; lean_object* v_k_1971_; 
v_decl_1970_ = lean_ctor_get(v_code_1505_, 0);
v_k_1971_ = lean_ctor_get(v_code_1505_, 1);
lean_inc_ref(v_k_1971_);
lean_inc_ref(v_decl_1970_);
v_decl_1528_ = v_decl_1970_;
v_k_1529_ = v_k_1971_;
v___y_1530_ = v_a_1506_;
v___y_1531_ = v_a_1507_;
v___y_1532_ = v_a_1508_;
v___y_1533_ = v_a_1509_;
v___y_1534_ = v_a_1510_;
v___y_1535_ = v_a_1511_;
goto v___jp_1527_;
}
case 2:
{
lean_object* v_decl_1972_; lean_object* v_k_1973_; 
v_decl_1972_ = lean_ctor_get(v_code_1505_, 0);
v_k_1973_ = lean_ctor_get(v_code_1505_, 1);
lean_inc_ref(v_k_1973_);
lean_inc_ref(v_decl_1972_);
v_decl_1528_ = v_decl_1972_;
v_k_1529_ = v_k_1973_;
v___y_1530_ = v_a_1506_;
v___y_1531_ = v_a_1507_;
v___y_1532_ = v_a_1508_;
v___y_1533_ = v_a_1509_;
v___y_1534_ = v_a_1510_;
v___y_1535_ = v_a_1511_;
goto v___jp_1527_;
}
case 4:
{
lean_object* v_cases_1974_; lean_object* v_typeName_1975_; lean_object* v_resultType_1976_; lean_object* v_discr_1977_; lean_object* v_alts_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2017_; 
v_cases_1974_ = lean_ctor_get(v_code_1505_, 0);
lean_inc_ref(v_cases_1974_);
v_typeName_1975_ = lean_ctor_get(v_cases_1974_, 0);
v_resultType_1976_ = lean_ctor_get(v_cases_1974_, 1);
v_discr_1977_ = lean_ctor_get(v_cases_1974_, 2);
v_alts_1978_ = lean_ctor_get(v_cases_1974_, 3);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_cases_1974_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1980_ = v_cases_1974_;
v_isShared_1981_ = v_isSharedCheck_2017_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_alts_1978_);
lean_inc(v_discr_1977_);
lean_inc(v_resultType_1976_);
lean_inc(v_typeName_1975_);
lean_dec(v_cases_1974_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2017_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1978_);
v___x_1983_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v___x_1982_, v_alts_1978_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2008_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_2008_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2008_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
size_t v___x_1988_; size_t v___x_1989_; uint8_t v___x_1990_; 
v___x_1988_ = lean_ptr_addr(v_alts_1978_);
lean_dec_ref(v_alts_1978_);
v___x_1989_ = lean_ptr_addr(v_a_1984_);
v___x_1990_ = lean_usize_dec_eq(v___x_1988_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2003_; 
v_isSharedCheck_2003_ = !lean_is_exclusive(v_code_1505_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v_code_1505_, 0);
lean_dec(v_unused_2004_);
v___x_1992_ = v_code_1505_;
v_isShared_1993_ = v_isSharedCheck_2003_;
goto v_resetjp_1991_;
}
else
{
lean_dec(v_code_1505_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2003_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 3, v_a_1984_);
v___x_1995_ = v___x_1980_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_typeName_1975_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_resultType_1976_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_discr_1977_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v_a_1984_);
v___x_1995_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1995_);
v___x_1997_ = v___x_1992_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1999_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1997_);
v___x_1999_ = v___x_1986_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
else
{
lean_object* v___x_2006_; 
lean_dec(v_a_1984_);
lean_del_object(v___x_1980_);
lean_dec(v_discr_1977_);
lean_dec_ref(v_resultType_1976_);
lean_dec(v_typeName_1975_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v_code_1505_);
v___x_2006_ = v___x_1986_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_code_1505_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_del_object(v___x_1980_);
lean_dec_ref(v_alts_1978_);
lean_dec(v_discr_1977_);
lean_dec_ref(v_resultType_1976_);
lean_dec(v_typeName_1975_);
lean_dec_ref_known(v_code_1505_, 1);
v_a_2009_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1983_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1983_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
default: 
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_code_1505_);
return v___x_2018_;
}
}
v___jp_1513_:
{
if (v___y_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec_ref(v_code_1505_);
v___x_1517_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___y_1514_);
lean_ctor_set(v___x_1517_, 1, v___y_1515_);
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
return v___x_1518_;
}
else
{
lean_object* v___x_1519_; 
lean_dec_ref(v___y_1515_);
lean_dec_ref(v___y_1514_);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_code_1505_);
return v___x_1519_;
}
}
v___jp_1520_:
{
if (v___y_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec_ref(v_code_1505_);
v___x_1524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___y_1521_);
lean_ctor_set(v___x_1524_, 1, v___y_1522_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; 
lean_dec_ref(v___y_1522_);
lean_dec_ref(v___y_1521_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_code_1505_);
return v___x_1526_;
}
}
v___jp_1527_:
{
lean_object* v_params_1536_; lean_object* v_type_1537_; lean_object* v_value_1538_; lean_object* v___x_1539_; 
v_params_1536_ = lean_ctor_get(v_decl_1528_, 2);
lean_inc_ref(v_params_1536_);
v_type_1537_ = lean_ctor_get(v_decl_1528_, 3);
lean_inc_ref(v_type_1537_);
v_value_1538_ = lean_ctor_get(v_decl_1528_, 4);
lean_inc_ref(v_value_1538_);
v___x_1539_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_value_1538_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; uint8_t v___x_1541_; lean_object* v___x_1542_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v___x_1541_ = 0;
v___x_1542_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1541_, v_decl_1528_, v_type_1537_, v_params_1536_, v_a_1540_, v___y_1533_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1544_) == 0)
{
switch(lean_obj_tag(v_code_1505_))
{
case 1:
{
lean_object* v_a_1545_; lean_object* v_decl_1546_; lean_object* v_k_1547_; size_t v___x_1548_; size_t v___x_1549_; uint8_t v___x_1550_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v_decl_1546_ = lean_ctor_get(v_code_1505_, 0);
v_k_1547_ = lean_ctor_get(v_code_1505_, 1);
v___x_1548_ = lean_ptr_addr(v_k_1547_);
v___x_1549_ = lean_ptr_addr(v_a_1545_);
v___x_1550_ = lean_usize_dec_eq(v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
v___y_1521_ = v_a_1543_;
v___y_1522_ = v_a_1545_;
v___y_1523_ = v___x_1550_;
goto v___jp_1520_;
}
else
{
size_t v___x_1551_; size_t v___x_1552_; uint8_t v___x_1553_; 
v___x_1551_ = lean_ptr_addr(v_decl_1546_);
v___x_1552_ = lean_ptr_addr(v_a_1543_);
v___x_1553_ = lean_usize_dec_eq(v___x_1551_, v___x_1552_);
v___y_1521_ = v_a_1543_;
v___y_1522_ = v_a_1545_;
v___y_1523_ = v___x_1553_;
goto v___jp_1520_;
}
}
case 2:
{
lean_object* v_a_1554_; lean_object* v_decl_1555_; lean_object* v_k_1556_; size_t v___x_1557_; size_t v___x_1558_; uint8_t v___x_1559_; 
v_a_1554_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1544_, 1);
v_decl_1555_ = lean_ctor_get(v_code_1505_, 0);
v_k_1556_ = lean_ctor_get(v_code_1505_, 1);
v___x_1557_ = lean_ptr_addr(v_k_1556_);
v___x_1558_ = lean_ptr_addr(v_a_1554_);
v___x_1559_ = lean_usize_dec_eq(v___x_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
v___y_1514_ = v_a_1543_;
v___y_1515_ = v_a_1554_;
v___y_1516_ = v___x_1559_;
goto v___jp_1513_;
}
else
{
size_t v___x_1560_; size_t v___x_1561_; uint8_t v___x_1562_; 
v___x_1560_ = lean_ptr_addr(v_decl_1555_);
v___x_1561_ = lean_ptr_addr(v_a_1543_);
v___x_1562_ = lean_usize_dec_eq(v___x_1560_, v___x_1561_);
v___y_1514_ = v_a_1543_;
v___y_1515_ = v_a_1554_;
v___y_1516_ = v___x_1562_;
goto v___jp_1513_;
}
}
default: 
{
lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_a_1543_);
lean_dec_ref(v_code_1505_);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v___x_1544_, 0);
lean_dec(v_unused_1572_);
v___x_1564_ = v___x_1544_;
v_isShared_1565_ = v_isSharedCheck_1571_;
goto v_resetjp_1563_;
}
else
{
lean_dec(v___x_1544_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1571_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1566_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3, &l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3);
v___x_1567_ = l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(v___x_1566_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1567_);
v___x_1569_ = v___x_1564_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
else
{
lean_dec(v_a_1543_);
lean_dec_ref(v_code_1505_);
return v___x_1544_;
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v_k_1529_);
lean_dec_ref(v_code_1505_);
v_a_1573_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1542_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1542_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_dec_ref(v_type_1537_);
lean_dec_ref(v_params_1536_);
lean_dec_ref(v_k_1529_);
lean_dec_ref(v_decl_1528_);
lean_dec_ref(v_code_1505_);
return v___x_1539_;
}
}
v___jp_1581_:
{
if (v___y_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec_ref(v_code_1505_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___y_1583_);
lean_ctor_set(v___x_1585_, 1, v___y_1582_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; 
lean_dec_ref(v___y_1583_);
lean_dec_ref(v___y_1582_);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_code_1505_);
return v___x_1587_;
}
}
v___jp_1588_:
{
if (v___y_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec_ref(v_code_1505_);
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___y_1589_);
lean_ctor_set(v___x_1592_, 1, v___y_1590_);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
else
{
lean_object* v___x_1594_; 
lean_dec_ref(v___y_1590_);
lean_dec_ref(v___y_1589_);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_code_1505_);
return v___x_1594_;
}
}
v___jp_1595_:
{
if (v___y_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec_ref(v_code_1505_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___y_1596_);
lean_ctor_set(v___x_1599_, 1, v___y_1597_);
v___x_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1599_);
return v___x_1600_;
}
else
{
lean_object* v___x_1601_; 
lean_dec_ref(v___y_1597_);
lean_dec_ref(v___y_1596_);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v_code_1505_);
return v___x_1601_;
}
}
v___jp_1602_:
{
if (v___y_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec_ref(v_code_1505_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___y_1603_);
lean_ctor_set(v___x_1606_, 1, v___y_1604_);
v___x_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; 
lean_dec_ref(v___y_1604_);
lean_dec_ref(v___y_1603_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_code_1505_);
return v___x_1608_;
}
}
v___jp_1609_:
{
if (v___y_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec_ref(v_code_1505_);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___y_1610_);
lean_ctor_set(v___x_1613_, 1, v___y_1611_);
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
return v___x_1614_;
}
else
{
lean_object* v___x_1615_; 
lean_dec_ref(v___y_1611_);
lean_dec_ref(v___y_1610_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_code_1505_);
return v___x_1615_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object* v_i_2019_, lean_object* v_as_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = lean_array_get_size(v_as_2020_);
v___x_2029_ = lean_nat_dec_lt(v_i_2019_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_dec(v_i_2019_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v_as_2020_);
return v___x_2030_;
}
else
{
lean_object* v_a_2031_; lean_object* v___y_2033_; 
v_a_2031_ = lean_array_fget_borrowed(v_as_2020_, v_i_2019_);
switch(lean_obj_tag(v_a_2031_))
{
case 0:
{
lean_object* v_code_2055_; 
v_code_2055_ = lean_ctor_get(v_a_2031_, 2);
lean_inc_ref(v_code_2055_);
v___y_2033_ = v_code_2055_;
goto v___jp_2032_;
}
case 1:
{
lean_object* v_code_2056_; 
v_code_2056_ = lean_ctor_get(v_a_2031_, 1);
lean_inc_ref(v_code_2056_);
v___y_2033_ = v_code_2056_;
goto v___jp_2032_;
}
default: 
{
lean_object* v_code_2057_; 
v_code_2057_ = lean_ctor_get(v_a_2031_, 0);
lean_inc_ref(v_code_2057_);
v___y_2033_ = v_code_2057_;
goto v___jp_2032_;
}
}
v___jp_2032_:
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v___y_2033_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; size_t v___x_2037_; size_t v___x_2038_; uint8_t v___x_2039_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
lean_inc(v_a_2031_);
v___x_2036_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2031_, v_a_2035_);
v___x_2037_ = lean_ptr_addr(v_a_2031_);
v___x_2038_ = lean_ptr_addr(v___x_2036_);
v___x_2039_ = lean_usize_dec_eq(v___x_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_add(v_i_2019_, v___x_2040_);
v___x_2042_ = lean_array_fset(v_as_2020_, v_i_2019_, v___x_2036_);
lean_dec(v_i_2019_);
v_i_2019_ = v___x_2041_;
v_as_2020_ = v___x_2042_;
goto _start;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec_ref(v___x_2036_);
v___x_2044_ = lean_unsigned_to_nat(1u);
v___x_2045_ = lean_nat_add(v_i_2019_, v___x_2044_);
lean_dec(v_i_2019_);
v_i_2019_ = v___x_2045_;
goto _start;
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v_as_2020_);
lean_dec(v_i_2019_);
v_a_2047_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2034_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2034_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object* v_i_2058_, lean_object* v_as_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_2058_, v_as_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object* v_code_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_code_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(lean_object* v_f_2077_, lean_object* v_v_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
if (lean_obj_tag(v_v_2078_) == 0)
{
lean_object* v_code_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2110_; 
v_code_2086_ = lean_ctor_get(v_v_2078_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_v_2078_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2088_ = v_v_2078_;
v_isShared_2089_ = v_isSharedCheck_2110_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_code_2086_);
lean_dec(v_v_2078_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2110_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; 
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
v___x_2090_ = lean_apply_8(v_f_2077_, v_code_2086_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, lean_box(0));
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2101_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2101_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2101_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v_a_2091_);
v___x_2096_ = v___x_2088_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2098_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2096_);
v___x_2098_ = v___x_2093_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_del_object(v___x_2088_);
v_a_2102_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2090_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2090_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
else
{
lean_object* v___x_2111_; 
lean_dec_ref(v_f_2077_);
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_v_2078_);
return v___x_2111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(lean_object* v_f_2112_, lean_object* v_v_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2112_, v_v_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(uint8_t v_pu_2122_, lean_object* v_f_2123_, lean_object* v_v_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2123_, v_v_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(lean_object* v_pu_2133_, lean_object* v_f_2134_, lean_object* v_v_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v_pu_boxed_2143_; lean_object* v_res_2144_; 
v_pu_boxed_2143_ = lean_unbox(v_pu_2133_);
v_res_2144_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_boxed_2143_, v_f_2134_, v_v_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object* v_decl_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_toSignature_2154_; lean_object* v_value_2155_; uint8_t v_recursive_2156_; lean_object* v_inlineAttr_x3f_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2182_; 
v_toSignature_2154_ = lean_ctor_get(v_decl_2146_, 0);
v_value_2155_ = lean_ctor_get(v_decl_2146_, 1);
v_recursive_2156_ = lean_ctor_get_uint8(v_decl_2146_, sizeof(void*)*3);
v_inlineAttr_x3f_2157_ = lean_ctor_get(v_decl_2146_, 2);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_decl_2146_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2159_ = v_decl_2146_;
v_isShared_2160_ = v_isSharedCheck_2182_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_inlineAttr_x3f_2157_);
lean_inc(v_value_2155_);
lean_inc(v_toSignature_2154_);
lean_dec(v_decl_2146_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2182_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0));
v___x_2162_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v___x_2161_, v_value_2155_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2173_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2173_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2173_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v_a_2163_);
v___x_2168_ = v___x_2159_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_toSignature_2154_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_a_2163_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_inlineAttr_x3f_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*3, v_recursive_2156_);
v___x_2168_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 0, v___x_2168_);
v___x_2170_ = v___x_2165_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_del_object(v___x_2159_);
lean_dec(v_inlineAttr_x3f_2157_);
lean_dec_ref(v_toSignature_2154_);
v_a_2174_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2162_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2162_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(lean_object* v_decl_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
lean_dec(v_a_2189_);
lean_dec_ref(v_a_2188_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
return v_res_2191_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1(void){
_start:
{
lean_object* v_cellCount_2194_; lean_object* v___x_2195_; 
v_cellCount_2194_ = lean_unsigned_to_nat(16u);
v___x_2195_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__2(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2196_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1);
v___x_2197_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
lean_ctor_set(v___x_2199_, 1, v___x_2197_);
lean_ctor_set(v___x_2199_, 2, v___x_2196_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__3(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__2, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__2);
v___x_2201_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0));
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___x_2200_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* v_decl_2203_, lean_object* v_sccDecls_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v_toSignature_2213_; lean_object* v_name_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2210_ = lean_unsigned_to_nat(0u);
v___x_2211_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__3, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__3_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__3);
v___x_2212_ = lean_st_mk_ref(v___x_2211_);
v_toSignature_2213_ = lean_ctor_get(v_decl_2203_, 0);
v_name_2214_ = lean_ctor_get(v_toSignature_2213_, 0);
lean_inc(v_name_2214_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_name_2214_);
lean_ctor_set(v___x_2215_, 1, v_sccDecls_2204_);
v___x_2216_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2203_, v___x_2215_, v___x_2212_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
lean_dec_ref_known(v___x_2215_, 2);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2242_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2242_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2242_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2221_; lean_object* v_decls_2222_; lean_object* v_decl_2224_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2221_ = lean_st_ref_get(v___x_2212_);
lean_dec(v___x_2212_);
v_decls_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc_ref(v_decls_2222_);
lean_dec(v___x_2221_);
v___x_2229_ = lean_array_get_size(v_decls_2222_);
v___x_2230_ = lean_nat_dec_eq(v___x_2229_, v___x_2210_);
if (v___x_2230_ == 0)
{
uint8_t v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = 0;
v___x_2232_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2231_, v_a_2217_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v_decl_2224_ = v_a_2233_;
goto v___jp_2223_;
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec_ref(v_decls_2222_);
lean_del_object(v___x_2219_);
v_a_2234_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2232_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2232_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
v_decl_2224_ = v_a_2217_;
goto v___jp_2223_;
}
v___jp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2225_ = lean_array_push(v_decls_2222_, v_decl_2224_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v___x_2225_);
v___x_2227_ = v___x_2219_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v___x_2212_);
v_a_2243_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2216_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2216_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(lean_object* v_decl_2251_, lean_object* v_sccDecls_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v_decl_2251_, v_sccDecls_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(lean_object* v_decls_2259_, lean_object* v_as_2260_, size_t v_i_2261_, size_t v_stop_2262_, lean_object* v_b_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_a_2270_; uint8_t v___x_2274_; 
v___x_2274_ = lean_usize_dec_eq(v_i_2261_, v_stop_2262_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_array_uget_borrowed(v_as_2260_, v_i_2261_);
lean_inc_ref(v_decls_2259_);
lean_inc(v___x_2275_);
v___x_2276_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v___x_2275_, v_decls_2259_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2278_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___x_2278_ = l_Array_append___redArg(v_b_2263_, v_a_2277_);
lean_dec(v_a_2277_);
v_a_2270_ = v___x_2278_;
goto v___jp_2269_;
}
else
{
lean_dec_ref(v_b_2263_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2279_; 
v_a_2279_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2276_, 1);
v_a_2270_ = v_a_2279_;
goto v___jp_2269_;
}
else
{
lean_dec_ref(v_decls_2259_);
return v___x_2276_;
}
}
}
else
{
lean_object* v___x_2280_; 
lean_dec_ref(v_decls_2259_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v_b_2263_);
return v___x_2280_;
}
v___jp_2269_:
{
size_t v___x_2271_; size_t v___x_2272_; 
v___x_2271_ = ((size_t)1ULL);
v___x_2272_ = lean_usize_add(v_i_2261_, v___x_2271_);
v_i_2261_ = v___x_2272_;
v_b_2263_ = v_a_2270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object* v_decls_2281_, lean_object* v_as_2282_, lean_object* v_i_2283_, lean_object* v_stop_2284_, lean_object* v_b_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
size_t v_i_boxed_2291_; size_t v_stop_boxed_2292_; lean_object* v_res_2293_; 
v_i_boxed_2291_ = lean_unbox_usize(v_i_2283_);
lean_dec(v_i_2283_);
v_stop_boxed_2292_ = lean_unbox_usize(v_stop_2284_);
lean_dec(v_stop_2284_);
v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2281_, v_as_2282_, v_i_boxed_2291_, v_stop_boxed_2292_, v_b_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec_ref(v_as_2282_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* v___x_2294_, lean_object* v_decls_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_2296_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2326_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2326_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2326_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
uint8_t v_extractClosed_2306_; 
v_extractClosed_2306_ = lean_ctor_get_uint8(v_a_2302_, sizeof(void*)*4 + 1);
lean_dec(v_a_2302_);
if (v_extractClosed_2306_ == 0)
{
lean_object* v___x_2308_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v_decls_2295_);
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_decls_2295_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2310_ = lean_mk_empty_array_with_capacity(v___x_2294_);
v___x_2311_ = lean_array_get_size(v_decls_2295_);
v___x_2312_ = lean_nat_dec_lt(v___x_2294_, v___x_2311_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2314_; 
lean_dec_ref(v_decls_2295_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2310_);
v___x_2314_ = v___x_2304_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2310_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
else
{
uint8_t v___x_2316_; 
v___x_2316_ = lean_nat_dec_le(v___x_2311_, v___x_2311_);
if (v___x_2316_ == 0)
{
if (v___x_2312_ == 0)
{
lean_object* v___x_2318_; 
lean_dec_ref(v_decls_2295_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2310_);
v___x_2318_ = v___x_2304_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2310_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
else
{
size_t v___x_2320_; size_t v___x_2321_; lean_object* v___x_2322_; 
lean_del_object(v___x_2304_);
v___x_2320_ = ((size_t)0ULL);
v___x_2321_ = lean_usize_of_nat(v___x_2311_);
lean_inc_ref(v_decls_2295_);
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2295_, v_decls_2295_, v___x_2320_, v___x_2321_, v___x_2310_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec_ref(v_decls_2295_);
return v___x_2322_;
}
}
else
{
size_t v___x_2323_; size_t v___x_2324_; lean_object* v___x_2325_; 
lean_del_object(v___x_2304_);
v___x_2323_ = ((size_t)0ULL);
v___x_2324_ = lean_usize_of_nat(v___x_2311_);
lean_inc_ref(v_decls_2295_);
v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2295_, v_decls_2295_, v___x_2323_, v___x_2324_, v___x_2310_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec_ref(v_decls_2295_);
return v___x_2325_;
}
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v_decls_2295_);
v_a_2327_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2301_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2301_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object* v___x_2335_, lean_object* v_decls_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(v___x_2335_, v_decls_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___x_2335_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2425_; uint8_t v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2426_ = 1;
v___x_2427_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2428_ = l_Lean_registerTraceClass(v___x_2425_, v___x_2426_, v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
return v_res_2430_;
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
