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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_i_2_ = stack[1].m_num;
size_t v_stop_3_ = stack[2].m_num;
lean_object* v_b_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v_res_19_;
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_as_1_, v_i_2_, v_stop_3_, v_b_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
stack->m_obj
 = v_res_19_;
}
lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(lean_object* v_v_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
switch(lean_obj_tag(v_v_20_))
{
case 2:
{
lean_object* v_struct_27_; lean_object* v___x_28_; 
v_struct_27_ = lean_ctor_get(v_v_20_, 2);
v___x_28_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_struct_27_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
return v___x_28_;
}
case 3:
{
lean_object* v_args_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v_args_29_ = lean_ctor_get(v_v_20_, 2);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_array_get_size(v_args_29_);
v___x_32_ = lean_box(0);
v___x_33_ = lean_nat_dec_lt(v___x_30_, v___x_31_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_32_);
return v___x_34_;
}
else
{
uint8_t v___x_35_; 
v___x_35_ = lean_nat_dec_le(v___x_31_, v___x_31_);
if (v___x_35_ == 0)
{
if (v___x_33_ == 0)
{
lean_object* v___x_36_; 
v___x_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_32_);
return v___x_36_;
}
else
{
size_t v___x_37_; size_t v___x_38_; lean_object* v___x_39_; 
v___x_37_ = ((size_t)0ULL);
v___x_38_ = lean_usize_of_nat(v___x_31_);
v___x_39_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_29_, v___x_37_, v___x_38_, v___x_32_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
return v___x_39_;
}
}
else
{
size_t v___x_40_; size_t v___x_41_; lean_object* v___x_42_; 
v___x_40_ = ((size_t)0ULL);
v___x_41_ = lean_usize_of_nat(v___x_31_);
v___x_42_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_29_, v___x_40_, v___x_41_, v___x_32_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
return v___x_42_;
}
}
}
case 4:
{
lean_object* v_fvarId_43_; lean_object* v_args_44_; lean_object* v___x_45_; 
v_fvarId_43_ = lean_ctor_get(v_v_20_, 0);
v_args_44_ = lean_ctor_get(v_v_20_, 1);
v___x_45_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_43_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_66_; 
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; 
v_unused_67_ = lean_ctor_get(v___x_45_, 0);
lean_dec(v_unused_67_);
v___x_47_ = v___x_45_;
v_isShared_48_ = v_isSharedCheck_66_;
goto v_resetjp_46_;
}
else
{
lean_dec(v___x_45_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_66_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_array_get_size(v_args_44_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_nat_dec_lt(v___x_49_, v___x_50_);
if (v___x_52_ == 0)
{
lean_object* v___x_54_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v___x_51_);
v___x_54_ = v___x_47_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_51_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
else
{
uint8_t v___x_56_; 
v___x_56_ = lean_nat_dec_le(v___x_50_, v___x_50_);
if (v___x_56_ == 0)
{
if (v___x_52_ == 0)
{
lean_object* v___x_58_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v___x_51_);
v___x_58_ = v___x_47_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_51_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
else
{
size_t v___x_60_; size_t v___x_61_; lean_object* v___x_62_; 
lean_del_object(v___x_47_);
v___x_60_ = ((size_t)0ULL);
v___x_61_ = lean_usize_of_nat(v___x_50_);
v___x_62_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_44_, v___x_60_, v___x_61_, v___x_51_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
return v___x_62_;
}
}
else
{
size_t v___x_63_; size_t v___x_64_; lean_object* v___x_65_; 
lean_del_object(v___x_47_);
v___x_63_ = ((size_t)0ULL);
v___x_64_ = lean_usize_of_nat(v___x_50_);
v___x_65_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_44_, v___x_63_, v___x_64_, v___x_51_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
return v___x_65_;
}
}
}
}
else
{
return v___x_45_;
}
}
default: 
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_box(0);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_20_ = stack[0].m_obj;
lean_object* v_a_21_ = stack[1].m_obj;
lean_object* v_a_22_ = stack[2].m_obj;
lean_object* v_a_23_ = stack[3].m_obj;
lean_object* v_a_24_ = stack[4].m_obj;
lean_object* v_a_25_ = stack[5].m_obj;
lean_object* v_res_70_;
v_res_70_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_v_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
stack->m_obj
 = v_res_70_;
}
lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(lean_object* v_fvarId_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
uint8_t v___x_78_; lean_object* v___x_79_; 
v___x_78_ = 0;
v___x_79_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_78_, v_fvarId_71_, v_a_74_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_101_; 
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_101_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_101_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
if (lean_obj_tag(v_a_80_) == 1)
{
lean_object* v_val_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_96_; 
lean_del_object(v___x_82_);
v_val_84_ = lean_ctor_get(v_a_80_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_a_80_);
if (v_isSharedCheck_96_ == 0)
{
v___x_86_ = v_a_80_;
v_isShared_87_ = v_isSharedCheck_96_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_val_84_);
lean_dec(v_a_80_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_96_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_88_ = lean_st_ref_take(v_a_72_);
lean_inc(v_val_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 0);
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_val_84_);
v___x_90_ = v_reuseFailAlloc_95_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v_value_93_; lean_object* v___x_94_; 
v___x_91_ = lean_array_push(v___x_88_, v___x_90_);
v___x_92_ = lean_st_ref_put(v_a_72_, v___x_91_);
v_value_93_ = lean_ctor_get(v_val_84_, 3);
lean_inc(v_value_93_);
lean_dec(v_val_84_);
v___x_94_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_93_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
lean_dec(v_value_93_);
return v___x_94_;
}
}
}
else
{
lean_object* v___x_97_; lean_object* v___x_99_; 
lean_dec(v_a_80_);
v___x_97_ = lean_box(0);
if (v_isShared_83_ == 0)
{
lean_ctor_set(v___x_82_, 0, v___x_97_);
v___x_99_ = v___x_82_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
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
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_a_102_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_79_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_79_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_extractFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_71_ = stack[0].m_obj;
lean_object* v_a_72_ = stack[1].m_obj;
lean_object* v_a_73_ = stack[2].m_obj;
lean_object* v_a_74_ = stack[3].m_obj;
lean_object* v_a_75_ = stack[4].m_obj;
lean_object* v_a_76_ = stack[5].m_obj;
lean_object* v_res_110_;
v_res_110_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
stack->m_obj
 = v_res_110_;
}
lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg(lean_object* v_arg_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
if (lean_obj_tag(v_arg_111_) == 1)
{
lean_object* v_fvarId_118_; lean_object* v___x_119_; 
v_fvarId_118_ = lean_ctor_get(v_arg_111_, 0);
v___x_119_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_118_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_box(0);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_extractArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_111_ = stack[0].m_obj;
lean_object* v_a_112_ = stack[1].m_obj;
lean_object* v_a_113_ = stack[2].m_obj;
lean_object* v_a_114_ = stack[3].m_obj;
lean_object* v_a_115_ = stack[4].m_obj;
lean_object* v_a_116_ = stack[5].m_obj;
lean_object* v_res_122_;
v_res_122_ = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(v_arg_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg___boxed(lean_object* v_arg_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(v_arg_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
lean_dec(v_a_124_);
lean_dec(v_arg_123_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0___boxed(lean_object* v_as_131_, lean_object* v_i_132_, lean_object* v_stop_133_, lean_object* v_b_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
size_t v_i_boxed_141_; size_t v_stop_boxed_142_; lean_object* v_res_143_; 
v_i_boxed_141_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_stop_boxed_142_ = lean_unbox_usize(v_stop_133_);
lean_dec(v_stop_133_);
v_res_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_as_131_, v_i_boxed_141_, v_stop_boxed_142_, v_b_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v_as_131_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar___boxed(lean_object* v_fvarId_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec(v_fvarId_144_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___boxed(lean_object* v_v_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_v_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec(v_v_152_);
return v_res_159_;
}
}
uint8_t l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(lean_object* v_arg_160_){
_start:
{
if (lean_obj_tag(v_arg_160_) == 1)
{
uint8_t v___x_161_; 
v___x_161_ = 0;
return v___x_161_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = 1;
return v___x_162_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_160_ = stack[0].m_obj;
uint8_t v_res_163_;
v_res_163_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v_arg_160_);
stack->m_num = v_res_163_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg___boxed(lean_object* v_arg_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v_arg_164_);
lean_dec(v_arg_164_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t v_____do__lift_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
if (v_____do__lift_167_ == 0)
{
uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = 1;
v___x_176_ = lean_box(v___x_175_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
else
{
uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = 0;
v___x_179_ = lean_box(v___x_178_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_167_ = stack[0].m_num;
lean_object* v___y_168_ = stack[1].m_obj;
lean_object* v___y_169_ = stack[2].m_obj;
lean_object* v___y_170_ = stack[3].m_obj;
lean_object* v___y_171_ = stack[4].m_obj;
lean_object* v___y_172_ = stack[5].m_obj;
lean_object* v___y_173_ = stack[6].m_obj;
lean_object* v_res_181_;
v_res_181_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v_____do__lift_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
stack->m_obj
 = v_res_181_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object* v_____do__lift_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
uint8_t v_____do__lift_14824__boxed_190_; lean_object* v_res_191_; 
v_____do__lift_14824__boxed_190_ = lean_unbox(v_____do__lift_182_);
v_res_191_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v_____do__lift_14824__boxed_190_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(lean_object* v_a_192_, lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_box(0);
return v___x_194_;
}
else
{
lean_object* v_key_195_; lean_object* v_value_196_; lean_object* v_tail_197_; uint8_t v___x_198_; 
v_key_195_ = lean_ctor_get(v_x_193_, 0);
v_value_196_ = lean_ctor_get(v_x_193_, 1);
v_tail_197_ = lean_ctor_get(v_x_193_, 2);
v___x_198_ = l_Lean_instBEqFVarId_beq(v_key_195_, v_a_192_);
if (v___x_198_ == 0)
{
v_x_193_ = v_tail_197_;
goto _start;
}
else
{
lean_object* v___x_200_; 
lean_inc(v_value_196_);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v_value_196_);
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg___boxed(lean_object* v_a_201_, lean_object* v_x_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_201_, v_x_202_);
lean_dec(v_x_202_);
lean_dec(v_a_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(lean_object* v_m_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_buckets_206_; lean_object* v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v_fold_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_buckets_206_ = lean_ctor_get(v_m_204_, 1);
v___x_207_ = lean_array_get_size(v_buckets_206_);
v___x_208_ = l_Lean_instHashableFVarId_hash(v_a_205_);
v___x_209_ = 32ULL;
v___x_210_ = lean_uint64_shift_right(v___x_208_, v___x_209_);
v_fold_211_ = lean_uint64_xor(v___x_208_, v___x_210_);
v___x_212_ = 16ULL;
v___x_213_ = lean_uint64_shift_right(v_fold_211_, v___x_212_);
v___x_214_ = lean_uint64_xor(v_fold_211_, v___x_213_);
v___x_215_ = lean_uint64_to_usize(v___x_214_);
v___x_216_ = lean_usize_of_nat(v___x_207_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_sub(v___x_216_, v___x_217_);
v___x_219_ = lean_usize_land(v___x_215_, v___x_218_);
v___x_220_ = lean_array_uget_borrowed(v_buckets_206_, v___x_219_);
v___x_221_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_205_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg___boxed(lean_object* v_m_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_m_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
return v_x_225_;
}
else
{
lean_object* v_key_227_; lean_object* v_value_228_; lean_object* v_tail_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_252_; 
v_key_227_ = lean_ctor_get(v_x_226_, 0);
v_value_228_ = lean_ctor_get(v_x_226_, 1);
v_tail_229_ = lean_ctor_get(v_x_226_, 2);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_252_ == 0)
{
v___x_231_ = v_x_226_;
v_isShared_232_ = v_isSharedCheck_252_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_tail_229_);
lean_inc(v_value_228_);
lean_inc(v_key_227_);
lean_dec(v_x_226_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_252_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v_fold_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_233_ = lean_array_get_size(v_x_225_);
v___x_234_ = l_Lean_instHashableFVarId_hash(v_key_227_);
v___x_235_ = 32ULL;
v___x_236_ = lean_uint64_shift_right(v___x_234_, v___x_235_);
v_fold_237_ = lean_uint64_xor(v___x_234_, v___x_236_);
v___x_238_ = 16ULL;
v___x_239_ = lean_uint64_shift_right(v_fold_237_, v___x_238_);
v___x_240_ = lean_uint64_xor(v_fold_237_, v___x_239_);
v___x_241_ = lean_uint64_to_usize(v___x_240_);
v___x_242_ = lean_usize_of_nat(v___x_233_);
v___x_243_ = ((size_t)1ULL);
v___x_244_ = lean_usize_sub(v___x_242_, v___x_243_);
v___x_245_ = lean_usize_land(v___x_241_, v___x_244_);
v___x_246_ = lean_array_uget_borrowed(v_x_225_, v___x_245_);
lean_inc(v___x_246_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 2, v___x_246_);
v___x_248_ = v___x_231_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_key_227_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_value_228_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v___x_246_);
v___x_248_ = v_reuseFailAlloc_251_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; 
v___x_249_ = lean_array_uset(v_x_225_, v___x_245_, v___x_248_);
v_x_225_ = v___x_249_;
v_x_226_ = v_tail_229_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(lean_object* v_i_253_, lean_object* v_source_254_, lean_object* v_target_255_){
_start:
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_array_get_size(v_source_254_);
v___x_257_ = lean_nat_dec_lt(v_i_253_, v___x_256_);
if (v___x_257_ == 0)
{
lean_dec_ref(v_source_254_);
lean_dec(v_i_253_);
return v_target_255_;
}
else
{
lean_object* v_es_258_; lean_object* v___x_259_; lean_object* v_source_260_; lean_object* v_target_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_es_258_ = lean_array_fget(v_source_254_, v_i_253_);
v___x_259_ = lean_box(0);
v_source_260_ = lean_array_fset(v_source_254_, v_i_253_, v___x_259_);
v_target_261_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_target_255_, v_es_258_);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_nat_add(v_i_253_, v___x_262_);
lean_dec(v_i_253_);
v_i_253_ = v___x_263_;
v_source_254_ = v_source_260_;
v_target_255_ = v_target_261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(lean_object* v_data_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v_nbuckets_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_266_ = lean_array_get_size(v_data_265_);
v___x_267_ = lean_unsigned_to_nat(2u);
v_nbuckets_268_ = lean_nat_mul(v___x_266_, v___x_267_);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_box(0);
v___x_271_ = lean_mk_array(v_nbuckets_268_, v___x_270_);
v___x_272_ = lean_array_propagate_mark(v_data_265_, v___x_271_);
v___x_273_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v___x_269_, v_data_265_, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(lean_object* v_a_274_, lean_object* v_b_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_dec(v_b_275_);
lean_dec(v_a_274_);
return v_x_276_;
}
else
{
lean_object* v_key_277_; lean_object* v_value_278_; lean_object* v_tail_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_291_; 
v_key_277_ = lean_ctor_get(v_x_276_, 0);
v_value_278_ = lean_ctor_get(v_x_276_, 1);
v_tail_279_ = lean_ctor_get(v_x_276_, 2);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_291_ == 0)
{
v___x_281_ = v_x_276_;
v_isShared_282_ = v_isSharedCheck_291_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_tail_279_);
lean_inc(v_value_278_);
lean_inc(v_key_277_);
lean_dec(v_x_276_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_291_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
uint8_t v___x_283_; 
v___x_283_ = l_Lean_instBEqFVarId_beq(v_key_277_, v_a_274_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_284_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_274_, v_b_275_, v_tail_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 2, v___x_284_);
v___x_286_ = v___x_281_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_key_277_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_value_278_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
else
{
lean_object* v___x_289_; 
lean_dec(v_value_278_);
lean_dec(v_key_277_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v_b_275_);
lean_ctor_set(v___x_281_, 0, v_a_274_);
v___x_289_ = v___x_281_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_274_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_b_275_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_tail_279_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(lean_object* v_a_292_, lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
uint8_t v___x_294_; 
v___x_294_ = 0;
return v___x_294_;
}
else
{
lean_object* v_key_295_; lean_object* v_tail_296_; uint8_t v___x_297_; 
v_key_295_ = lean_ctor_get(v_x_293_, 0);
v_tail_296_ = lean_ctor_get(v_x_293_, 2);
v___x_297_ = l_Lean_instBEqFVarId_beq(v_key_295_, v_a_292_);
if (v___x_297_ == 0)
{
v_x_293_ = v_tail_296_;
goto _start;
}
else
{
return v___x_297_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_292_ = stack[0].m_obj;
lean_object* v_x_293_ = stack[1].m_obj;
uint8_t v_res_299_;
v_res_299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_292_, v_x_293_);
stack->m_num = v_res_299_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg___boxed(lean_object* v_a_300_, lean_object* v_x_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_300_, v_x_301_);
lean_dec(v_x_301_);
lean_dec(v_a_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(lean_object* v_m_304_, lean_object* v_a_305_, lean_object* v_b_306_){
_start:
{
lean_object* v_size_307_; lean_object* v_buckets_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_351_; 
v_size_307_ = lean_ctor_get(v_m_304_, 0);
v_buckets_308_ = lean_ctor_get(v_m_304_, 1);
v_isSharedCheck_351_ = !lean_is_exclusive(v_m_304_);
if (v_isSharedCheck_351_ == 0)
{
v___x_310_ = v_m_304_;
v_isShared_311_ = v_isSharedCheck_351_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_buckets_308_);
lean_inc(v_size_307_);
lean_dec(v_m_304_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_351_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v_fold_316_; uint64_t v___x_317_; uint64_t v___x_318_; uint64_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v_bkt_325_; uint8_t v___x_326_; 
v___x_312_ = lean_array_get_size(v_buckets_308_);
v___x_313_ = l_Lean_instHashableFVarId_hash(v_a_305_);
v___x_314_ = 32ULL;
v___x_315_ = lean_uint64_shift_right(v___x_313_, v___x_314_);
v_fold_316_ = lean_uint64_xor(v___x_313_, v___x_315_);
v___x_317_ = 16ULL;
v___x_318_ = lean_uint64_shift_right(v_fold_316_, v___x_317_);
v___x_319_ = lean_uint64_xor(v_fold_316_, v___x_318_);
v___x_320_ = lean_uint64_to_usize(v___x_319_);
v___x_321_ = lean_usize_of_nat(v___x_312_);
v___x_322_ = ((size_t)1ULL);
v___x_323_ = lean_usize_sub(v___x_321_, v___x_322_);
v___x_324_ = lean_usize_land(v___x_320_, v___x_323_);
v_bkt_325_ = lean_array_uget_borrowed(v_buckets_308_, v___x_324_);
v___x_326_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_305_, v_bkt_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v_size_x27_328_; lean_object* v___x_329_; lean_object* v_buckets_x27_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_327_ = lean_unsigned_to_nat(1u);
v_size_x27_328_ = lean_nat_add(v_size_307_, v___x_327_);
lean_dec(v_size_307_);
lean_inc(v_bkt_325_);
v___x_329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_329_, 0, v_a_305_);
lean_ctor_set(v___x_329_, 1, v_b_306_);
lean_ctor_set(v___x_329_, 2, v_bkt_325_);
v_buckets_x27_330_ = lean_array_uset(v_buckets_308_, v___x_324_, v___x_329_);
v___x_331_ = lean_unsigned_to_nat(4u);
v___x_332_ = lean_nat_mul(v_size_x27_328_, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(3u);
v___x_334_ = lean_nat_div(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_array_get_size(v_buckets_x27_330_);
v___x_336_ = lean_nat_dec_le(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
if (v___x_336_ == 0)
{
lean_object* v_val_337_; lean_object* v___x_339_; 
v_val_337_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_buckets_x27_330_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v_val_337_);
lean_ctor_set(v___x_310_, 0, v_size_x27_328_);
v___x_339_ = v___x_310_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_size_x27_328_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_val_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
else
{
lean_object* v___x_342_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v_buckets_x27_330_);
lean_ctor_set(v___x_310_, 0, v_size_x27_328_);
v___x_342_ = v___x_310_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_size_x27_328_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_buckets_x27_330_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
else
{
lean_object* v___x_344_; lean_object* v_buckets_x27_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
lean_inc(v_bkt_325_);
v___x_344_ = lean_box(0);
v_buckets_x27_345_ = lean_array_uset(v_buckets_308_, v___x_324_, v___x_344_);
v___x_346_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_305_, v_b_306_, v_bkt_325_);
v___x_347_ = lean_array_uset(v_buckets_x27_345_, v___x_324_, v___x_346_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v___x_347_);
v___x_349_ = v___x_310_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_size_307_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(lean_object* v_declName_352_, lean_object* v_as_353_, size_t v_i_354_, size_t v_stop_355_){
_start:
{
uint8_t v___x_356_; 
v___x_356_ = lean_usize_dec_eq(v_i_354_, v_stop_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v_toSignature_358_; lean_object* v_name_359_; uint8_t v___x_360_; 
v___x_357_ = lean_array_uget_borrowed(v_as_353_, v_i_354_);
v_toSignature_358_ = lean_ctor_get(v___x_357_, 0);
v_name_359_ = lean_ctor_get(v_toSignature_358_, 0);
v___x_360_ = lean_name_eq(v_name_359_, v_declName_352_);
if (v___x_360_ == 0)
{
size_t v___x_361_; size_t v___x_362_; 
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_add(v_i_354_, v___x_361_);
v_i_354_ = v___x_362_;
goto _start;
}
else
{
return v___x_360_;
}
}
else
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_352_ = stack[0].m_obj;
lean_object* v_as_353_ = stack[1].m_obj;
size_t v_i_354_ = stack[2].m_num;
size_t v_stop_355_ = stack[3].m_num;
uint8_t v_res_365_;
v_res_365_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_352_, v_as_353_, v_i_354_, v_stop_355_);
stack->m_num = v_res_365_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3___boxed(lean_object* v_declName_366_, lean_object* v_as_367_, lean_object* v_i_368_, lean_object* v_stop_369_){
_start:
{
size_t v_i_boxed_370_; size_t v_stop_boxed_371_; uint8_t v_res_372_; lean_object* v_r_373_; 
v_i_boxed_370_ = lean_unbox_usize(v_i_368_);
lean_dec(v_i_368_);
v_stop_boxed_371_ = lean_unbox_usize(v_stop_369_);
lean_dec(v_stop_369_);
v_res_372_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_366_, v_as_367_, v_i_boxed_370_, v_stop_boxed_371_);
lean_dec_ref(v_as_367_);
lean_dec(v_declName_366_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(uint8_t v_isRoot_374_, uint8_t v___x_375_, lean_object* v_as_376_, size_t v_i_377_, size_t v_stop_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = lean_usize_dec_eq(v_i_377_, v_stop_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; uint8_t v___y_382_; lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_380_ = 1;
v___x_386_ = lean_array_uget_borrowed(v_as_376_, v_i_377_);
v___x_387_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v___x_386_);
if (v___x_387_ == 0)
{
v___y_382_ = v_isRoot_374_;
goto v___jp_381_;
}
else
{
v___y_382_ = v___x_375_;
goto v___jp_381_;
}
v___jp_381_:
{
if (v___y_382_ == 0)
{
size_t v___x_383_; size_t v___x_384_; 
v___x_383_ = ((size_t)1ULL);
v___x_384_ = lean_usize_add(v_i_377_, v___x_383_);
v_i_377_ = v___x_384_;
goto _start;
}
else
{
return v___x_380_;
}
}
}
else
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_isRoot_374_ = stack[0].m_num;
uint8_t v___x_375_ = stack[1].m_num;
lean_object* v_as_376_ = stack[2].m_obj;
size_t v_i_377_ = stack[3].m_num;
size_t v_stop_378_ = stack[4].m_num;
uint8_t v_res_389_;
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_374_, v___x_375_, v_as_376_, v_i_377_, v_stop_378_);
stack->m_num = v_res_389_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object* v_isRoot_390_, lean_object* v___x_391_, lean_object* v_as_392_, lean_object* v_i_393_, lean_object* v_stop_394_){
_start:
{
uint8_t v_isRoot_boxed_395_; uint8_t v___x_15289__boxed_396_; size_t v_i_boxed_397_; size_t v_stop_boxed_398_; uint8_t v_res_399_; lean_object* v_r_400_; 
v_isRoot_boxed_395_ = lean_unbox(v_isRoot_390_);
v___x_15289__boxed_396_ = lean_unbox(v___x_391_);
v_i_boxed_397_ = lean_unbox_usize(v_i_393_);
lean_dec(v_i_393_);
v_stop_boxed_398_ = lean_unbox_usize(v_stop_394_);
lean_dec(v_stop_394_);
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_boxed_395_, v___x_15289__boxed_396_, v_as_392_, v_i_boxed_397_, v_stop_boxed_398_);
lean_dec_ref(v_as_392_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0(void){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = lean_cstr_to_nat("9223372036854775808");
return v___x_401_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(uint8_t v___x_402_, lean_object* v_as_403_, size_t v_i_404_, size_t v_stop_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v___x_413_; 
v___x_413_ = lean_usize_dec_eq(v_i_404_, v_stop_405_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; uint8_t v_a_416_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_414_ = 1;
v___x_422_ = lean_array_uget_borrowed(v_as_403_, v_i_404_);
lean_inc(v___x_422_);
v___x_423_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_422_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_433_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_433_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
uint8_t v___x_428_; 
v___x_428_ = lean_unbox(v_a_424_);
lean_dec(v_a_424_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_box(v___x_414_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_429_);
v___x_431_ = v___x_426_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
else
{
lean_del_object(v___x_426_);
v_a_416_ = v___x_402_;
goto v___jp_415_;
}
}
}
else
{
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_434_; uint8_t v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_423_, 1);
v___x_435_ = lean_unbox(v_a_434_);
lean_dec(v_a_434_);
v_a_416_ = v___x_435_;
goto v___jp_415_;
}
else
{
return v___x_423_;
}
}
v___jp_415_:
{
if (v_a_416_ == 0)
{
size_t v___x_417_; size_t v___x_418_; 
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_add(v_i_404_, v___x_417_);
v_i_404_ = v___x_418_;
goto _start;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_box(v___x_414_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
}
else
{
uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = 0;
v___x_437_ = lean_box(v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_402_ = stack[0].m_num;
lean_object* v_as_403_ = stack[1].m_obj;
size_t v_i_404_ = stack[2].m_num;
size_t v_stop_405_ = stack[3].m_num;
lean_object* v___y_406_ = stack[4].m_obj;
lean_object* v___y_407_ = stack[5].m_obj;
lean_object* v___y_408_ = stack[6].m_obj;
lean_object* v___y_409_ = stack[7].m_obj;
lean_object* v___y_410_ = stack[8].m_obj;
lean_object* v___y_411_ = stack[9].m_obj;
lean_object* v_res_439_;
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___x_402_, v_as_403_, v_i_404_, v_stop_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
stack->m_obj
 = v_res_439_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(lean_object* v_as_440_, size_t v_i_441_, size_t v_stop_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = lean_usize_dec_eq(v_i_441_, v_stop_442_);
if (v___x_454_ == 0)
{
uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = 1;
v___x_456_ = lean_array_uget_borrowed(v_as_440_, v_i_441_);
lean_inc(v___x_456_);
v___x_457_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_456_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_467_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_467_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
uint8_t v___x_462_; 
v___x_462_ = lean_unbox(v_a_458_);
lean_dec(v_a_458_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_box(v___x_455_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_463_);
v___x_465_ = v___x_460_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
else
{
lean_del_object(v___x_460_);
goto v___jp_450_;
}
}
}
else
{
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_477_; 
v_a_468_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_477_ == 0)
{
v___x_470_ = v___x_457_;
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_457_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint8_t v___x_472_; 
v___x_472_ = lean_unbox(v_a_468_);
lean_dec(v_a_468_);
if (v___x_472_ == 0)
{
lean_del_object(v___x_470_);
goto v___jp_450_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = lean_box(v___x_455_);
if (v_isShared_471_ == 0)
{
lean_ctor_set_tag(v___x_470_, 0);
lean_ctor_set(v___x_470_, 0, v___x_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
return v___x_457_;
}
}
}
else
{
uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = 0;
v___x_479_ = lean_box(v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
v___jp_450_:
{
size_t v___x_451_; size_t v___x_452_; 
v___x_451_ = ((size_t)1ULL);
v___x_452_ = lean_usize_add(v_i_441_, v___x_451_);
v_i_441_ = v___x_452_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_440_ = stack[0].m_obj;
size_t v_i_441_ = stack[1].m_num;
size_t v_stop_442_ = stack[2].m_num;
lean_object* v___y_443_ = stack[3].m_obj;
lean_object* v___y_444_ = stack[4].m_obj;
lean_object* v___y_445_ = stack[5].m_obj;
lean_object* v___y_446_ = stack[6].m_obj;
lean_object* v___y_447_ = stack[7].m_obj;
lean_object* v___y_448_ = stack[8].m_obj;
lean_object* v_res_481_;
v_res_481_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_as_440_, v_i_441_, v_stop_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
stack->m_obj
 = v_res_481_;
}
lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t v_isRoot_482_, lean_object* v_v_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
switch(lean_obj_tag(v_v_483_))
{
case 0:
{
lean_object* v_value_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_540_; 
v_value_495_ = lean_ctor_get(v_v_483_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v_v_483_);
if (v_isSharedCheck_540_ == 0)
{
v___x_497_ = v_v_483_;
v_isShared_498_ = v_isSharedCheck_540_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_value_495_);
lean_dec(v_v_483_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_540_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
switch(lean_obj_tag(v_value_495_))
{
case 1:
{
lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_507_; 
lean_del_object(v___x_497_);
v_isSharedCheck_507_ = !lean_is_exclusive(v_value_495_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v_value_495_, 0);
lean_dec(v_unused_508_);
v___x_500_ = v_value_495_;
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
else
{
lean_dec(v_value_495_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint8_t v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_502_ = 1;
v___x_503_ = lean_box(v___x_502_);
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 0);
lean_ctor_set(v___x_500_, 0, v___x_503_);
v___x_505_ = v___x_500_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
case 0:
{
lean_del_object(v___x_497_);
if (v_isRoot_482_ == 0)
{
lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_517_; 
v_isSharedCheck_517_ = !lean_is_exclusive(v_value_495_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_value_495_, 0);
lean_dec(v_unused_518_);
v___x_510_ = v_value_495_;
v_isShared_511_ = v_isSharedCheck_517_;
goto v_resetjp_509_;
}
else
{
lean_dec(v_value_495_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_517_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = 1;
v___x_513_ = lean_box(v___x_512_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_513_);
v___x_515_ = v___x_510_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
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
lean_object* v_val_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_529_; 
v_val_519_ = lean_ctor_get(v_value_495_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_value_495_);
if (v_isSharedCheck_529_ == 0)
{
v___x_521_ = v_value_495_;
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_val_519_);
lean_dec(v_value_495_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_529_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_523_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0, &l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0);
v___x_524_ = lean_nat_dec_le(v___x_523_, v_val_519_);
lean_dec(v_val_519_);
v___x_525_ = lean_box(v___x_524_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_525_);
v___x_527_ = v___x_521_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
default: 
{
lean_dec_ref(v_value_495_);
if (v_isRoot_482_ == 0)
{
uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_530_ = 1;
v___x_531_ = lean_box(v___x_530_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_531_);
v___x_533_ = v___x_497_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
else
{
uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = 0;
v___x_536_ = lean_box(v___x_535_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_536_);
v___x_538_ = v___x_497_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
case 1:
{
if (v_isRoot_482_ == 0)
{
uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = 1;
v___x_542_ = lean_box(v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
else
{
uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = 0;
v___x_545_ = lean_box(v___x_544_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
case 2:
{
lean_object* v_struct_547_; lean_object* v___x_548_; 
v_struct_547_ = lean_ctor_get(v_v_483_, 2);
lean_inc(v_struct_547_);
lean_dec_ref_known(v_v_483_, 3);
v___x_548_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_struct_547_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
return v___x_548_;
}
case 3:
{
lean_object* v_declName_549_; lean_object* v_args_550_; lean_object* v_sccDecls_551_; lean_object* v___x_552_; uint8_t v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; uint8_t v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; uint8_t v___y_606_; uint8_t v___y_610_; uint8_t v___y_611_; uint8_t v___y_615_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_declName_549_ = lean_ctor_get(v_v_483_, 0);
lean_inc(v_declName_549_);
v_args_550_ = lean_ctor_get(v_v_483_, 2);
lean_inc_ref(v_args_550_);
lean_dec_ref_known(v_v_483_, 3);
v_sccDecls_551_ = lean_ctor_get(v_a_484_, 1);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_array_get_size(v_sccDecls_551_);
v___x_635_ = lean_nat_dec_lt(v___x_552_, v___x_634_);
if (v___x_635_ == 0)
{
v___y_615_ = v___x_635_;
goto v___jp_614_;
}
else
{
if (v___x_635_ == 0)
{
v___y_615_ = v___x_635_;
goto v___jp_614_;
}
else
{
size_t v___x_636_; size_t v___x_637_; uint8_t v___x_638_; 
v___x_636_ = ((size_t)0ULL);
v___x_637_ = lean_usize_of_nat(v___x_634_);
v___x_638_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_549_, v_sccDecls_551_, v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
v___y_615_ = v___x_638_;
goto v___jp_614_;
}
else
{
uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec_ref(v_args_550_);
lean_dec(v_declName_549_);
v___x_639_ = 0;
v___x_640_ = lean_box(v___x_639_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
}
v___jp_553_:
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_array_get_size(v_args_550_);
v___x_562_ = lean_nat_dec_lt(v___x_552_, v___x_561_);
if (v___x_562_ == 0)
{
lean_dec_ref(v_args_550_);
goto v___jp_491_;
}
else
{
if (v___x_562_ == 0)
{
lean_dec_ref(v_args_550_);
goto v___jp_491_;
}
else
{
size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_563_ = ((size_t)0ULL);
v___x_564_ = lean_usize_of_nat(v___x_561_);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___y_554_, v_args_550_, v___x_563_, v___x_564_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec_ref(v_args_550_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_575_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_575_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_575_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_575_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
uint8_t v___x_570_; 
v___x_570_ = lean_unbox(v_a_566_);
lean_dec(v_a_566_);
if (v___x_570_ == 0)
{
lean_del_object(v___x_568_);
goto v___jp_491_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_box(v___y_554_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_571_);
v___x_573_ = v___x_568_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
else
{
return v___x_565_;
}
}
}
}
v___jp_576_:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_549_, v___y_583_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_596_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_596_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_596_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
if (lean_obj_tag(v_a_585_) == 1)
{
lean_object* v_val_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_val_589_ = lean_ctor_get(v_a_585_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v_a_585_, 1);
v___x_590_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_589_);
lean_dec(v_val_589_);
v___x_591_ = lean_nat_dec_eq(v___x_590_, v___x_552_);
lean_dec(v___x_590_);
if (v___x_591_ == 0)
{
lean_del_object(v___x_587_);
v___y_554_ = v___y_577_;
v___y_555_ = v___y_578_;
v___y_556_ = v___y_579_;
v___y_557_ = v___y_580_;
v___y_558_ = v___y_581_;
v___y_559_ = v___y_582_;
v___y_560_ = v___y_583_;
goto v___jp_553_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_594_; 
lean_dec_ref(v_args_550_);
v___x_592_ = lean_box(v___y_577_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_592_);
v___x_594_ = v___x_587_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_del_object(v___x_587_);
lean_dec(v_a_585_);
v___y_554_ = v___y_577_;
v___y_555_ = v___y_578_;
v___y_556_ = v___y_579_;
v___y_557_ = v___y_580_;
v___y_558_ = v___y_581_;
v___y_559_ = v___y_582_;
v___y_560_ = v___y_583_;
goto v___jp_553_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v_args_550_);
v_a_597_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_584_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_584_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
v___jp_605_:
{
if (v___y_606_ == 0)
{
v___y_577_ = v___y_606_;
v___y_578_ = v_a_484_;
v___y_579_ = v_a_485_;
v___y_580_ = v_a_486_;
v___y_581_ = v_a_487_;
v___y_582_ = v_a_488_;
v___y_583_ = v_a_489_;
goto v___jp_576_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec_ref(v_args_550_);
lean_dec(v_declName_549_);
v___x_607_ = lean_box(v___y_606_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
v___jp_609_:
{
if (v___y_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec_ref(v_args_550_);
lean_dec(v_declName_549_);
v___x_612_ = lean_box(v___y_610_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
else
{
v___y_606_ = v___y_610_;
goto v___jp_605_;
}
}
v___jp_614_:
{
lean_object* v___x_616_; lean_object* v_env_617_; uint8_t v___x_618_; 
v___x_616_ = lean_st_ref_get(v_a_489_);
v_env_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref(v_env_617_);
lean_dec(v___x_616_);
lean_inc(v_declName_549_);
v___x_618_ = l_Lean_hasNeverExtractAttribute(v_env_617_, v_declName_549_);
if (v___x_618_ == 0)
{
if (v_isRoot_482_ == 0)
{
lean_dec(v_declName_549_);
v___y_554_ = v___x_618_;
v___y_555_ = v_a_484_;
v___y_556_ = v_a_485_;
v___y_557_ = v_a_486_;
v___y_558_ = v_a_487_;
v___y_559_ = v_a_488_;
v___y_560_ = v_a_489_;
goto v___jp_553_;
}
else
{
lean_object* v___x_619_; lean_object* v_env_620_; lean_object* v___x_621_; 
v___x_619_ = lean_st_ref_get(v_a_489_);
v_env_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc_ref(v_env_620_);
lean_dec(v___x_619_);
lean_inc(v_declName_549_);
v___x_621_ = l_Lean_Environment_find_x3f(v_env_620_, v_declName_549_, v___x_618_);
if (lean_obj_tag(v___x_621_) == 1)
{
lean_object* v_val_622_; 
v_val_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_val_622_);
lean_dec_ref_known(v___x_621_, 1);
switch(lean_obj_tag(v_val_622_))
{
case 1:
{
lean_object* v_val_623_; lean_object* v_toConstantVal_624_; lean_object* v_type_625_; uint8_t v___x_626_; 
v_val_623_ = lean_ctor_get(v_val_622_, 0);
lean_inc_ref(v_val_623_);
lean_dec_ref_known(v_val_622_, 1);
v_toConstantVal_624_ = lean_ctor_get(v_val_623_, 0);
lean_inc_ref(v_toConstantVal_624_);
lean_dec_ref(v_val_623_);
v_type_625_ = lean_ctor_get(v_toConstantVal_624_, 2);
lean_inc_ref(v_type_625_);
lean_dec_ref(v_toConstantVal_624_);
v___x_626_ = l_Lean_Expr_isForall(v_type_625_);
lean_dec_ref(v_type_625_);
v___y_610_ = v___x_618_;
v___y_611_ = v___x_626_;
goto v___jp_609_;
}
case 6:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
lean_dec_ref_known(v_val_622_, 1);
v___x_627_ = lean_array_get_size(v_args_550_);
v___x_628_ = lean_nat_dec_lt(v___x_552_, v___x_627_);
if (v___x_628_ == 0)
{
v___y_610_ = v___x_618_;
v___y_611_ = v___x_618_;
goto v___jp_609_;
}
else
{
if (v___x_628_ == 0)
{
v___y_610_ = v___x_618_;
v___y_611_ = v___x_618_;
goto v___jp_609_;
}
else
{
size_t v___x_629_; size_t v___x_630_; uint8_t v___x_631_; 
v___x_629_ = ((size_t)0ULL);
v___x_630_ = lean_usize_of_nat(v___x_627_);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_482_, v___x_618_, v_args_550_, v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
v___y_610_ = v___x_618_;
v___y_611_ = v___x_618_;
goto v___jp_609_;
}
else
{
if (v___x_618_ == 0)
{
v___y_606_ = v___x_618_;
goto v___jp_605_;
}
else
{
v___y_610_ = v___x_618_;
v___y_611_ = v___x_618_;
goto v___jp_609_;
}
}
}
}
}
default: 
{
lean_dec(v_val_622_);
v___y_606_ = v___x_618_;
goto v___jp_605_;
}
}
}
else
{
lean_dec(v___x_621_);
v___y_577_ = v___x_618_;
v___y_578_ = v_a_484_;
v___y_579_ = v_a_485_;
v___y_580_ = v_a_486_;
v___y_581_ = v_a_487_;
v___y_582_ = v_a_488_;
v___y_583_ = v_a_489_;
goto v___jp_576_;
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v_args_550_);
lean_dec(v_declName_549_);
v___x_632_ = lean_box(v___y_615_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
}
default: 
{
lean_object* v_fvarId_642_; lean_object* v_args_643_; lean_object* v___x_644_; 
v_fvarId_642_ = lean_ctor_get(v_v_483_, 0);
lean_inc(v_fvarId_642_);
v_args_643_ = lean_ctor_get(v_v_483_, 1);
lean_inc_ref(v_args_643_);
lean_dec_ref_known(v_v_483_, 2);
v___x_644_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_642_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___y_647_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_array_get_size(v_args_643_);
v___x_659_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v_args_643_);
v___x_660_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_659_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
v___y_647_ = v___x_660_;
goto v___jp_646_;
}
else
{
if (v___x_659_ == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v_args_643_);
v___x_661_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_659_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
v___y_647_ = v___x_661_;
goto v___jp_646_;
}
else
{
size_t v___x_662_; size_t v___x_663_; lean_object* v___x_664_; 
v___x_662_ = ((size_t)0ULL);
v___x_663_ = lean_usize_of_nat(v___x_658_);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_args_643_, v___x_662_, v___x_663_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec_ref(v_args_643_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; uint8_t v___x_666_; lean_object* v___x_667_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v___x_666_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
v___x_667_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_666_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
v___y_647_ = v___x_667_;
goto v___jp_646_;
}
else
{
v___y_647_ = v___x_664_;
goto v___jp_646_;
}
}
}
v___jp_646_:
{
if (lean_obj_tag(v___y_647_) == 0)
{
uint8_t v___x_648_; 
v___x_648_ = lean_unbox(v_a_645_);
if (v___x_648_ == 0)
{
lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_isSharedCheck_655_ = !lean_is_exclusive(v___y_647_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v___y_647_, 0);
lean_dec(v_unused_656_);
v___x_650_ = v___y_647_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_dec(v___y_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v_a_645_);
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_645_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
else
{
lean_dec(v_a_645_);
return v___y_647_;
}
}
else
{
lean_dec(v_a_645_);
return v___y_647_;
}
}
}
else
{
lean_dec_ref(v_args_643_);
return v___x_644_;
}
}
}
v___jp_491_:
{
uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = 1;
v___x_493_ = lean_box(v___x_492_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_isRoot_482_ = stack[0].m_num;
lean_object* v_v_483_ = stack[1].m_obj;
lean_object* v_a_484_ = stack[2].m_obj;
lean_object* v_a_485_ = stack[3].m_obj;
lean_object* v_a_486_ = stack[4].m_obj;
lean_object* v_a_487_ = stack[5].m_obj;
lean_object* v_a_488_ = stack[6].m_obj;
lean_object* v_a_489_ = stack[7].m_obj;
lean_object* v_res_668_;
v_res_668_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v_isRoot_482_, v_v_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
stack->m_obj
 = v_res_668_;
}
lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(lean_object* v_fvarId_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
uint8_t v___x_677_; lean_object* v___x_678_; 
v___x_677_ = 0;
v___x_678_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_677_, v_fvarId_669_, v_a_673_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_692_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_692_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_692_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_692_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
if (lean_obj_tag(v_a_679_) == 1)
{
lean_object* v_val_683_; lean_object* v_value_684_; uint8_t v___x_685_; lean_object* v___x_686_; 
lean_del_object(v___x_681_);
v_val_683_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v_a_679_, 1);
v_value_684_ = lean_ctor_get(v_val_683_, 3);
lean_inc(v_value_684_);
lean_dec(v_val_683_);
v___x_685_ = 0;
v___x_686_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_685_, v_value_684_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_686_;
}
else
{
uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
lean_dec(v_a_679_);
v___x_687_ = 0;
v___x_688_ = lean_box(v___x_687_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_688_);
v___x_690_ = v___x_681_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_a_693_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_678_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_678_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_669_ = stack[0].m_obj;
lean_object* v_a_670_ = stack[1].m_obj;
lean_object* v_a_671_ = stack[2].m_obj;
lean_object* v_a_672_ = stack[3].m_obj;
lean_object* v_a_673_ = stack[4].m_obj;
lean_object* v_a_674_ = stack[5].m_obj;
lean_object* v_a_675_ = stack[6].m_obj;
lean_object* v_res_701_;
v_res_701_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
stack->m_obj
 = v_res_701_;
}
lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object* v_fvarId_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_710_; lean_object* v_fvarDecisionCache_711_; lean_object* v___x_712_; 
v___x_710_ = lean_st_ref_get(v_a_704_);
v_fvarDecisionCache_711_ = lean_ctor_get(v___x_710_, 1);
lean_inc_ref(v_fvarDecisionCache_711_);
lean_dec(v___x_710_);
v___x_712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_fvarDecisionCache_711_, v_fvarId_702_);
lean_dec_ref(v_fvarDecisionCache_711_);
if (lean_obj_tag(v___x_712_) == 1)
{
lean_object* v_val_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_fvarId_702_);
v_val_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_val_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set_tag(v___x_715_, 0);
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_val_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
else
{
lean_object* v___x_721_; 
lean_dec(v___x_712_);
v___x_721_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_741_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_741_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_741_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_741_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v_decls_727_; lean_object* v_fvarDecisionCache_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_740_; 
v___x_726_ = lean_st_ref_take(v_a_704_);
v_decls_727_ = lean_ctor_get(v___x_726_, 0);
v_fvarDecisionCache_728_ = lean_ctor_get(v___x_726_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_740_ == 0)
{
v___x_730_ = v___x_726_;
v_isShared_731_ = v_isSharedCheck_740_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_fvarDecisionCache_728_);
lean_inc(v_decls_727_);
lean_dec(v___x_726_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_740_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
lean_inc(v_a_722_);
v___x_732_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_fvarDecisionCache_728_, v_fvarId_702_, v_a_722_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 1, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_decls_727_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_732_);
v___x_734_ = v_reuseFailAlloc_739_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_st_ref_put(v_a_704_, v___x_734_);
if (v_isShared_725_ == 0)
{
v___x_737_ = v___x_724_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_722_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_702_);
return v___x_721_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_702_ = stack[0].m_obj;
lean_object* v_a_703_ = stack[1].m_obj;
lean_object* v_a_704_ = stack[2].m_obj;
lean_object* v_a_705_ = stack[3].m_obj;
lean_object* v_a_706_ = stack[4].m_obj;
lean_object* v_a_707_ = stack[5].m_obj;
lean_object* v_a_708_ = stack[6].m_obj;
lean_object* v_res_742_;
v_res_742_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
stack->m_obj
 = v_res_742_;
}
lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object* v_arg_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
if (lean_obj_tag(v_arg_743_) == 1)
{
lean_object* v_fvarId_751_; lean_object* v___x_752_; 
v_fvarId_751_ = lean_ctor_get(v_arg_743_, 0);
lean_inc(v_fvarId_751_);
lean_dec_ref_known(v_arg_743_, 1);
v___x_752_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_751_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_752_;
}
else
{
uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v_arg_743_);
v___x_753_ = 1;
v___x_754_ = lean_box(v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_743_ = stack[0].m_obj;
lean_object* v_a_744_ = stack[1].m_obj;
lean_object* v_a_745_ = stack[2].m_obj;
lean_object* v_a_746_ = stack[3].m_obj;
lean_object* v_a_747_ = stack[4].m_obj;
lean_object* v_a_748_ = stack[5].m_obj;
lean_object* v_a_749_ = stack[6].m_obj;
lean_object* v_res_756_;
v_res_756_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v_arg_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
stack->m_obj
 = v_res_756_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object* v_arg_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v_arg_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(lean_object* v_fvarId_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_fvarId_766_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object* v_fvarId_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object* v___x_784_, lean_object* v_as_785_, lean_object* v_i_786_, lean_object* v_stop_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
uint8_t v___x_15354__boxed_795_; size_t v_i_boxed_796_; size_t v_stop_boxed_797_; lean_object* v_res_798_; 
v___x_15354__boxed_795_ = lean_unbox(v___x_784_);
v_i_boxed_796_ = lean_unbox_usize(v_i_786_);
lean_dec(v_i_786_);
v_stop_boxed_797_ = lean_unbox_usize(v_stop_787_);
lean_dec(v_stop_787_);
v_res_798_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___x_15354__boxed_795_, v_as_785_, v_i_boxed_796_, v_stop_boxed_797_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec_ref(v_as_785_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(lean_object* v_as_799_, lean_object* v_i_800_, lean_object* v_stop_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
size_t v_i_boxed_809_; size_t v_stop_boxed_810_; lean_object* v_res_811_; 
v_i_boxed_809_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_stop_boxed_810_ = lean_unbox_usize(v_stop_801_);
lean_dec(v_stop_801_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_as_799_, v_i_boxed_809_, v_stop_boxed_810_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec_ref(v_as_799_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object* v_isRoot_812_, lean_object* v_v_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
uint8_t v_isRoot_boxed_821_; lean_object* v_res_822_; 
v_isRoot_boxed_821_ = lean_unbox(v_isRoot_812_);
v_res_822_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v_isRoot_boxed_821_, v_v_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object* v_00_u03b2_823_, lean_object* v_m_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_824_, v_a_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___boxed(lean_object* v_00_u03b2_827_, lean_object* v_m_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(v_00_u03b2_827_, v_m_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_m_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(lean_object* v_00_u03b2_831_, lean_object* v_m_832_, lean_object* v_a_833_, lean_object* v_b_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_m_832_, v_a_833_, v_b_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(lean_object* v_00_u03b2_836_, lean_object* v_a_837_, lean_object* v_x_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_837_, v_x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___boxed(lean_object* v_00_u03b2_840_, lean_object* v_a_841_, lean_object* v_x_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(v_00_u03b2_840_, v_a_841_, v_x_842_);
lean_dec(v_x_842_);
lean_dec(v_a_841_);
return v_res_843_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(lean_object* v_00_u03b2_844_, lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_845_ = stack[1].m_obj;
lean_object* v_x_846_ = stack[2].m_obj;
uint8_t v_res_848_;
v_res_848_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(lean_box(0), v_a_845_, v_x_846_);
stack->m_num = v_res_848_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___boxed(lean_object* v_00_u03b2_849_, lean_object* v_a_850_, lean_object* v_x_851_){
_start:
{
uint8_t v_res_852_; lean_object* v_r_853_; 
v_res_852_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(v_00_u03b2_849_, v_a_850_, v_x_851_);
lean_dec(v_x_851_);
lean_dec(v_a_850_);
v_r_853_ = lean_box(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10(lean_object* v_00_u03b2_854_, lean_object* v_data_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_data_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11(lean_object* v_00_u03b2_857_, lean_object* v_a_858_, lean_object* v_b_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_858_, v_b_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_862_, lean_object* v_i_863_, lean_object* v_source_864_, lean_object* v_target_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v_i_863_, v_source_864_, v_target_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_x_868_, v_x_869_);
return v___x_870_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(lean_object* v_prevArrayId_876_, lean_object* v_decl_877_, lean_object* v_k_878_, lean_object* v_illegalSet_879_, lean_object* v_size_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_decl_892_; lean_object* v_k_893_; lean_object* v_illegalSet_894_; lean_object* v_zero_902_; uint8_t v_isZero_903_; 
v_zero_902_ = lean_unsigned_to_nat(0u);
v_isZero_903_ = lean_nat_dec_eq(v_size_880_, v_zero_902_);
if (v_isZero_903_ == 1)
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec(v_size_880_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
lean_dec(v_prevArrayId_876_);
v___x_904_ = lean_box(0);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
else
{
lean_object* v_value_906_; 
v_value_906_ = lean_ctor_get(v_decl_877_, 3);
if (lean_obj_tag(v_value_906_) == 3)
{
lean_object* v_declName_907_; 
v_declName_907_ = lean_ctor_get(v_value_906_, 0);
if (lean_obj_tag(v_declName_907_) == 1)
{
lean_object* v_pre_908_; 
v_pre_908_ = lean_ctor_get(v_declName_907_, 0);
if (lean_obj_tag(v_pre_908_) == 1)
{
lean_object* v_pre_909_; 
v_pre_909_ = lean_ctor_get(v_pre_908_, 0);
if (lean_obj_tag(v_pre_909_) == 0)
{
lean_object* v_fvarId_910_; lean_object* v_args_911_; lean_object* v_str_912_; lean_object* v_str_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_fvarId_910_ = lean_ctor_get(v_decl_877_, 0);
v_args_911_ = lean_ctor_get(v_value_906_, 2);
v_str_912_ = lean_ctor_get(v_declName_907_, 1);
v_str_913_ = lean_ctor_get(v_pre_908_, 1);
v___x_914_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_915_ = lean_string_dec_eq(v_str_913_, v___x_914_);
if (v___x_915_ == 0)
{
lean_dec(v_size_880_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
lean_dec(v_prevArrayId_876_);
goto v___jp_888_;
}
else
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_917_ = lean_string_dec_eq(v_str_912_, v___x_916_);
if (v___x_917_ == 0)
{
lean_dec(v_size_880_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
lean_dec(v_prevArrayId_876_);
goto v___jp_888_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_918_ = lean_array_get_size(v_args_911_);
v___x_919_ = lean_unsigned_to_nat(3u);
v___x_920_ = lean_nat_dec_eq(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_dec(v_size_880_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
lean_dec(v_prevArrayId_876_);
goto v___jp_888_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_unsigned_to_nat(1u);
v___x_922_ = lean_array_fget(v_args_911_, v___x_921_);
if (lean_obj_tag(v___x_922_) == 1)
{
lean_object* v_fvarId_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_1040_; 
v_fvarId_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_1040_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_fvarId_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_1040_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
uint8_t v___x_927_; 
v___x_927_ = l_Lean_instBEqFVarId_beq(v_fvarId_923_, v_prevArrayId_876_);
lean_dec(v_prevArrayId_876_);
lean_dec(v_fvarId_923_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_930_; 
lean_dec(v_size_880_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
v___x_928_ = lean_box(0);
if (v_isShared_926_ == 0)
{
lean_ctor_set_tag(v___x_925_, 0);
lean_ctor_set(v___x_925_, 0, v___x_928_);
v___x_930_ = v___x_925_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
else
{
lean_object* v_n_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
lean_del_object(v___x_925_);
v_n_932_ = lean_nat_sub(v_size_880_, v___x_921_);
lean_dec(v_size_880_);
v___x_933_ = lean_unsigned_to_nat(2u);
v___x_934_ = lean_array_fget_borrowed(v_args_911_, v___x_933_);
lean_inc(v___x_934_);
v___x_935_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_934_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_1031_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_1031_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_1031_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
uint8_t v___x_940_; 
v___x_940_ = lean_unbox(v_a_936_);
lean_dec(v_a_936_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec(v_n_932_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
v___x_941_ = lean_box(0);
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
else
{
uint8_t v___x_945_; 
v___x_945_ = lean_nat_dec_eq(v_n_932_, v_zero_902_);
if (v___x_945_ == 0)
{
lean_inc(v_fvarId_910_);
lean_dec_ref(v_decl_877_);
if (lean_obj_tag(v_k_878_) == 0)
{
lean_object* v_decl_946_; lean_object* v_k_947_; lean_object* v___x_948_; 
lean_del_object(v___x_938_);
v_decl_946_ = lean_ctor_get(v_k_878_, 0);
lean_inc_ref(v_decl_946_);
v_k_947_ = lean_ctor_get(v_k_878_, 1);
lean_inc_ref(v_k_947_);
lean_dec_ref_known(v_k_878_, 2);
lean_inc(v_fvarId_910_);
v___x_948_ = l_Lean_FVarIdSet_insert(v_illegalSet_879_, v_fvarId_910_);
v_prevArrayId_876_ = v_fvarId_910_;
v_decl_877_ = v_decl_946_;
v_k_878_ = v_k_947_;
v_illegalSet_879_ = v___x_948_;
v_size_880_ = v_n_932_;
goto _start;
}
else
{
lean_object* v___x_950_; lean_object* v___x_952_; 
lean_dec(v_n_932_);
lean_dec(v_fvarId_910_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
v___x_950_ = lean_box(0);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_950_);
v___x_952_ = v___x_938_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
else
{
lean_del_object(v___x_938_);
lean_dec(v_n_932_);
if (lean_obj_tag(v_k_878_) == 0)
{
lean_object* v_decl_954_; lean_object* v_value_955_; 
v_decl_954_ = lean_ctor_get(v_k_878_, 0);
lean_inc_ref(v_decl_954_);
v_value_955_ = lean_ctor_get(v_decl_954_, 3);
lean_inc(v_value_955_);
if (lean_obj_tag(v_value_955_) == 3)
{
lean_object* v_declName_956_; 
v_declName_956_ = lean_ctor_get(v_value_955_, 0);
lean_inc(v_declName_956_);
if (lean_obj_tag(v_declName_956_) == 1)
{
lean_object* v_pre_957_; 
v_pre_957_ = lean_ctor_get(v_declName_956_, 0);
lean_inc(v_pre_957_);
if (lean_obj_tag(v_pre_957_) == 1)
{
lean_object* v_pre_958_; 
v_pre_958_ = lean_ctor_get(v_pre_957_, 0);
lean_inc(v_pre_958_);
if (lean_obj_tag(v_pre_958_) == 0)
{
lean_object* v_k_959_; lean_object* v_fvarId_960_; lean_object* v_binderName_961_; lean_object* v_type_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1029_; 
v_k_959_ = lean_ctor_get(v_k_878_, 1);
v_fvarId_960_ = lean_ctor_get(v_decl_954_, 0);
v_binderName_961_ = lean_ctor_get(v_decl_954_, 1);
v_type_962_ = lean_ctor_get(v_decl_954_, 2);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_decl_954_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v_decl_954_, 3);
lean_dec(v_unused_1030_);
v___x_964_ = v_decl_954_;
v_isShared_965_ = v_isSharedCheck_1029_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_type_962_);
lean_inc(v_binderName_961_);
lean_inc(v_fvarId_960_);
lean_dec(v_decl_954_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1029_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_us_966_; lean_object* v_args_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_1027_; 
v_us_966_ = lean_ctor_get(v_value_955_, 1);
v_args_967_ = lean_ctor_get(v_value_955_, 2);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_value_955_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v_value_955_, 0);
lean_dec(v_unused_1028_);
v___x_969_ = v_value_955_;
v_isShared_970_ = v_isSharedCheck_1027_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_args_967_);
lean_inc(v_us_966_);
lean_dec(v_value_955_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_1027_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_str_971_; lean_object* v_str_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_str_971_ = lean_ctor_get(v_declName_956_, 1);
lean_inc_ref(v_str_971_);
lean_dec_ref_known(v_declName_956_, 2);
v_str_972_ = lean_ctor_get(v_pre_957_, 1);
lean_inc_ref(v_str_972_);
lean_dec_ref_known(v_pre_957_, 2);
v___x_973_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2));
v___x_974_ = lean_string_dec_eq(v_str_972_, v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_975_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3));
v___x_976_ = lean_string_dec_eq(v_str_972_, v___x_975_);
lean_dec_ref(v_str_972_);
if (v___x_976_ == 0)
{
lean_dec_ref(v_str_971_);
lean_del_object(v___x_969_);
lean_dec_ref(v_args_967_);
lean_dec(v_us_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_type_962_);
lean_dec(v_binderName_961_);
lean_dec(v_fvarId_960_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
else
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_978_ = lean_string_dec_eq(v_str_971_, v___x_977_);
lean_dec_ref(v_str_971_);
if (v___x_978_ == 0)
{
lean_del_object(v___x_969_);
lean_dec_ref(v_args_967_);
lean_dec(v_us_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_type_962_);
lean_dec(v_binderName_961_);
lean_dec(v_fvarId_960_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
else
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = lean_array_get_size(v_args_967_);
v___x_980_ = lean_nat_dec_eq(v___x_979_, v___x_921_);
if (v___x_980_ == 0)
{
lean_del_object(v___x_969_);
lean_dec_ref(v_args_967_);
lean_dec(v_us_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_type_962_);
lean_dec(v_binderName_961_);
lean_dec(v_fvarId_960_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
else
{
lean_object* v___x_981_; 
v___x_981_ = lean_array_fget(v_args_967_, v_zero_902_);
lean_dec_ref(v_args_967_);
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
v___x_986_ = l_Lean_instBEqFVarId_beq(v_fvarId_982_, v_fvarId_910_);
if (v___x_986_ == 0)
{
lean_del_object(v___x_984_);
lean_dec(v_fvarId_982_);
lean_del_object(v___x_969_);
lean_dec(v_us_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_type_962_);
lean_dec(v_binderName_961_);
lean_dec(v_fvarId_960_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
lean_inc_ref(v_k_959_);
lean_inc(v_fvarId_910_);
lean_dec_ref_known(v_k_878_, 2);
lean_dec_ref(v_decl_877_);
v___x_987_ = l_Lean_Name_str___override(v_pre_958_, v___x_975_);
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
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_921_);
v___x_992_ = lean_array_push(v___x_991_, v___x_990_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 2, v___x_992_);
lean_ctor_set(v___x_969_, 0, v___x_988_);
v___x_994_ = v___x_969_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_us_966_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v___x_992_);
v___x_994_ = v_reuseFailAlloc_999_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_996_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 3, v___x_994_);
v___x_996_ = v___x_964_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_fvarId_960_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_binderName_961_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_type_962_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v___x_994_);
v___x_996_ = v_reuseFailAlloc_998_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_FVarIdSet_insert(v_illegalSet_879_, v_fvarId_910_);
v_decl_892_ = v___x_996_;
v_k_893_ = v_k_959_;
v_illegalSet_894_ = v___x_997_;
goto v___jp_891_;
}
}
}
}
}
}
else
{
lean_dec(v___x_981_);
lean_del_object(v___x_969_);
lean_dec(v_us_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_type_962_);
lean_dec(v_binderName_961_);
lean_dec(v_fvarId_960_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
}
}
}
}
else
{
lean_object* v___x_1002_; uint8_t v___x_1003_; 
lean_dec_ref(v_str_972_);
v___x_1002_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_1003_ = lean_string_dec_eq(v_str_971_, v___x_1002_);
lean_dec_ref(v_str_971_);
if (v___x_1003_ == 0)
{
lean_del_object(v___x_969_);
lean_dec_ref(v_args_967_);
lean_dec(v_us_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_type_962_);
lean_dec(v_binderName_961_);
lean_dec(v_fvarId_960_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
else
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_array_get_size(v_args_967_);
v___x_1005_ = lean_nat_dec_eq(v___x_1004_, v___x_921_);
if (v___x_1005_ == 0)
{
lean_del_object(v___x_969_);
lean_dec_ref(v_args_967_);
lean_dec(v_us_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_type_962_);
lean_dec(v_binderName_961_);
lean_dec(v_fvarId_960_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_array_fget(v_args_967_, v_zero_902_);
lean_dec_ref(v_args_967_);
if (lean_obj_tag(v___x_1006_) == 1)
{
lean_object* v_fvarId_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1026_; 
v_fvarId_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1026_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_fvarId_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1026_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Lean_instBEqFVarId_beq(v_fvarId_1007_, v_fvarId_910_);
if (v___x_1011_ == 0)
{
lean_del_object(v___x_1009_);
lean_dec(v_fvarId_1007_);
lean_del_object(v___x_969_);
lean_dec(v_us_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_type_962_);
lean_dec(v_binderName_961_);
lean_dec(v_fvarId_960_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
lean_inc_ref(v_k_959_);
lean_inc(v_fvarId_910_);
lean_dec_ref_known(v_k_878_, 2);
lean_dec_ref(v_decl_877_);
v___x_1012_ = l_Lean_Name_str___override(v_pre_958_, v___x_973_);
v___x_1013_ = l_Lean_Name_str___override(v___x_1012_, v___x_1002_);
if (v_isShared_1010_ == 0)
{
v___x_1015_ = v___x_1009_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_fvarId_1007_);
v___x_1015_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1016_ = lean_mk_empty_array_with_capacity(v___x_921_);
v___x_1017_ = lean_array_push(v___x_1016_, v___x_1015_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 2, v___x_1017_);
lean_ctor_set(v___x_969_, 0, v___x_1013_);
v___x_1019_ = v___x_969_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_us_966_);
lean_ctor_set(v_reuseFailAlloc_1024_, 2, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 3, v___x_1019_);
v___x_1021_ = v___x_964_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_fvarId_960_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_binderName_961_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v_type_962_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_FVarIdSet_insert(v_illegalSet_879_, v_fvarId_910_);
v_decl_892_ = v___x_1021_;
v_k_893_ = v_k_959_;
v_illegalSet_894_ = v___x_1022_;
goto v___jp_891_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1006_);
lean_del_object(v___x_969_);
lean_dec(v_us_966_);
lean_del_object(v___x_964_);
lean_dec_ref(v_type_962_);
lean_dec(v_binderName_961_);
lean_dec(v_fvarId_960_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
}
}
}
}
}
}
else
{
lean_dec(v_pre_958_);
lean_dec_ref_known(v_pre_957_, 2);
lean_dec_ref_known(v_declName_956_, 2);
lean_dec_ref_known(v_value_955_, 3);
lean_dec_ref(v_decl_954_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
}
else
{
lean_dec_ref_known(v_declName_956_, 2);
lean_dec(v_pre_957_);
lean_dec_ref_known(v_value_955_, 3);
lean_dec_ref(v_decl_954_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
}
else
{
lean_dec(v_declName_956_);
lean_dec_ref_known(v_value_955_, 3);
lean_dec_ref(v_decl_954_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
}
else
{
lean_dec(v_value_955_);
lean_dec_ref(v_decl_954_);
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
}
else
{
v_decl_892_ = v_decl_877_;
v_k_893_ = v_k_878_;
v_illegalSet_894_ = v_illegalSet_879_;
goto v___jp_891_;
}
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_n_932_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
v_a_1032_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_935_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_935_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
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
}
}
else
{
lean_dec(v___x_922_);
lean_dec(v_size_880_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
lean_dec(v_prevArrayId_876_);
goto v___jp_888_;
}
}
}
}
}
else
{
lean_dec(v_size_880_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
lean_dec(v_prevArrayId_876_);
goto v___jp_888_;
}
}
else
{
lean_dec(v_size_880_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
lean_dec(v_prevArrayId_876_);
goto v___jp_888_;
}
}
else
{
lean_dec(v_size_880_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
lean_dec(v_prevArrayId_876_);
goto v___jp_888_;
}
}
else
{
lean_dec(v_size_880_);
lean_dec(v_illegalSet_879_);
lean_dec_ref(v_k_878_);
lean_dec_ref(v_decl_877_);
lean_dec(v_prevArrayId_876_);
goto v___jp_888_;
}
}
v___jp_888_:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_box(0);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
v___jp_891_:
{
uint8_t v___x_895_; uint8_t v___x_896_; 
v___x_895_ = 0;
v___x_896_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_895_, v_k_893_, v_illegalSet_894_);
lean_dec(v_illegalSet_894_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_897_, 0, v_decl_892_);
lean_ctor_set(v___x_897_, 1, v_k_893_);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref(v_k_893_);
lean_dec_ref(v_decl_892_);
v___x_900_ = lean_box(0);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain_0interp(lean_interpreter_value* stack)
{
lean_object* v_prevArrayId_876_ = stack[0].m_obj;
lean_object* v_decl_877_ = stack[1].m_obj;
lean_object* v_k_878_ = stack[2].m_obj;
lean_object* v_illegalSet_879_ = stack[3].m_obj;
lean_object* v_size_880_ = stack[4].m_obj;
lean_object* v_a_881_ = stack[5].m_obj;
lean_object* v_a_882_ = stack[6].m_obj;
lean_object* v_a_883_ = stack[7].m_obj;
lean_object* v_a_884_ = stack[8].m_obj;
lean_object* v_a_885_ = stack[9].m_obj;
lean_object* v_a_886_ = stack[10].m_obj;
lean_object* v_res_1041_;
v_res_1041_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_prevArrayId_876_, v_decl_877_, v_k_878_, v_illegalSet_879_, v_size_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
stack->m_obj
 = v_res_1041_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___boxed(lean_object* v_prevArrayId_1042_, lean_object* v_decl_1043_, lean_object* v_k_1044_, lean_object* v_illegalSet_1045_, lean_object* v_size_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_prevArrayId_1042_, v_decl_1043_, v_k_1044_, v_illegalSet_1045_, v_size_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
return v_res_1054_;
}
}
lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(lean_object* v_decl_1057_, lean_object* v_k_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_value_1075_; 
v_value_1075_ = lean_ctor_get(v_decl_1057_, 3);
if (lean_obj_tag(v_value_1075_) == 3)
{
lean_object* v_declName_1076_; 
v_declName_1076_ = lean_ctor_get(v_value_1075_, 0);
if (lean_obj_tag(v_declName_1076_) == 1)
{
lean_object* v_pre_1077_; 
v_pre_1077_ = lean_ctor_get(v_declName_1076_, 0);
if (lean_obj_tag(v_pre_1077_) == 1)
{
lean_object* v_pre_1078_; 
v_pre_1078_ = lean_ctor_get(v_pre_1077_, 0);
if (lean_obj_tag(v_pre_1078_) == 0)
{
lean_object* v_args_1079_; lean_object* v_str_1080_; lean_object* v_str_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_args_1079_ = lean_ctor_get(v_value_1075_, 2);
v_str_1080_ = lean_ctor_get(v_declName_1076_, 1);
v_str_1081_ = lean_ctor_get(v_pre_1077_, 1);
v___x_1082_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1083_ = lean_string_dec_eq(v_str_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1072_;
}
else
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_1085_ = lean_string_dec_eq(v_str_1080_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1072_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1086_ = lean_array_get_size(v_args_1079_);
v___x_1087_ = lean_unsigned_to_nat(3u);
v___x_1088_ = lean_nat_dec_eq(v___x_1086_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1072_;
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_array_fget_borrowed(v_args_1079_, v___x_1089_);
if (lean_obj_tag(v___x_1090_) == 1)
{
lean_object* v_fvarId_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; 
v_fvarId_1091_ = lean_ctor_get(v___x_1090_, 0);
v___x_1092_ = lean_box(1);
v___x_1093_ = 0;
v___x_1094_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_1093_, v_fvarId_1091_, v_a_1062_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1149_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1149_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1149_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
if (lean_obj_tag(v_a_1095_) == 1)
{
lean_object* v_val_1099_; lean_object* v_fvarId_1100_; lean_object* v_value_1101_; lean_object* v_sizeFVar_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; 
lean_del_object(v___x_1097_);
v_val_1099_ = lean_ctor_get(v_a_1095_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v_a_1095_, 1);
v_fvarId_1100_ = lean_ctor_get(v_val_1099_, 0);
lean_inc(v_fvarId_1100_);
v_value_1101_ = lean_ctor_get(v_val_1099_, 3);
lean_inc(v_value_1101_);
lean_dec(v_val_1099_);
if (lean_obj_tag(v_value_1101_) == 3)
{
lean_object* v_declName_1124_; 
v_declName_1124_ = lean_ctor_get(v_value_1101_, 0);
lean_inc(v_declName_1124_);
if (lean_obj_tag(v_declName_1124_) == 1)
{
lean_object* v_pre_1125_; 
v_pre_1125_ = lean_ctor_get(v_declName_1124_, 0);
lean_inc(v_pre_1125_);
if (lean_obj_tag(v_pre_1125_) == 1)
{
lean_object* v_pre_1126_; 
v_pre_1126_ = lean_ctor_get(v_pre_1125_, 0);
if (lean_obj_tag(v_pre_1126_) == 0)
{
lean_object* v_args_1127_; lean_object* v_str_1128_; lean_object* v_str_1129_; uint8_t v___x_1130_; 
v_args_1127_ = lean_ctor_get(v_value_1101_, 2);
lean_inc_ref(v_args_1127_);
lean_dec_ref_known(v_value_1101_, 3);
v_str_1128_ = lean_ctor_get(v_declName_1124_, 1);
lean_inc_ref(v_str_1128_);
lean_dec_ref_known(v_declName_1124_, 2);
v_str_1129_ = lean_ctor_get(v_pre_1125_, 1);
lean_inc_ref(v_str_1129_);
lean_dec_ref_known(v_pre_1125_, 2);
v___x_1130_ = lean_string_dec_eq(v_str_1129_, v___x_1082_);
lean_dec_ref(v_str_1129_);
if (v___x_1130_ == 0)
{
lean_dec_ref(v_str_1128_);
lean_dec_ref(v_args_1127_);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1069_;
}
else
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1132_ = lean_string_dec_eq(v_str_1128_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1134_ = lean_string_dec_eq(v_str_1128_, v___x_1133_);
lean_dec_ref(v_str_1128_);
if (v___x_1134_ == 0)
{
lean_dec_ref(v_args_1127_);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1069_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1135_ = lean_array_get_size(v_args_1127_);
v___x_1136_ = lean_unsigned_to_nat(2u);
v___x_1137_ = lean_nat_dec_eq(v___x_1135_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_dec_ref(v_args_1127_);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1069_;
}
else
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_array_fget(v_args_1127_, v___x_1089_);
lean_dec_ref(v_args_1127_);
if (lean_obj_tag(v___x_1138_) == 1)
{
lean_object* v_fvarId_1139_; 
v_fvarId_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_fvarId_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v_sizeFVar_1103_ = v_fvarId_1139_;
v___y_1104_ = v_a_1059_;
v___y_1105_ = v_a_1060_;
v___y_1106_ = v_a_1061_;
v___y_1107_ = v_a_1062_;
v___y_1108_ = v_a_1063_;
v___y_1109_ = v_a_1064_;
goto v___jp_1102_;
}
else
{
lean_dec(v___x_1138_);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1069_;
}
}
}
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
lean_dec_ref(v_str_1128_);
v___x_1140_ = lean_array_get_size(v_args_1127_);
v___x_1141_ = lean_unsigned_to_nat(2u);
v___x_1142_ = lean_nat_dec_eq(v___x_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_dec_ref(v_args_1127_);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1069_;
}
else
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_array_fget(v_args_1127_, v___x_1089_);
lean_dec_ref(v_args_1127_);
if (lean_obj_tag(v___x_1143_) == 1)
{
lean_object* v_fvarId_1144_; 
v_fvarId_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_fvarId_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v_sizeFVar_1103_ = v_fvarId_1144_;
v___y_1104_ = v_a_1059_;
v___y_1105_ = v_a_1060_;
v___y_1106_ = v_a_1061_;
v___y_1107_ = v_a_1062_;
v___y_1108_ = v_a_1063_;
v___y_1109_ = v_a_1064_;
goto v___jp_1102_;
}
else
{
lean_dec(v___x_1143_);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1069_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1125_, 2);
lean_dec_ref_known(v_declName_1124_, 2);
lean_dec_ref_known(v_value_1101_, 3);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1069_;
}
}
else
{
lean_dec_ref_known(v_declName_1124_, 2);
lean_dec(v_pre_1125_);
lean_dec_ref_known(v_value_1101_, 3);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1069_;
}
}
else
{
lean_dec(v_declName_1124_);
lean_dec_ref_known(v_value_1101_, 3);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1069_;
}
}
else
{
lean_dec(v_value_1101_);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1069_;
}
v___jp_1102_:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1093_, v_sizeFVar_1103_, v___y_1107_);
lean_dec(v_sizeFVar_1103_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
if (lean_obj_tag(v_a_1111_) == 1)
{
lean_object* v_val_1112_; 
v_val_1112_ = lean_ctor_get(v_a_1111_, 0);
lean_inc(v_val_1112_);
lean_dec_ref_known(v_a_1111_, 1);
if (lean_obj_tag(v_val_1112_) == 0)
{
lean_object* v_value_1113_; 
v_value_1113_ = lean_ctor_get(v_val_1112_, 0);
lean_inc_ref(v_value_1113_);
lean_dec_ref_known(v_val_1112_, 1);
if (lean_obj_tag(v_value_1113_) == 0)
{
lean_object* v_val_1114_; lean_object* v___x_1115_; 
v_val_1114_ = lean_ctor_get(v_value_1113_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v_value_1113_, 1);
v___x_1115_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_fvarId_1100_, v_decl_1057_, v_k_1058_, v___x_1092_, v_val_1114_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
return v___x_1115_;
}
else
{
lean_dec_ref(v_value_1113_);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1066_;
}
}
else
{
lean_dec(v_val_1112_);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1066_;
}
}
else
{
lean_dec(v_a_1111_);
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1066_;
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v_fvarId_1100_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
v_a_1116_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1110_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1110_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
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
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v_a_1095_);
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
v___x_1145_ = lean_box(0);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1145_);
v___x_1147_ = v___x_1097_;
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
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
v_a_1150_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1094_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1094_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1072_;
}
}
}
}
}
else
{
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1072_;
}
}
else
{
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1072_;
}
}
else
{
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1072_;
}
}
else
{
lean_dec_ref(v_k_1058_);
lean_dec_ref(v_decl_1057_);
goto v___jp_1072_;
}
v___jp_1066_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
v___jp_1069_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
v___jp_1072_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1057_ = stack[0].m_obj;
lean_object* v_k_1058_ = stack[1].m_obj;
lean_object* v_a_1059_ = stack[2].m_obj;
lean_object* v_a_1060_ = stack[3].m_obj;
lean_object* v_a_1061_ = stack[4].m_obj;
lean_object* v_a_1062_ = stack[5].m_obj;
lean_object* v_a_1063_ = stack[6].m_obj;
lean_object* v_a_1064_ = stack[7].m_obj;
lean_object* v_res_1158_;
v_res_1158_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1057_, v_k_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
stack->m_obj
 = v_res_1158_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___boxed(lean_object* v_decl_1159_, lean_object* v_k_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1159_, v_k_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
return v_res_1168_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
return v___x_1173_;
}
}
lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(lean_object* v_env_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v_nextMacroScope_1178_; lean_object* v_ngen_1179_; lean_object* v_auxDeclNGen_1180_; lean_object* v_traceState_1181_; lean_object* v_recordedDeps_1182_; lean_object* v_messages_1183_; lean_object* v_infoState_1184_; lean_object* v_snapshotTasks_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1196_; 
v___x_1177_ = lean_st_ref_take(v___y_1175_);
v_nextMacroScope_1178_ = lean_ctor_get(v___x_1177_, 1);
v_ngen_1179_ = lean_ctor_get(v___x_1177_, 2);
v_auxDeclNGen_1180_ = lean_ctor_get(v___x_1177_, 3);
v_traceState_1181_ = lean_ctor_get(v___x_1177_, 4);
v_recordedDeps_1182_ = lean_ctor_get(v___x_1177_, 6);
v_messages_1183_ = lean_ctor_get(v___x_1177_, 7);
v_infoState_1184_ = lean_ctor_get(v___x_1177_, 8);
v_snapshotTasks_1185_ = lean_ctor_get(v___x_1177_, 9);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; lean_object* v_unused_1198_; 
v_unused_1197_ = lean_ctor_get(v___x_1177_, 5);
lean_dec(v_unused_1197_);
v_unused_1198_ = lean_ctor_get(v___x_1177_, 0);
lean_dec(v_unused_1198_);
v___x_1187_ = v___x_1177_;
v_isShared_1188_ = v_isSharedCheck_1196_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_snapshotTasks_1185_);
lean_inc(v_infoState_1184_);
lean_inc(v_messages_1183_);
lean_inc(v_recordedDeps_1182_);
lean_inc(v_traceState_1181_);
lean_inc(v_auxDeclNGen_1180_);
lean_inc(v_ngen_1179_);
lean_inc(v_nextMacroScope_1178_);
lean_dec(v___x_1177_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1196_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 5, v___x_1190_);
lean_ctor_set(v___x_1187_, 0, v_env_1174_);
v___x_1192_ = v___x_1187_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_env_1174_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_nextMacroScope_1178_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_ngen_1179_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v_auxDeclNGen_1180_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v_traceState_1181_);
lean_ctor_set(v_reuseFailAlloc_1195_, 5, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1195_, 6, v_recordedDeps_1182_);
lean_ctor_set(v_reuseFailAlloc_1195_, 7, v_messages_1183_);
lean_ctor_set(v_reuseFailAlloc_1195_, 8, v_infoState_1184_);
lean_ctor_set(v_reuseFailAlloc_1195_, 9, v_snapshotTasks_1185_);
v___x_1192_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_st_ref_put(v___y_1175_, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1189_);
return v___x_1194_;
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1174_ = stack[0].m_obj;
lean_object* v___y_1175_ = stack[1].m_obj;
lean_object* v_res_1199_;
v_res_1199_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1174_, v___y_1175_);
stack->m_obj
 = v_res_1199_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___boxed(lean_object* v_env_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1200_, v___y_1201_);
lean_dec(v___y_1201_);
return v_res_1203_;
}
}
lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(lean_object* v_env_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1204_, v___y_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1204_ = stack[0].m_obj;
lean_object* v___y_1205_ = stack[1].m_obj;
lean_object* v___y_1206_ = stack[2].m_obj;
lean_object* v___y_1207_ = stack[3].m_obj;
lean_object* v___y_1208_ = stack[4].m_obj;
lean_object* v___y_1209_ = stack[5].m_obj;
lean_object* v___y_1210_ = stack[6].m_obj;
lean_object* v_res_1213_;
v_res_1213_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_env_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
stack->m_obj
 = v_res_1213_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(lean_object* v_env_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_env_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1222_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(size_t v_sz_1223_, size_t v_i_1224_, lean_object* v_bs_1225_, uint8_t v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
uint8_t v___x_1233_; 
v___x_1233_ = lean_usize_dec_lt(v_i_1224_, v_sz_1223_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v_bs_1225_);
return v___x_1234_;
}
else
{
uint8_t v___x_1235_; lean_object* v_v_1236_; lean_object* v___x_1237_; lean_object* v_bs_x27_1238_; lean_object* v___x_1239_; 
v___x_1235_ = 0;
v_v_1236_ = lean_array_uget(v_bs_1225_, v_i_1224_);
v___x_1237_ = lean_unsigned_to_nat(0u);
v_bs_x27_1238_ = lean_array_uset(v_bs_1225_, v_i_1224_, v___x_1237_);
v___x_1239_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_1235_, v_v_1236_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; size_t v___x_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_add(v_i_1224_, v___x_1241_);
v___x_1243_ = lean_array_uset(v_bs_x27_1238_, v_i_1224_, v_a_1240_);
v_i_1224_ = v___x_1242_;
v_bs_1225_ = v___x_1243_;
goto _start;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_bs_x27_1238_);
v_a_1245_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1239_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1239_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1223_ = stack[0].m_num;
size_t v_i_1224_ = stack[1].m_num;
lean_object* v_bs_1225_ = stack[2].m_obj;
uint8_t v___y_1226_ = stack[3].m_num;
lean_object* v___y_1227_ = stack[4].m_obj;
lean_object* v___y_1228_ = stack[5].m_obj;
lean_object* v___y_1229_ = stack[6].m_obj;
lean_object* v___y_1230_ = stack[7].m_obj;
lean_object* v___y_1231_ = stack[8].m_obj;
lean_object* v_res_1253_;
v_res_1253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_1223_, v_i_1224_, v_bs_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
stack->m_obj
 = v_res_1253_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(lean_object* v_sz_1254_, lean_object* v_i_1255_, lean_object* v_bs_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
size_t v_sz_boxed_1264_; size_t v_i_boxed_1265_; uint8_t v___y_8229__boxed_1266_; lean_object* v_res_1267_; 
v_sz_boxed_1264_ = lean_unbox_usize(v_sz_1254_);
lean_dec(v_sz_1254_);
v_i_boxed_1265_ = lean_unbox_usize(v_i_1255_);
lean_dec(v_i_1255_);
v___y_8229__boxed_1266_ = lean_unbox(v___y_1257_);
v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_boxed_1264_, v_i_boxed_1265_, v_bs_1256_, v___y_8229__boxed_1266_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
return v_res_1267_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_unsigned_to_nat(16u);
v___x_1272_ = lean_mk_array(v___x_1271_, v___x_1270_);
return v___x_1272_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1);
v___x_1274_ = lean_unsigned_to_nat(0u);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
return v___x_1275_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3(void){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_1276_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(lean_object* v_decl_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_type_1293_; lean_object* v_value_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_type_1293_ = lean_ctor_get(v_decl_1285_, 2);
lean_inc_ref(v_type_1293_);
v_value_1294_ = lean_ctor_get(v_decl_1285_, 3);
v___x_1295_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0));
v___x_1296_ = lean_st_mk_ref(v___x_1295_);
v___x_1297_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_1294_, v___x_1296_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v_a_1307_; lean_object* v___x_1389_; size_t v_sz_1390_; size_t v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref_known(v___x_1297_, 1);
v___x_1298_ = lean_st_ref_get(v___x_1296_);
lean_dec(v___x_1296_);
v___x_1299_ = l_Array_reverse___redArg(v___x_1298_);
v___x_1300_ = 0;
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v_decl_1285_);
v___x_1302_ = lean_array_push(v___x_1299_, v___x_1301_);
v___x_1303_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_1304_ = 0;
v___x_1305_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3);
v___x_1389_ = lean_st_mk_ref(v___x_1303_);
v_sz_1390_ = lean_array_size(v___x_1302_);
v___x_1391_ = ((size_t)0ULL);
v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_1390_, v___x_1391_, v___x_1302_, v___x_1304_, v___x_1389_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1394_ = lean_st_ref_get(v___x_1389_);
lean_dec(v___x_1389_);
lean_dec(v___x_1394_);
v_a_1307_ = v_a_1393_;
goto v___jp_1306_;
}
else
{
lean_dec(v___x_1389_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1395_; 
v_a_1395_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1395_);
lean_dec_ref_known(v___x_1392_, 1);
v_a_1307_ = v_a_1395_;
goto v___jp_1306_;
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec_ref(v_type_1293_);
v_a_1396_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1392_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1392_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
v___jp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_env_1318_; lean_object* v___x_1319_; 
v___x_1308_ = lean_array_get_size(v_a_1307_);
v___x_1309_ = lean_unsigned_to_nat(1u);
v___x_1310_ = lean_nat_sub(v___x_1308_, v___x_1309_);
v___x_1311_ = lean_array_get_borrowed(v___x_1305_, v_a_1307_, v___x_1310_);
lean_dec(v___x_1310_);
v___x_1312_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1311_);
v___x_1313_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
v___x_1314_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_a_1307_, v___x_1313_);
lean_dec_ref(v_a_1307_);
v___x_1315_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4));
lean_inc_ref(v___x_1314_);
v___x_1316_ = l_Lean_Compiler_LCNF_Code_toExpr(v___x_1300_, v___x_1314_, v___x_1315_);
v___x_1317_ = lean_st_ref_get(v_a_1291_);
v_env_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc_ref_n(v_env_1318_, 2);
lean_dec(v___x_1317_);
v___x_1319_ = l_Lean_getClosedTermName_x3f(v_env_1318_, v___x_1316_);
if (lean_obj_tag(v___x_1319_) == 1)
{
lean_object* v_val_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v_env_1318_);
lean_dec_ref(v___x_1316_);
lean_dec_ref(v_type_1293_);
v_val_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_val_1320_);
lean_dec_ref_known(v___x_1319_, 1);
v___x_1321_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1300_, v___x_1314_, v_a_1289_);
lean_dec_ref(v___x_1314_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v___x_1321_, 0);
lean_dec(v_unused_1329_);
v___x_1323_ = v___x_1321_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_dec(v___x_1321_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v_val_1320_);
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_val_1320_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_val_1320_);
v_a_1330_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1321_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1321_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
else
{
lean_object* v___x_1338_; lean_object* v_baseName_1339_; lean_object* v_decls_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v___x_1319_);
v___x_1338_ = lean_st_ref_get(v_a_1287_);
v_baseName_1339_ = lean_ctor_get(v_a_1286_, 0);
v_decls_1340_ = lean_ctor_get(v___x_1338_, 0);
lean_inc_ref(v_decls_1340_);
lean_dec(v___x_1338_);
v___x_1341_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6));
v___x_1342_ = lean_array_get_size(v_decls_1340_);
lean_dec_ref(v_decls_1340_);
v___x_1343_ = lean_name_append_index_after(v___x_1341_, v___x_1342_);
lean_inc(v_baseName_1339_);
v___x_1344_ = l_Lean_Name_append(v_baseName_1339_, v___x_1343_);
lean_inc(v___x_1344_);
v___x_1345_ = l_Lean_cacheClosedTermName(v_env_1318_, v___x_1316_, v___x_1344_);
v___x_1346_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v___x_1345_, v_a_1291_);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; 
v_unused_1388_ = lean_ctor_get(v___x_1346_, 0);
lean_dec(v_unused_1388_);
v___x_1348_ = v___x_1346_;
v_isShared_1349_ = v_isSharedCheck_1387_;
goto v_resetjp_1347_;
}
else
{
lean_dec(v___x_1346_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1387_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = 1;
lean_inc(v___x_1344_);
v___x_1352_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1352_, 0, v___x_1344_);
lean_ctor_set(v___x_1352_, 1, v___x_1350_);
lean_ctor_set(v___x_1352_, 2, v_type_1293_);
lean_ctor_set(v___x_1352_, 3, v___x_1315_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*4, v___x_1351_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1314_);
v___x_1354_ = v___x_1348_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1314_);
v___x_1354_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7));
v___x_1356_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1356_, 0, v___x_1352_);
lean_ctor_set(v___x_1356_, 1, v___x_1354_);
lean_ctor_set(v___x_1356_, 2, v___x_1355_);
lean_ctor_set_uint8(v___x_1356_, sizeof(void*)*3, v___x_1304_);
lean_inc_ref(v___x_1356_);
v___x_1357_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1356_, v_a_1291_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1376_; 
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1357_, 0);
lean_dec(v_unused_1377_);
v___x_1359_ = v___x_1357_;
v_isShared_1360_ = v_isSharedCheck_1376_;
goto v_resetjp_1358_;
}
else
{
lean_dec(v___x_1357_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1376_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v_decls_1362_; lean_object* v_fvarDecisionCache_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1375_; 
v___x_1361_ = lean_st_ref_take(v_a_1287_);
v_decls_1362_ = lean_ctor_get(v___x_1361_, 0);
v_fvarDecisionCache_1363_ = lean_ctor_get(v___x_1361_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1365_ = v___x_1361_;
v_isShared_1366_ = v_isSharedCheck_1375_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_fvarDecisionCache_1363_);
lean_inc(v_decls_1362_);
lean_dec(v___x_1361_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1375_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1367_ = lean_array_push(v_decls_1362_, v___x_1356_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1367_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_fvarDecisionCache_1363_);
v___x_1369_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = lean_st_ref_put(v_a_1287_, v___x_1369_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1344_);
v___x_1372_ = v___x_1359_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1344_);
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
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref_known(v___x_1356_, 3);
lean_dec(v___x_1344_);
v_a_1378_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1357_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1357_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
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
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec(v___x_1296_);
lean_dec_ref(v_type_1293_);
lean_dec_ref(v_decl_1285_);
v_a_1404_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1297_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1297_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1285_ = stack[0].m_obj;
lean_object* v_a_1286_ = stack[1].m_obj;
lean_object* v_a_1287_ = stack[2].m_obj;
lean_object* v_a_1288_ = stack[3].m_obj;
lean_object* v_a_1289_ = stack[4].m_obj;
lean_object* v_a_1290_ = stack[5].m_obj;
lean_object* v_a_1291_ = stack[6].m_obj;
lean_object* v_res_1412_;
v_res_1412_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
stack->m_obj
 = v_res_1412_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___boxed(lean_object* v_decl_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
return v_res_1421_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(lean_object* v_msg_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0);
v___x_1425_ = lean_panic_fn_borrowed(v___x_1424_, v_msg_1423_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1429_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2));
v___x_1430_ = lean_unsigned_to_nat(9u);
v___x_1431_ = lean_unsigned_to_nat(650u);
v___x_1432_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1));
v___x_1433_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0));
v___x_1434_ = l_mkPanicMessageWithDecl(v___x_1433_, v___x_1432_, v___x_1431_, v___x_1430_, v___x_1429_);
return v___x_1434_;
}
}
lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* v_code_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_decl_1446_; lean_object* v_k_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; 
switch(lean_obj_tag(v_code_1437_))
{
case 0:
{
lean_object* v_decl_1561_; lean_object* v_k_1562_; lean_object* v_value_1563_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; 
v_decl_1561_ = lean_ctor_get(v_code_1437_, 0);
v_k_1562_ = lean_ctor_get(v_code_1437_, 1);
v_value_1563_ = lean_ctor_get(v_decl_1561_, 3);
lean_inc(v_value_1563_);
if (lean_obj_tag(v_value_1563_) == 3)
{
lean_object* v_declName_1760_; 
v_declName_1760_ = lean_ctor_get(v_value_1563_, 0);
if (lean_obj_tag(v_declName_1760_) == 1)
{
lean_object* v_pre_1761_; 
v_pre_1761_ = lean_ctor_get(v_declName_1760_, 0);
if (lean_obj_tag(v_pre_1761_) == 1)
{
lean_object* v_pre_1762_; 
v_pre_1762_ = lean_ctor_get(v_pre_1761_, 0);
if (lean_obj_tag(v_pre_1762_) == 0)
{
lean_object* v_args_1763_; lean_object* v_str_1764_; lean_object* v_str_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v_sizeId_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; 
v_args_1763_ = lean_ctor_get(v_value_1563_, 2);
v_str_1764_ = lean_ctor_get(v_declName_1760_, 1);
v_str_1765_ = lean_ctor_get(v_pre_1761_, 1);
v___x_1766_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1767_ = lean_string_dec_eq(v_str_1765_, v___x_1766_);
if (v___x_1767_ == 0)
{
v___y_1565_ = v_a_1438_;
v___y_1566_ = v_a_1439_;
v___y_1567_ = v_a_1440_;
v___y_1568_ = v_a_1441_;
v___y_1569_ = v_a_1442_;
v___y_1570_ = v_a_1443_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_2106_ = lean_string_dec_eq(v_str_1764_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_2108_ = lean_string_dec_eq(v_str_1764_, v___x_2107_);
if (v___x_2108_ == 0)
{
v___y_1565_ = v_a_1438_;
v___y_1566_ = v_a_1439_;
v___y_1567_ = v_a_1440_;
v___y_1568_ = v_a_1441_;
v___y_1569_ = v_a_1442_;
v___y_1570_ = v_a_1443_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2109_ = lean_array_get_size(v_args_1763_);
v___x_2110_ = lean_unsigned_to_nat(2u);
v___x_2111_ = lean_nat_dec_eq(v___x_2109_, v___x_2110_);
if (v___x_2111_ == 0)
{
v___y_1565_ = v_a_1438_;
v___y_1566_ = v_a_1439_;
v___y_1567_ = v_a_1440_;
v___y_1568_ = v_a_1441_;
v___y_1569_ = v_a_1442_;
v___y_1570_ = v_a_1443_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_unsigned_to_nat(1u);
v___x_2113_ = lean_array_fget_borrowed(v_args_1763_, v___x_2112_);
if (lean_obj_tag(v___x_2113_) == 1)
{
lean_object* v_fvarId_2114_; 
v_fvarId_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_fvarId_2114_);
v_sizeId_1973_ = v_fvarId_2114_;
v___y_1974_ = v_a_1438_;
v___y_1975_ = v_a_1439_;
v___y_1976_ = v_a_1440_;
v___y_1977_ = v_a_1441_;
v___y_1978_ = v_a_1442_;
v___y_1979_ = v_a_1443_;
goto v___jp_1972_;
}
else
{
v___y_1565_ = v_a_1438_;
v___y_1566_ = v_a_1439_;
v___y_1567_ = v_a_1440_;
v___y_1568_ = v_a_1441_;
v___y_1569_ = v_a_1442_;
v___y_1570_ = v_a_1443_;
goto v___jp_1564_;
}
}
}
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2115_ = lean_array_get_size(v_args_1763_);
v___x_2116_ = lean_unsigned_to_nat(2u);
v___x_2117_ = lean_nat_dec_eq(v___x_2115_, v___x_2116_);
if (v___x_2117_ == 0)
{
v___y_1565_ = v_a_1438_;
v___y_1566_ = v_a_1439_;
v___y_1567_ = v_a_1440_;
v___y_1568_ = v_a_1441_;
v___y_1569_ = v_a_1442_;
v___y_1570_ = v_a_1443_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_unsigned_to_nat(1u);
v___x_2119_ = lean_array_fget_borrowed(v_args_1763_, v___x_2118_);
if (lean_obj_tag(v___x_2119_) == 1)
{
lean_object* v_fvarId_2120_; 
v_fvarId_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_fvarId_2120_);
v_sizeId_1973_ = v_fvarId_2120_;
v___y_1974_ = v_a_1438_;
v___y_1975_ = v_a_1439_;
v___y_1976_ = v_a_1440_;
v___y_1977_ = v_a_1441_;
v___y_1978_ = v_a_1442_;
v___y_1979_ = v_a_1443_;
goto v___jp_1972_;
}
else
{
v___y_1565_ = v_a_1438_;
v___y_1566_ = v_a_1439_;
v___y_1567_ = v_a_1440_;
v___y_1568_ = v_a_1441_;
v___y_1569_ = v_a_1442_;
v___y_1570_ = v_a_1443_;
goto v___jp_1564_;
}
}
}
}
v___jp_1768_:
{
lean_object* v___x_1775_; 
lean_inc_ref(v_k_1562_);
lean_inc_ref(v_decl_1561_);
v___x_1775_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1561_, v_k_1562_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
if (lean_obj_tag(v_a_1776_) == 1)
{
lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1848_; 
v_isSharedCheck_1848_ = !lean_is_exclusive(v_value_1563_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; lean_object* v_unused_1850_; lean_object* v_unused_1851_; 
v_unused_1849_ = lean_ctor_get(v_value_1563_, 2);
lean_dec(v_unused_1849_);
v_unused_1850_ = lean_ctor_get(v_value_1563_, 1);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_value_1563_, 0);
lean_dec(v_unused_1851_);
v___x_1778_ = v_value_1563_;
v_isShared_1779_ = v_isSharedCheck_1848_;
goto v_resetjp_1777_;
}
else
{
lean_dec(v_value_1563_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1848_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v_val_1780_; lean_object* v_fst_1781_; lean_object* v_snd_1782_; lean_object* v___x_1783_; 
v_val_1780_ = lean_ctor_get(v_a_1776_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v_a_1776_, 1);
v_fst_1781_ = lean_ctor_get(v_val_1780_, 0);
lean_inc_n(v_fst_1781_, 2);
v_snd_1782_ = lean_ctor_get(v_val_1780_, 1);
lean_inc(v_snd_1782_);
lean_dec(v_val_1780_);
v___x_1783_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1781_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = 0;
v___x_1786_ = lean_box(0);
v___x_1787_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 2, v___x_1787_);
lean_ctor_set(v___x_1778_, 1, v___x_1786_);
lean_ctor_set(v___x_1778_, 0, v_a_1784_);
v___x_1789_ = v___x_1778_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1784_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1785_, v_fst_1781_, v___x_1789_, v___y_1772_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1792_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1782_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1830_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1795_ = v___x_1792_;
v_isShared_1796_ = v_isSharedCheck_1830_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1830_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
size_t v___x_1797_; size_t v___x_1798_; uint8_t v___x_1799_; 
v___x_1797_ = lean_ptr_addr(v_k_1562_);
v___x_1798_ = lean_ptr_addr(v_a_1793_);
v___x_1799_ = lean_usize_dec_eq(v___x_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1809_; 
v_isSharedCheck_1809_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; lean_object* v_unused_1811_; 
v_unused_1810_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1811_);
v___x_1801_ = v_code_1437_;
v_isShared_1802_ = v_isSharedCheck_1809_;
goto v_resetjp_1800_;
}
else
{
lean_dec(v_code_1437_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1809_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v_a_1793_);
lean_ctor_set(v___x_1801_, 0, v_a_1791_);
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1791_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_a_1793_);
v___x_1804_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1806_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1804_);
v___x_1806_ = v___x_1795_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
size_t v___x_1812_; size_t v___x_1813_; uint8_t v___x_1814_; 
v___x_1812_ = lean_ptr_addr(v_decl_1561_);
v___x_1813_ = lean_ptr_addr(v_a_1791_);
v___x_1814_ = lean_usize_dec_eq(v___x_1812_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1824_; 
v_isSharedCheck_1824_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; lean_object* v_unused_1826_; 
v_unused_1825_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1826_);
v___x_1816_ = v_code_1437_;
v_isShared_1817_ = v_isSharedCheck_1824_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v_code_1437_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1824_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 1, v_a_1793_);
lean_ctor_set(v___x_1816_, 0, v_a_1791_);
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1791_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_a_1793_);
v___x_1819_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1819_);
v___x_1821_ = v___x_1795_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v___x_1828_; 
lean_dec(v_a_1793_);
lean_dec(v_a_1791_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v_code_1437_);
v___x_1828_ = v___x_1795_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_code_1437_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
else
{
lean_dec(v_a_1791_);
lean_dec_ref_known(v_code_1437_, 2);
return v___x_1792_;
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v_snd_1782_);
lean_dec_ref_known(v_code_1437_, 2);
v_a_1831_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1790_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1790_);
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
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_snd_1782_);
lean_dec(v_fst_1781_);
lean_del_object(v___x_1778_);
lean_dec_ref_known(v_code_1437_, 2);
v_a_1840_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1783_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1783_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
else
{
lean_object* v___x_1852_; 
lean_dec(v_a_1776_);
v___x_1852_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1767_, v_value_1563_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; uint8_t v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1854_ = lean_unbox(v_a_1853_);
lean_dec(v_a_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; 
lean_inc_ref(v_k_1562_);
v___x_1855_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1562_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1892_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1892_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1892_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
size_t v___x_1860_; size_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = lean_ptr_addr(v_k_1562_);
v___x_1861_ = lean_ptr_addr(v_a_1856_);
v___x_1862_ = lean_usize_dec_eq(v___x_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1872_; 
lean_inc_ref(v_decl_1561_);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; lean_object* v_unused_1874_; 
v_unused_1873_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1874_);
v___x_1864_ = v_code_1437_;
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
else
{
lean_dec(v_code_1437_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 1, v_a_1856_);
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_decl_1561_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_a_1856_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1867_);
v___x_1869_ = v___x_1858_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
else
{
size_t v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = lean_ptr_addr(v_decl_1561_);
v___x_1876_ = lean_usize_dec_eq(v___x_1875_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1886_; 
lean_inc_ref(v_decl_1561_);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; lean_object* v_unused_1888_; 
v_unused_1887_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1887_);
v_unused_1888_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1888_);
v___x_1878_ = v_code_1437_;
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
else
{
lean_dec(v_code_1437_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v_a_1856_);
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_decl_1561_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_a_1856_);
v___x_1881_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1883_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1881_);
v___x_1883_ = v___x_1858_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v___x_1890_; 
lean_dec(v_a_1856_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v_code_1437_);
v___x_1890_ = v___x_1858_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_code_1437_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1437_, 2);
return v___x_1855_;
}
}
else
{
lean_object* v___x_1893_; 
lean_inc_ref(v_decl_1561_);
v___x_1893_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1561_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___x_1895_ = 0;
v___x_1896_ = lean_box(0);
v___x_1897_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1898_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1898_, 0, v_a_1894_);
lean_ctor_set(v___x_1898_, 1, v___x_1896_);
lean_ctor_set(v___x_1898_, 2, v___x_1897_);
lean_inc_ref(v_decl_1561_);
v___x_1899_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1895_, v_decl_1561_, v___x_1898_, v___y_1772_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
lean_inc_ref(v_k_1562_);
v___x_1901_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1562_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1939_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1939_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1939_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
size_t v___x_1906_; size_t v___x_1907_; uint8_t v___x_1908_; 
v___x_1906_ = lean_ptr_addr(v_k_1562_);
v___x_1907_ = lean_ptr_addr(v_a_1902_);
v___x_1908_ = lean_usize_dec_eq(v___x_1906_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1918_; 
v_isSharedCheck_1918_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; lean_object* v_unused_1920_; 
v_unused_1919_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1919_);
v_unused_1920_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1920_);
v___x_1910_ = v_code_1437_;
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
else
{
lean_dec(v_code_1437_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1918_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v_a_1902_);
lean_ctor_set(v___x_1910_, 0, v_a_1900_);
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1900_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_a_1902_);
v___x_1913_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1915_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1913_);
v___x_1915_ = v___x_1904_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
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
else
{
size_t v___x_1921_; size_t v___x_1922_; uint8_t v___x_1923_; 
v___x_1921_ = lean_ptr_addr(v_decl_1561_);
v___x_1922_ = lean_ptr_addr(v_a_1900_);
v___x_1923_ = lean_usize_dec_eq(v___x_1921_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1933_; 
v_isSharedCheck_1933_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; lean_object* v_unused_1935_; 
v_unused_1934_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1934_);
v_unused_1935_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1935_);
v___x_1925_ = v_code_1437_;
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
else
{
lean_dec(v_code_1437_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 1, v_a_1902_);
lean_ctor_set(v___x_1925_, 0, v_a_1900_);
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1900_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_a_1902_);
v___x_1928_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1930_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1928_);
v___x_1930_ = v___x_1904_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
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
else
{
lean_object* v___x_1937_; 
lean_dec(v_a_1902_);
lean_dec(v_a_1900_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v_code_1437_);
v___x_1937_ = v___x_1904_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_code_1437_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
else
{
lean_dec(v_a_1900_);
lean_dec_ref_known(v_code_1437_, 2);
return v___x_1901_;
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref_known(v_code_1437_, 2);
v_a_1940_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1899_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1899_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref_known(v_code_1437_, 2);
v_a_1948_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1893_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1893_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref_known(v_code_1437_, 2);
v_a_1956_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1852_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1852_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref_known(v_value_1563_, 3);
lean_dec_ref_known(v_code_1437_, 2);
v_a_1964_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1775_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1775_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
v___jp_1972_:
{
uint8_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = 0;
v___x_1981_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1980_, v_sizeId_1973_, v___y_1977_);
lean_dec(v_sizeId_1973_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
if (lean_obj_tag(v_a_1982_) == 1)
{
lean_object* v_val_1983_; 
v_val_1983_ = lean_ctor_get(v_a_1982_, 0);
lean_inc(v_val_1983_);
lean_dec_ref_known(v_a_1982_, 1);
if (lean_obj_tag(v_val_1983_) == 0)
{
lean_object* v_value_1984_; 
v_value_1984_ = lean_ctor_get(v_val_1983_, 0);
lean_inc_ref(v_value_1984_);
lean_dec_ref_known(v_val_1983_, 1);
if (lean_obj_tag(v_value_1984_) == 0)
{
lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2093_; 
v_isSharedCheck_2093_ = !lean_is_exclusive(v_value_1563_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; lean_object* v_unused_2095_; lean_object* v_unused_2096_; 
v_unused_2094_ = lean_ctor_get(v_value_1563_, 2);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_value_1563_, 1);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_value_1563_, 0);
lean_dec(v_unused_2096_);
v___x_1986_ = v_value_1563_;
v_isShared_1987_ = v_isSharedCheck_2093_;
goto v_resetjp_1985_;
}
else
{
lean_dec(v_value_1563_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2093_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_val_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_val_1988_ = lean_ctor_get(v_value_1984_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v_value_1984_, 1);
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_nat_dec_eq(v_val_1988_, v___x_1989_);
lean_dec(v_val_1988_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; 
lean_del_object(v___x_1986_);
lean_inc_ref(v_k_1562_);
v___x_1991_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1562_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2028_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2028_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2028_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
size_t v___x_1996_; size_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = lean_ptr_addr(v_k_1562_);
v___x_1997_ = lean_ptr_addr(v_a_1992_);
v___x_1998_ = lean_usize_dec_eq(v___x_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2008_; 
lean_inc_ref(v_decl_1561_);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; lean_object* v_unused_2010_; 
v_unused_2009_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_2010_);
v___x_2000_ = v_code_1437_;
v_isShared_2001_ = v_isSharedCheck_2008_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v_code_1437_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2008_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v_a_1992_);
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_decl_1561_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_a_1992_);
v___x_2003_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2005_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_2003_);
v___x_2005_ = v___x_1994_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
size_t v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = lean_ptr_addr(v_decl_1561_);
v___x_2012_ = lean_usize_dec_eq(v___x_2011_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2022_; 
lean_inc_ref(v_decl_1561_);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; lean_object* v_unused_2024_; 
v_unused_2023_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_2024_);
v___x_2014_ = v_code_1437_;
v_isShared_2015_ = v_isSharedCheck_2022_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v_code_1437_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2022_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 1, v_a_1992_);
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_decl_1561_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_a_1992_);
v___x_2017_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2019_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_2017_);
v___x_2019_ = v___x_1994_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v___x_2026_; 
lean_dec(v_a_1992_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v_code_1437_);
v___x_2026_ = v___x_1994_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_code_1437_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1437_, 2);
return v___x_1991_;
}
}
else
{
lean_object* v___x_2029_; 
lean_inc_ref(v_decl_1561_);
v___x_2029_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1561_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = lean_box(0);
v___x_2032_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 2, v___x_2032_);
lean_ctor_set(v___x_1986_, 1, v___x_2031_);
lean_ctor_set(v___x_1986_, 0, v_a_2030_);
v___x_2034_ = v___x_1986_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2030_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2035_; 
lean_inc_ref(v_decl_1561_);
v___x_2035_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1980_, v_decl_1561_, v___x_2034_, v___y_1977_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2037_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
lean_inc_ref(v_k_1562_);
v___x_2037_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1562_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2075_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2075_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2075_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
size_t v___x_2042_; size_t v___x_2043_; uint8_t v___x_2044_; 
v___x_2042_ = lean_ptr_addr(v_k_1562_);
v___x_2043_ = lean_ptr_addr(v_a_2038_);
v___x_2044_ = lean_usize_dec_eq(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2054_; 
v_isSharedCheck_2054_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; lean_object* v_unused_2056_; 
v_unused_2055_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_2056_);
v___x_2046_ = v_code_1437_;
v_isShared_2047_ = v_isSharedCheck_2054_;
goto v_resetjp_2045_;
}
else
{
lean_dec(v_code_1437_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2054_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 1, v_a_2038_);
lean_ctor_set(v___x_2046_, 0, v_a_2036_);
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2036_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_a_2038_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2049_);
v___x_2051_ = v___x_2040_;
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
else
{
size_t v___x_2057_; size_t v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = lean_ptr_addr(v_decl_1561_);
v___x_2058_ = lean_ptr_addr(v_a_2036_);
v___x_2059_ = lean_usize_dec_eq(v___x_2057_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2069_; 
v_isSharedCheck_2069_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; lean_object* v_unused_2071_; 
v_unused_2070_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_2071_);
v___x_2061_ = v_code_1437_;
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v_code_1437_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v_a_2038_);
lean_ctor_set(v___x_2061_, 0, v_a_2036_);
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2036_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_a_2038_);
v___x_2064_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2066_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2064_);
v___x_2066_ = v___x_2040_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v___x_2073_; 
lean_dec(v_a_2038_);
lean_dec(v_a_2036_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v_code_1437_);
v___x_2073_ = v___x_2040_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_code_1437_);
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
else
{
lean_dec(v_a_2036_);
lean_dec_ref_known(v_code_1437_, 2);
return v___x_2037_;
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec_ref_known(v_code_1437_, 2);
v_a_2076_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2035_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2035_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_del_object(v___x_1986_);
lean_dec_ref_known(v_code_1437_, 2);
v_a_2085_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2029_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2029_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_1984_);
v___y_1769_ = v___y_1974_;
v___y_1770_ = v___y_1975_;
v___y_1771_ = v___y_1976_;
v___y_1772_ = v___y_1977_;
v___y_1773_ = v___y_1978_;
v___y_1774_ = v___y_1979_;
goto v___jp_1768_;
}
}
else
{
lean_dec(v_val_1983_);
v___y_1769_ = v___y_1974_;
v___y_1770_ = v___y_1975_;
v___y_1771_ = v___y_1976_;
v___y_1772_ = v___y_1977_;
v___y_1773_ = v___y_1978_;
v___y_1774_ = v___y_1979_;
goto v___jp_1768_;
}
}
else
{
lean_dec(v_a_1982_);
v___y_1769_ = v___y_1974_;
v___y_1770_ = v___y_1975_;
v___y_1771_ = v___y_1976_;
v___y_1772_ = v___y_1977_;
v___y_1773_ = v___y_1978_;
v___y_1774_ = v___y_1979_;
goto v___jp_1768_;
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref_known(v_value_1563_, 3);
lean_dec_ref_known(v_code_1437_, 2);
v_a_2097_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_1981_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_1981_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
else
{
v___y_1565_ = v_a_1438_;
v___y_1566_ = v_a_1439_;
v___y_1567_ = v_a_1440_;
v___y_1568_ = v_a_1441_;
v___y_1569_ = v_a_1442_;
v___y_1570_ = v_a_1443_;
goto v___jp_1564_;
}
}
else
{
v___y_1565_ = v_a_1438_;
v___y_1566_ = v_a_1439_;
v___y_1567_ = v_a_1440_;
v___y_1568_ = v_a_1441_;
v___y_1569_ = v_a_1442_;
v___y_1570_ = v_a_1443_;
goto v___jp_1564_;
}
}
else
{
v___y_1565_ = v_a_1438_;
v___y_1566_ = v_a_1439_;
v___y_1567_ = v_a_1440_;
v___y_1568_ = v_a_1441_;
v___y_1569_ = v_a_1442_;
v___y_1570_ = v_a_1443_;
goto v___jp_1564_;
}
}
else
{
v___y_1565_ = v_a_1438_;
v___y_1566_ = v_a_1439_;
v___y_1567_ = v_a_1440_;
v___y_1568_ = v_a_1441_;
v___y_1569_ = v_a_1442_;
v___y_1570_ = v_a_1443_;
goto v___jp_1564_;
}
v___jp_1564_:
{
lean_object* v___x_1571_; 
lean_inc_ref(v_k_1562_);
lean_inc_ref(v_decl_1561_);
v___x_1571_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1561_, v_k_1562_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
if (lean_obj_tag(v_a_1572_) == 1)
{
lean_object* v_val_1573_; lean_object* v_fst_1574_; lean_object* v_snd_1575_; lean_object* v___x_1576_; 
lean_dec(v_value_1563_);
v_val_1573_ = lean_ctor_get(v_a_1572_, 0);
lean_inc(v_val_1573_);
lean_dec_ref_known(v_a_1572_, 1);
v_fst_1574_ = lean_ctor_get(v_val_1573_, 0);
lean_inc_n(v_fst_1574_, 2);
v_snd_1575_ = lean_ctor_get(v_val_1573_, 1);
lean_inc(v_snd_1575_);
lean_dec(v_val_1573_);
v___x_1576_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1574_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
v___x_1578_ = 0;
v___x_1579_ = lean_box(0);
v___x_1580_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1581_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1581_, 0, v_a_1577_);
lean_ctor_set(v___x_1581_, 1, v___x_1579_);
lean_ctor_set(v___x_1581_, 2, v___x_1580_);
v___x_1582_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1578_, v_fst_1574_, v___x_1581_, v___y_1568_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1575_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1622_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1622_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1622_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
size_t v___x_1589_; size_t v___x_1590_; uint8_t v___x_1591_; 
v___x_1589_ = lean_ptr_addr(v_k_1562_);
v___x_1590_ = lean_ptr_addr(v_a_1585_);
v___x_1591_ = lean_usize_dec_eq(v___x_1589_, v___x_1590_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1601_; 
v_isSharedCheck_1601_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; lean_object* v_unused_1603_; 
v_unused_1602_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1602_);
v_unused_1603_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1603_);
v___x_1593_ = v_code_1437_;
v_isShared_1594_ = v_isSharedCheck_1601_;
goto v_resetjp_1592_;
}
else
{
lean_dec(v_code_1437_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1601_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v_a_1585_);
lean_ctor_set(v___x_1593_, 0, v_a_1583_);
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1583_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_a_1585_);
v___x_1596_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1598_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1596_);
v___x_1598_ = v___x_1587_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
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
else
{
size_t v___x_1604_; size_t v___x_1605_; uint8_t v___x_1606_; 
v___x_1604_ = lean_ptr_addr(v_decl_1561_);
v___x_1605_ = lean_ptr_addr(v_a_1583_);
v___x_1606_ = lean_usize_dec_eq(v___x_1604_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1616_; 
v_isSharedCheck_1616_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; lean_object* v_unused_1618_; 
v_unused_1617_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1618_);
v___x_1608_ = v_code_1437_;
v_isShared_1609_ = v_isSharedCheck_1616_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v_code_1437_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1616_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 1, v_a_1585_);
lean_ctor_set(v___x_1608_, 0, v_a_1583_);
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1583_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_a_1585_);
v___x_1611_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1613_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1611_);
v___x_1613_ = v___x_1587_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
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
lean_object* v___x_1620_; 
lean_dec(v_a_1585_);
lean_dec(v_a_1583_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_code_1437_);
v___x_1620_ = v___x_1587_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_code_1437_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
else
{
lean_dec(v_a_1583_);
lean_dec_ref_known(v_code_1437_, 2);
return v___x_1584_;
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec(v_snd_1575_);
lean_dec_ref_known(v_code_1437_, 2);
v_a_1623_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1582_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1582_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec(v_snd_1575_);
lean_dec(v_fst_1574_);
lean_dec_ref_known(v_code_1437_, 2);
v_a_1631_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1576_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1576_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
uint8_t v___x_1639_; lean_object* v___x_1640_; 
lean_dec(v_a_1572_);
v___x_1639_ = 1;
v___x_1640_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1639_, v_value_1563_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; uint8_t v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = lean_unbox(v_a_1641_);
lean_dec(v_a_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; 
lean_inc_ref(v_k_1562_);
v___x_1643_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1562_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1680_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1680_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1680_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
size_t v___x_1648_; size_t v___x_1649_; uint8_t v___x_1650_; 
v___x_1648_ = lean_ptr_addr(v_k_1562_);
v___x_1649_ = lean_ptr_addr(v_a_1644_);
v___x_1650_ = lean_usize_dec_eq(v___x_1648_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1660_; 
lean_inc_ref(v_decl_1561_);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; lean_object* v_unused_1662_; 
v_unused_1661_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1662_);
v___x_1652_ = v_code_1437_;
v_isShared_1653_ = v_isSharedCheck_1660_;
goto v_resetjp_1651_;
}
else
{
lean_dec(v_code_1437_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1660_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v_a_1644_);
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_decl_1561_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_a_1644_);
v___x_1655_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1657_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1655_);
v___x_1657_ = v___x_1646_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
else
{
size_t v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = lean_ptr_addr(v_decl_1561_);
v___x_1664_ = lean_usize_dec_eq(v___x_1663_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1674_; 
lean_inc_ref(v_decl_1561_);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; lean_object* v_unused_1676_; 
v_unused_1675_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1675_);
v_unused_1676_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1676_);
v___x_1666_ = v_code_1437_;
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
else
{
lean_dec(v_code_1437_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1674_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v_a_1644_);
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_decl_1561_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_a_1644_);
v___x_1669_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1669_);
v___x_1671_ = v___x_1646_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v___x_1678_; 
lean_dec(v_a_1644_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v_code_1437_);
v___x_1678_ = v___x_1646_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_code_1437_);
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
else
{
lean_dec_ref_known(v_code_1437_, 2);
return v___x_1643_;
}
}
else
{
lean_object* v___x_1681_; 
lean_inc_ref(v_decl_1561_);
v___x_1681_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1561_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
v___x_1683_ = 0;
v___x_1684_ = lean_box(0);
v___x_1685_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1686_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1686_, 0, v_a_1682_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
lean_ctor_set(v___x_1686_, 2, v___x_1685_);
lean_inc_ref(v_decl_1561_);
v___x_1687_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1683_, v_decl_1561_, v___x_1686_, v___y_1568_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
lean_inc_ref(v_k_1562_);
v___x_1689_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1562_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1727_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1727_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1727_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
size_t v___x_1694_; size_t v___x_1695_; uint8_t v___x_1696_; 
v___x_1694_ = lean_ptr_addr(v_k_1562_);
v___x_1695_ = lean_ptr_addr(v_a_1690_);
v___x_1696_ = lean_usize_dec_eq(v___x_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1706_; 
v_isSharedCheck_1706_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; lean_object* v_unused_1708_; 
v_unused_1707_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1708_);
v___x_1698_ = v_code_1437_;
v_isShared_1699_ = v_isSharedCheck_1706_;
goto v_resetjp_1697_;
}
else
{
lean_dec(v_code_1437_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1706_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v_a_1690_);
lean_ctor_set(v___x_1698_, 0, v_a_1688_);
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1688_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_a_1690_);
v___x_1701_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1703_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1701_);
v___x_1703_ = v___x_1692_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
else
{
size_t v___x_1709_; size_t v___x_1710_; uint8_t v___x_1711_; 
v___x_1709_ = lean_ptr_addr(v_decl_1561_);
v___x_1710_ = lean_ptr_addr(v_a_1688_);
v___x_1711_ = lean_usize_dec_eq(v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1721_; 
v_isSharedCheck_1721_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; lean_object* v_unused_1723_; 
v_unused_1722_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1722_);
v_unused_1723_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1723_);
v___x_1713_ = v_code_1437_;
v_isShared_1714_ = v_isSharedCheck_1721_;
goto v_resetjp_1712_;
}
else
{
lean_dec(v_code_1437_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1721_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v_a_1690_);
lean_ctor_set(v___x_1713_, 0, v_a_1688_);
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1688_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_a_1690_);
v___x_1716_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1716_);
v___x_1718_ = v___x_1692_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
else
{
lean_object* v___x_1725_; 
lean_dec(v_a_1690_);
lean_dec(v_a_1688_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v_code_1437_);
v___x_1725_ = v___x_1692_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_code_1437_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
else
{
lean_dec(v_a_1688_);
lean_dec_ref_known(v_code_1437_, 2);
return v___x_1689_;
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref_known(v_code_1437_, 2);
v_a_1728_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1687_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1687_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec_ref_known(v_code_1437_, 2);
v_a_1736_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1681_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1681_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec_ref_known(v_code_1437_, 2);
v_a_1744_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1640_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1640_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec(v_value_1563_);
lean_dec_ref_known(v_code_1437_, 2);
v_a_1752_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1571_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1571_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2121_; lean_object* v_k_2122_; 
v_decl_2121_ = lean_ctor_get(v_code_1437_, 0);
v_k_2122_ = lean_ctor_get(v_code_1437_, 1);
lean_inc_ref(v_k_2122_);
lean_inc_ref(v_decl_2121_);
v_decl_1446_ = v_decl_2121_;
v_k_1447_ = v_k_2122_;
v___y_1448_ = v_a_1438_;
v___y_1449_ = v_a_1439_;
v___y_1450_ = v_a_1440_;
v___y_1451_ = v_a_1441_;
v___y_1452_ = v_a_1442_;
v___y_1453_ = v_a_1443_;
goto v___jp_1445_;
}
case 2:
{
lean_object* v_decl_2123_; lean_object* v_k_2124_; 
v_decl_2123_ = lean_ctor_get(v_code_1437_, 0);
v_k_2124_ = lean_ctor_get(v_code_1437_, 1);
lean_inc_ref(v_k_2124_);
lean_inc_ref(v_decl_2123_);
v_decl_1446_ = v_decl_2123_;
v_k_1447_ = v_k_2124_;
v___y_1448_ = v_a_1438_;
v___y_1449_ = v_a_1439_;
v___y_1450_ = v_a_1440_;
v___y_1451_ = v_a_1441_;
v___y_1452_ = v_a_1442_;
v___y_1453_ = v_a_1443_;
goto v___jp_1445_;
}
case 4:
{
lean_object* v_cases_2125_; lean_object* v_typeName_2126_; lean_object* v_resultType_2127_; lean_object* v_discr_2128_; lean_object* v_alts_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2168_; 
v_cases_2125_ = lean_ctor_get(v_code_1437_, 0);
lean_inc_ref(v_cases_2125_);
v_typeName_2126_ = lean_ctor_get(v_cases_2125_, 0);
v_resultType_2127_ = lean_ctor_get(v_cases_2125_, 1);
v_discr_2128_ = lean_ctor_get(v_cases_2125_, 2);
v_alts_2129_ = lean_ctor_get(v_cases_2125_, 3);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_cases_2125_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2131_ = v_cases_2125_;
v_isShared_2132_ = v_isSharedCheck_2168_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_alts_2129_);
lean_inc(v_discr_2128_);
lean_inc(v_resultType_2127_);
lean_inc(v_typeName_2126_);
lean_dec(v_cases_2125_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2168_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2129_);
v___x_2134_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v___x_2133_, v_alts_2129_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2159_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2159_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2159_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
size_t v___x_2139_; size_t v___x_2140_; uint8_t v___x_2141_; 
v___x_2139_ = lean_ptr_addr(v_alts_2129_);
lean_dec_ref(v_alts_2129_);
v___x_2140_ = lean_ptr_addr(v_a_2135_);
v___x_2141_ = lean_usize_dec_eq(v___x_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2154_; 
v_isSharedCheck_2154_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_2155_);
v___x_2143_ = v_code_1437_;
v_isShared_2144_ = v_isSharedCheck_2154_;
goto v_resetjp_2142_;
}
else
{
lean_dec(v_code_1437_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2154_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 3, v_a_2135_);
v___x_2146_ = v___x_2131_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_typeName_2126_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_resultType_2127_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_discr_2128_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_a_2135_);
v___x_2146_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2148_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v___x_2146_);
v___x_2148_ = v___x_2143_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2148_);
v___x_2150_ = v___x_2137_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
else
{
lean_object* v___x_2157_; 
lean_dec(v_a_2135_);
lean_del_object(v___x_2131_);
lean_dec(v_discr_2128_);
lean_dec_ref(v_resultType_2127_);
lean_dec(v_typeName_2126_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v_code_1437_);
v___x_2157_ = v___x_2137_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_code_1437_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_del_object(v___x_2131_);
lean_dec_ref(v_alts_2129_);
lean_dec(v_discr_2128_);
lean_dec_ref(v_resultType_2127_);
lean_dec(v_typeName_2126_);
lean_dec_ref_known(v_code_1437_, 1);
v_a_2160_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2134_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2134_);
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
default: 
{
lean_object* v___x_2169_; 
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v_code_1437_);
return v___x_2169_;
}
}
v___jp_1445_:
{
lean_object* v_params_1454_; lean_object* v_type_1455_; lean_object* v_value_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; 
v_params_1454_ = lean_ctor_get(v_decl_1446_, 2);
lean_inc_ref(v_params_1454_);
v_type_1455_ = lean_ctor_get(v_decl_1446_, 3);
lean_inc_ref(v_type_1455_);
v_value_1456_ = lean_ctor_get(v_decl_1446_, 4);
v___x_1457_ = 0;
lean_inc_ref(v_value_1456_);
v___x_1458_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_value_1456_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1460_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref_known(v___x_1458_, 1);
v___x_1460_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1457_, v_decl_1446_, v_type_1455_, v_params_1454_, v_a_1459_, v___y_1451_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1462_) == 0)
{
switch(lean_obj_tag(v_code_1437_))
{
case 1:
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1502_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1502_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1502_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v_decl_1467_; lean_object* v_k_1468_; size_t v___x_1469_; size_t v___x_1470_; uint8_t v___x_1471_; 
v_decl_1467_ = lean_ctor_get(v_code_1437_, 0);
v_k_1468_ = lean_ctor_get(v_code_1437_, 1);
v___x_1469_ = lean_ptr_addr(v_k_1468_);
v___x_1470_ = lean_ptr_addr(v_a_1463_);
v___x_1471_ = lean_usize_dec_eq(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1481_; 
v_isSharedCheck_1481_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; lean_object* v_unused_1483_; 
v_unused_1482_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1483_);
v___x_1473_ = v_code_1437_;
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
else
{
lean_dec(v_code_1437_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v_a_1463_);
lean_ctor_set(v___x_1473_, 0, v_a_1461_);
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1461_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_a_1463_);
v___x_1476_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1478_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1476_);
v___x_1478_ = v___x_1465_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
size_t v___x_1484_; size_t v___x_1485_; uint8_t v___x_1486_; 
v___x_1484_ = lean_ptr_addr(v_decl_1467_);
v___x_1485_ = lean_ptr_addr(v_a_1461_);
v___x_1486_ = lean_usize_dec_eq(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1496_; 
v_isSharedCheck_1496_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; 
v_unused_1497_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1498_);
v___x_1488_ = v_code_1437_;
v_isShared_1489_ = v_isSharedCheck_1496_;
goto v_resetjp_1487_;
}
else
{
lean_dec(v_code_1437_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1496_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 1, v_a_1463_);
lean_ctor_set(v___x_1488_, 0, v_a_1461_);
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1461_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_a_1463_);
v___x_1491_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1491_);
v___x_1493_ = v___x_1465_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
else
{
lean_object* v___x_1500_; 
lean_dec(v_a_1463_);
lean_dec(v_a_1461_);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v_code_1437_);
v___x_1500_ = v___x_1465_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_code_1437_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
case 2:
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1542_; 
v_a_1503_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1505_ = v___x_1462_;
v_isShared_1506_ = v_isSharedCheck_1542_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1462_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1542_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_decl_1507_; lean_object* v_k_1508_; size_t v___x_1509_; size_t v___x_1510_; uint8_t v___x_1511_; 
v_decl_1507_ = lean_ctor_get(v_code_1437_, 0);
v_k_1508_ = lean_ctor_get(v_code_1437_, 1);
v___x_1509_ = lean_ptr_addr(v_k_1508_);
v___x_1510_ = lean_ptr_addr(v_a_1503_);
v___x_1511_ = lean_usize_dec_eq(v___x_1509_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1521_; 
v_isSharedCheck_1521_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; lean_object* v_unused_1523_; 
v_unused_1522_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1523_);
v___x_1513_ = v_code_1437_;
v_isShared_1514_ = v_isSharedCheck_1521_;
goto v_resetjp_1512_;
}
else
{
lean_dec(v_code_1437_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1521_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 1, v_a_1503_);
lean_ctor_set(v___x_1513_, 0, v_a_1461_);
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1461_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_a_1503_);
v___x_1516_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1516_);
v___x_1518_ = v___x_1505_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
size_t v___x_1524_; size_t v___x_1525_; uint8_t v___x_1526_; 
v___x_1524_ = lean_ptr_addr(v_decl_1507_);
v___x_1525_ = lean_ptr_addr(v_a_1461_);
v___x_1526_ = lean_usize_dec_eq(v___x_1524_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1536_; 
v_isSharedCheck_1536_ = !lean_is_exclusive(v_code_1437_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; lean_object* v_unused_1538_; 
v_unused_1537_ = lean_ctor_get(v_code_1437_, 1);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v_code_1437_, 0);
lean_dec(v_unused_1538_);
v___x_1528_ = v_code_1437_;
v_isShared_1529_ = v_isSharedCheck_1536_;
goto v_resetjp_1527_;
}
else
{
lean_dec(v_code_1437_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1536_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 1, v_a_1503_);
lean_ctor_set(v___x_1528_, 0, v_a_1461_);
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1461_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_a_1503_);
v___x_1531_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1531_);
v___x_1533_ = v___x_1505_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
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
lean_object* v___x_1540_; 
lean_dec(v_a_1503_);
lean_dec(v_a_1461_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v_code_1437_);
v___x_1540_ = v___x_1505_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_code_1437_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
default: 
{
lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_a_1461_);
lean_dec_ref(v_code_1437_);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v___x_1462_, 0);
lean_dec(v_unused_1552_);
v___x_1544_ = v___x_1462_;
v_isShared_1545_ = v_isSharedCheck_1551_;
goto v_resetjp_1543_;
}
else
{
lean_dec(v___x_1462_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1551_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1546_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3, &l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3);
v___x_1547_ = l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(v___x_1546_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1547_);
v___x_1549_ = v___x_1544_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
else
{
lean_dec(v_a_1461_);
lean_dec_ref(v_code_1437_);
return v___x_1462_;
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v_k_1447_);
lean_dec_ref(v_code_1437_);
v_a_1553_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1460_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1460_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_dec_ref(v_type_1455_);
lean_dec_ref(v_params_1454_);
lean_dec_ref(v_k_1447_);
lean_dec_ref(v_decl_1446_);
lean_dec_ref(v_code_1437_);
return v___x_1458_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_visitCode_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_1437_ = stack[0].m_obj;
lean_object* v_a_1438_ = stack[1].m_obj;
lean_object* v_a_1439_ = stack[2].m_obj;
lean_object* v_a_1440_ = stack[3].m_obj;
lean_object* v_a_1441_ = stack[4].m_obj;
lean_object* v_a_1442_ = stack[5].m_obj;
lean_object* v_a_1443_ = stack[6].m_obj;
lean_object* v_res_2170_;
v_res_2170_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_code_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
stack->m_obj
 = v_res_2170_;
}
lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object* v_i_2171_, lean_object* v_as_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = lean_array_get_size(v_as_2172_);
v___x_2181_ = lean_nat_dec_lt(v_i_2171_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; 
lean_dec(v_i_2171_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_as_2172_);
return v___x_2182_;
}
else
{
lean_object* v_a_2183_; lean_object* v___y_2185_; 
v_a_2183_ = lean_array_fget_borrowed(v_as_2172_, v_i_2171_);
switch(lean_obj_tag(v_a_2183_))
{
case 0:
{
lean_object* v_code_2207_; 
v_code_2207_ = lean_ctor_get(v_a_2183_, 2);
lean_inc_ref(v_code_2207_);
v___y_2185_ = v_code_2207_;
goto v___jp_2184_;
}
case 1:
{
lean_object* v_code_2208_; 
v_code_2208_ = lean_ctor_get(v_a_2183_, 1);
lean_inc_ref(v_code_2208_);
v___y_2185_ = v_code_2208_;
goto v___jp_2184_;
}
default: 
{
lean_object* v_code_2209_; 
v_code_2209_ = lean_ctor_get(v_a_2183_, 0);
lean_inc_ref(v_code_2209_);
v___y_2185_ = v_code_2209_;
goto v___jp_2184_;
}
}
v___jp_2184_:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v___y_2185_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; size_t v___x_2189_; size_t v___x_2190_; uint8_t v___x_2191_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
lean_inc(v_a_2183_);
v___x_2188_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2183_, v_a_2187_);
v___x_2189_ = lean_ptr_addr(v_a_2183_);
v___x_2190_ = lean_ptr_addr(v___x_2188_);
v___x_2191_ = lean_usize_dec_eq(v___x_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = lean_nat_add(v_i_2171_, v___x_2192_);
v___x_2194_ = lean_array_fset(v_as_2172_, v_i_2171_, v___x_2188_);
lean_dec(v_i_2171_);
v_i_2171_ = v___x_2193_;
v_as_2172_ = v___x_2194_;
goto _start;
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec_ref(v___x_2188_);
v___x_2196_ = lean_unsigned_to_nat(1u);
v___x_2197_ = lean_nat_add(v_i_2171_, v___x_2196_);
lean_dec(v_i_2171_);
v_i_2171_ = v___x_2197_;
goto _start;
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v_as_2172_);
lean_dec(v_i_2171_);
v_a_2199_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2186_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2186_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_2171_ = stack[0].m_obj;
lean_object* v_as_2172_ = stack[1].m_obj;
lean_object* v___y_2173_ = stack[2].m_obj;
lean_object* v___y_2174_ = stack[3].m_obj;
lean_object* v___y_2175_ = stack[4].m_obj;
lean_object* v___y_2176_ = stack[5].m_obj;
lean_object* v___y_2177_ = stack[6].m_obj;
lean_object* v___y_2178_ = stack[7].m_obj;
lean_object* v_res_2210_;
v_res_2210_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_2171_, v_as_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
stack->m_obj
 = v_res_2210_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object* v_i_2211_, lean_object* v_as_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_2211_, v_as_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object* v_code_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_code_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
return v_res_2229_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(lean_object* v_f_2230_, lean_object* v_v_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
if (lean_obj_tag(v_v_2231_) == 0)
{
lean_object* v_code_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2263_; 
v_code_2239_ = lean_ctor_get(v_v_2231_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_v_2231_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2241_ = v_v_2231_;
v_isShared_2242_ = v_isSharedCheck_2263_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_code_2239_);
lean_dec(v_v_2231_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2263_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; 
lean_inc(v___y_2237_);
lean_inc_ref(v___y_2236_);
lean_inc(v___y_2235_);
lean_inc_ref(v___y_2234_);
lean_inc(v___y_2233_);
lean_inc_ref(v___y_2232_);
v___x_2243_ = lean_apply_8(v_f_2230_, v_code_2239_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, lean_box(0));
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2254_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2254_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2254_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v_a_2244_);
v___x_2249_ = v___x_2241_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2249_);
v___x_2251_ = v___x_2246_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_del_object(v___x_2241_);
v_a_2255_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2243_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2243_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
else
{
lean_object* v___x_2264_; 
lean_dec_ref(v_f_2230_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v_v_2231_);
return v___x_2264_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2230_ = stack[0].m_obj;
lean_object* v_v_2231_ = stack[1].m_obj;
lean_object* v___y_2232_ = stack[2].m_obj;
lean_object* v___y_2233_ = stack[3].m_obj;
lean_object* v___y_2234_ = stack[4].m_obj;
lean_object* v___y_2235_ = stack[5].m_obj;
lean_object* v___y_2236_ = stack[6].m_obj;
lean_object* v___y_2237_ = stack[7].m_obj;
lean_object* v_res_2265_;
v_res_2265_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2230_, v_v_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
stack->m_obj
 = v_res_2265_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(lean_object* v_f_2266_, lean_object* v_v_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2266_, v_v_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2275_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(uint8_t v_pu_2276_, lean_object* v_f_2277_, lean_object* v_v_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2277_, v_v_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2276_ = stack[0].m_num;
lean_object* v_f_2277_ = stack[1].m_obj;
lean_object* v_v_2278_ = stack[2].m_obj;
lean_object* v___y_2279_ = stack[3].m_obj;
lean_object* v___y_2280_ = stack[4].m_obj;
lean_object* v___y_2281_ = stack[5].m_obj;
lean_object* v___y_2282_ = stack[6].m_obj;
lean_object* v___y_2283_ = stack[7].m_obj;
lean_object* v___y_2284_ = stack[8].m_obj;
lean_object* v_res_2287_;
v_res_2287_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_2276_, v_f_2277_, v_v_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
stack->m_obj
 = v_res_2287_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(lean_object* v_pu_2288_, lean_object* v_f_2289_, lean_object* v_v_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
uint8_t v_pu_boxed_2298_; lean_object* v_res_2299_; 
v_pu_boxed_2298_ = lean_unbox(v_pu_2288_);
v_res_2299_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_boxed_2298_, v_f_2289_, v_v_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2299_;
}
}
lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object* v_decl_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_toSignature_2309_; lean_object* v_value_2310_; uint8_t v_recursive_2311_; lean_object* v_inlineAttr_x3f_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2337_; 
v_toSignature_2309_ = lean_ctor_get(v_decl_2301_, 0);
v_value_2310_ = lean_ctor_get(v_decl_2301_, 1);
v_recursive_2311_ = lean_ctor_get_uint8(v_decl_2301_, sizeof(void*)*3);
v_inlineAttr_x3f_2312_ = lean_ctor_get(v_decl_2301_, 2);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_decl_2301_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2314_ = v_decl_2301_;
v_isShared_2315_ = v_isSharedCheck_2337_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_inlineAttr_x3f_2312_);
lean_inc(v_value_2310_);
lean_inc(v_toSignature_2309_);
lean_dec(v_decl_2301_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2337_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0));
v___x_2317_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v___x_2316_, v_value_2310_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2328_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2328_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2328_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v_a_2318_);
v___x_2323_ = v___x_2314_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_toSignature_2309_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_a_2318_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_inlineAttr_x3f_2312_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*3, v_recursive_2311_);
v___x_2323_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2325_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2323_);
v___x_2325_ = v___x_2320_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_del_object(v___x_2314_);
lean_dec(v_inlineAttr_x3f_2312_);
lean_dec_ref(v_toSignature_2309_);
v_a_2329_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2317_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2317_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ExtractClosed_visitDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2301_ = stack[0].m_obj;
lean_object* v_a_2302_ = stack[1].m_obj;
lean_object* v_a_2303_ = stack[2].m_obj;
lean_object* v_a_2304_ = stack[3].m_obj;
lean_object* v_a_2305_ = stack[4].m_obj;
lean_object* v_a_2306_ = stack[5].m_obj;
lean_object* v_a_2307_ = stack[6].m_obj;
lean_object* v_res_2338_;
v_res_2338_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
stack->m_obj
 = v_res_2338_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(lean_object* v_decl_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
return v_res_2347_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_2351_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0));
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set(v___x_2352_, 1, v___x_2350_);
return v___x_2352_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* v_decl_2353_, lean_object* v_sccDecls_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v_toSignature_2360_; lean_object* v_name_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_toSignature_2360_ = lean_ctor_get(v_decl_2353_, 0);
v_name_2361_ = lean_ctor_get(v_toSignature_2360_, 0);
lean_inc(v_name_2361_);
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v_name_2361_);
lean_ctor_set(v___x_2362_, 1, v_sccDecls_2354_);
v___x_2363_ = lean_unsigned_to_nat(0u);
v___x_2364_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1);
v___x_2365_ = lean_st_mk_ref(v___x_2364_);
v___x_2366_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2353_, v___x_2362_, v___x_2365_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
lean_dec_ref_known(v___x_2362_, 2);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2392_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2392_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2392_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v_decls_2372_; lean_object* v_decl_2374_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2371_ = lean_st_ref_get(v___x_2365_);
lean_dec(v___x_2365_);
v_decls_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc_ref(v_decls_2372_);
lean_dec(v___x_2371_);
v___x_2379_ = lean_array_get_size(v_decls_2372_);
v___x_2380_ = lean_nat_dec_eq(v___x_2379_, v___x_2363_);
if (v___x_2380_ == 0)
{
uint8_t v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = 0;
v___x_2382_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2381_, v_a_2367_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v_decl_2374_ = v_a_2383_;
goto v___jp_2373_;
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec_ref(v_decls_2372_);
lean_del_object(v___x_2369_);
v_a_2384_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2382_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2382_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
v_decl_2374_ = v_a_2367_;
goto v___jp_2373_;
}
v___jp_2373_:
{
lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2375_ = lean_array_push(v_decls_2372_, v_decl_2374_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2375_);
v___x_2377_ = v___x_2369_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v___x_2365_);
v_a_2393_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2366_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2366_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_extractClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2353_ = stack[0].m_obj;
lean_object* v_sccDecls_2354_ = stack[1].m_obj;
lean_object* v_a_2355_ = stack[2].m_obj;
lean_object* v_a_2356_ = stack[3].m_obj;
lean_object* v_a_2357_ = stack[4].m_obj;
lean_object* v_a_2358_ = stack[5].m_obj;
lean_object* v_res_2401_;
v_res_2401_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v_decl_2353_, v_sccDecls_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
stack->m_obj
 = v_res_2401_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(lean_object* v_decl_2402_, lean_object* v_sccDecls_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v_decl_2402_, v_sccDecls_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
return v_res_2409_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(lean_object* v_decls_2410_, lean_object* v_as_2411_, size_t v_i_2412_, size_t v_stop_2413_, lean_object* v_b_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_a_2421_; uint8_t v___x_2425_; 
v___x_2425_ = lean_usize_dec_eq(v_i_2412_, v_stop_2413_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_array_uget_borrowed(v_as_2411_, v_i_2412_);
lean_inc_ref(v_decls_2410_);
lean_inc(v___x_2426_);
v___x_2427_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v___x_2426_, v_decls_2410_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
v___x_2429_ = l_Array_append___redArg(v_b_2414_, v_a_2428_);
lean_dec(v_a_2428_);
v_a_2421_ = v___x_2429_;
goto v___jp_2420_;
}
else
{
lean_dec_ref(v_b_2414_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2430_; 
v_a_2430_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2427_, 1);
v_a_2421_ = v_a_2430_;
goto v___jp_2420_;
}
else
{
lean_dec_ref(v_decls_2410_);
return v___x_2427_;
}
}
}
else
{
lean_object* v___x_2431_; 
lean_dec_ref(v_decls_2410_);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_b_2414_);
return v___x_2431_;
}
v___jp_2420_:
{
size_t v___x_2422_; size_t v___x_2423_; 
v___x_2422_ = ((size_t)1ULL);
v___x_2423_ = lean_usize_add(v_i_2412_, v___x_2422_);
v_i_2412_ = v___x_2423_;
v_b_2414_ = v_a_2421_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_2410_ = stack[0].m_obj;
lean_object* v_as_2411_ = stack[1].m_obj;
size_t v_i_2412_ = stack[2].m_num;
size_t v_stop_2413_ = stack[3].m_num;
lean_object* v_b_2414_ = stack[4].m_obj;
lean_object* v___y_2415_ = stack[5].m_obj;
lean_object* v___y_2416_ = stack[6].m_obj;
lean_object* v___y_2417_ = stack[7].m_obj;
lean_object* v___y_2418_ = stack[8].m_obj;
lean_object* v_res_2432_;
v_res_2432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2410_, v_as_2411_, v_i_2412_, v_stop_2413_, v_b_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
stack->m_obj
 = v_res_2432_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object* v_decls_2433_, lean_object* v_as_2434_, lean_object* v_i_2435_, lean_object* v_stop_2436_, lean_object* v_b_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
size_t v_i_boxed_2443_; size_t v_stop_boxed_2444_; lean_object* v_res_2445_; 
v_i_boxed_2443_ = lean_unbox_usize(v_i_2435_);
lean_dec(v_i_2435_);
v_stop_boxed_2444_ = lean_unbox_usize(v_stop_2436_);
lean_dec(v_stop_2436_);
v_res_2445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2433_, v_as_2434_, v_i_boxed_2443_, v_stop_boxed_2444_, v_b_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec_ref(v_as_2434_);
return v_res_2445_;
}
}
lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* v___x_2446_, lean_object* v_decls_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_2448_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2478_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2478_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2478_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
uint8_t v_extractClosed_2458_; 
v_extractClosed_2458_ = lean_ctor_get_uint8(v_a_2454_, sizeof(void*)*4 + 1);
lean_dec(v_a_2454_);
if (v_extractClosed_2458_ == 0)
{
lean_object* v___x_2460_; 
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v_decls_2447_);
v___x_2460_ = v___x_2456_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_decls_2447_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2462_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___x_2463_ = lean_array_get_size(v_decls_2447_);
v___x_2464_ = lean_nat_dec_lt(v___x_2446_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2466_; 
lean_dec_ref(v_decls_2447_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2462_);
v___x_2466_ = v___x_2456_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2462_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
else
{
uint8_t v___x_2468_; 
v___x_2468_ = lean_nat_dec_le(v___x_2463_, v___x_2463_);
if (v___x_2468_ == 0)
{
if (v___x_2464_ == 0)
{
lean_object* v___x_2470_; 
lean_dec_ref(v_decls_2447_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2462_);
v___x_2470_ = v___x_2456_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2462_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
else
{
size_t v___x_2472_; size_t v___x_2473_; lean_object* v___x_2474_; 
lean_del_object(v___x_2456_);
v___x_2472_ = ((size_t)0ULL);
v___x_2473_ = lean_usize_of_nat(v___x_2463_);
lean_inc_ref(v_decls_2447_);
v___x_2474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2447_, v_decls_2447_, v___x_2472_, v___x_2473_, v___x_2462_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec_ref(v_decls_2447_);
return v___x_2474_;
}
}
else
{
size_t v___x_2475_; size_t v___x_2476_; lean_object* v___x_2477_; 
lean_del_object(v___x_2456_);
v___x_2475_ = ((size_t)0ULL);
v___x_2476_ = lean_usize_of_nat(v___x_2463_);
lean_inc_ref(v_decls_2447_);
v___x_2477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2447_, v_decls_2447_, v___x_2475_, v___x_2476_, v___x_2462_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec_ref(v_decls_2447_);
return v___x_2477_;
}
}
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v_decls_2447_);
v_a_2479_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2453_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2453_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_extractClosed___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2446_ = stack[0].m_obj;
lean_object* v_decls_2447_ = stack[1].m_obj;
lean_object* v___y_2448_ = stack[2].m_obj;
lean_object* v___y_2449_ = stack[3].m_obj;
lean_object* v___y_2450_ = stack[4].m_obj;
lean_object* v___y_2451_ = stack[5].m_obj;
lean_object* v_res_2487_;
v_res_2487_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(v___x_2446_, v_decls_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
stack->m_obj
 = v_res_2487_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object* v___x_2488_, lean_object* v_decls_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(v___x_2488_, v_decls_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___x_2488_);
return v_res_2495_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2578_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2579_ = 1;
v___x_2580_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2581_ = l_Lean_registerTraceClass(v___x_2578_, v___x_2579_, v___x_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2582_;
v_res_2582_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2582_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
return v_res_2584_;
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
