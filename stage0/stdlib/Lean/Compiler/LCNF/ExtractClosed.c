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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t v_____do__lift_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
if (v_____do__lift_171_ == 0)
{
uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = 1;
v___x_180_ = lean_box(v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
else
{
uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = 0;
v___x_183_ = lean_box(v___x_182_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object* v_____do__lift_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
uint8_t v_____do__lift_15161__boxed_193_; lean_object* v_res_194_; 
v_____do__lift_15161__boxed_193_ = lean_unbox(v_____do__lift_185_);
v_res_194_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v_____do__lift_15161__boxed_193_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(lean_object* v_a_195_, lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v___x_197_; 
v___x_197_ = lean_box(0);
return v___x_197_;
}
else
{
lean_object* v_key_198_; lean_object* v_value_199_; lean_object* v_tail_200_; uint8_t v___x_201_; 
v_key_198_ = lean_ctor_get(v_x_196_, 0);
v_value_199_ = lean_ctor_get(v_x_196_, 1);
v_tail_200_ = lean_ctor_get(v_x_196_, 2);
v___x_201_ = l_Lean_instBEqFVarId_beq(v_key_198_, v_a_195_);
if (v___x_201_ == 0)
{
v_x_196_ = v_tail_200_;
goto _start;
}
else
{
lean_object* v___x_203_; 
lean_inc(v_value_199_);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v_value_199_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg___boxed(lean_object* v_a_204_, lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_204_, v_x_205_);
lean_dec(v_x_205_);
lean_dec(v_a_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(lean_object* v_m_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_buckets_209_; lean_object* v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v_fold_214_; uint64_t v___x_215_; uint64_t v___x_216_; uint64_t v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_buckets_209_ = lean_ctor_get(v_m_207_, 1);
v___x_210_ = lean_array_get_size(v_buckets_209_);
v___x_211_ = l_Lean_instHashableFVarId_hash(v_a_208_);
v___x_212_ = 32ULL;
v___x_213_ = lean_uint64_shift_right(v___x_211_, v___x_212_);
v_fold_214_ = lean_uint64_xor(v___x_211_, v___x_213_);
v___x_215_ = 16ULL;
v___x_216_ = lean_uint64_shift_right(v_fold_214_, v___x_215_);
v___x_217_ = lean_uint64_xor(v_fold_214_, v___x_216_);
v___x_218_ = lean_uint64_to_usize(v___x_217_);
v___x_219_ = lean_usize_of_nat(v___x_210_);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_sub(v___x_219_, v___x_220_);
v___x_222_ = lean_usize_land(v___x_218_, v___x_221_);
v___x_223_ = lean_array_uget_borrowed(v_buckets_209_, v___x_222_);
v___x_224_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_208_, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg___boxed(lean_object* v_m_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_m_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
return v_x_228_;
}
else
{
lean_object* v_key_230_; lean_object* v_value_231_; lean_object* v_tail_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_255_; 
v_key_230_ = lean_ctor_get(v_x_229_, 0);
v_value_231_ = lean_ctor_get(v_x_229_, 1);
v_tail_232_ = lean_ctor_get(v_x_229_, 2);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_255_ == 0)
{
v___x_234_ = v_x_229_;
v_isShared_235_ = v_isSharedCheck_255_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_tail_232_);
lean_inc(v_value_231_);
lean_inc(v_key_230_);
lean_dec(v_x_229_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_255_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v_fold_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_236_ = lean_array_get_size(v_x_228_);
v___x_237_ = l_Lean_instHashableFVarId_hash(v_key_230_);
v___x_238_ = 32ULL;
v___x_239_ = lean_uint64_shift_right(v___x_237_, v___x_238_);
v_fold_240_ = lean_uint64_xor(v___x_237_, v___x_239_);
v___x_241_ = 16ULL;
v___x_242_ = lean_uint64_shift_right(v_fold_240_, v___x_241_);
v___x_243_ = lean_uint64_xor(v_fold_240_, v___x_242_);
v___x_244_ = lean_uint64_to_usize(v___x_243_);
v___x_245_ = lean_usize_of_nat(v___x_236_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_sub(v___x_245_, v___x_246_);
v___x_248_ = lean_usize_land(v___x_244_, v___x_247_);
v___x_249_ = lean_array_uget_borrowed(v_x_228_, v___x_248_);
lean_inc(v___x_249_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 2, v___x_249_);
v___x_251_ = v___x_234_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_key_230_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_value_231_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v___x_249_);
v___x_251_ = v_reuseFailAlloc_254_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; 
v___x_252_ = lean_array_uset(v_x_228_, v___x_248_, v___x_251_);
v_x_228_ = v___x_252_;
v_x_229_ = v_tail_232_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(lean_object* v_i_256_, lean_object* v_source_257_, lean_object* v_target_258_){
_start:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_get_size(v_source_257_);
v___x_260_ = lean_nat_dec_lt(v_i_256_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec_ref(v_source_257_);
lean_dec(v_i_256_);
return v_target_258_;
}
else
{
lean_object* v_es_261_; lean_object* v___x_262_; lean_object* v_source_263_; lean_object* v_target_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_es_261_ = lean_array_fget(v_source_257_, v_i_256_);
v___x_262_ = lean_box(0);
v_source_263_ = lean_array_fset(v_source_257_, v_i_256_, v___x_262_);
v_target_264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_target_258_, v_es_261_);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_i_256_, v___x_265_);
lean_dec(v_i_256_);
v_i_256_ = v___x_266_;
v_source_257_ = v_source_263_;
v_target_258_ = v_target_264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(lean_object* v_data_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_nbuckets_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_269_ = lean_array_get_size(v_data_268_);
v___x_270_ = lean_unsigned_to_nat(2u);
v_nbuckets_271_ = lean_nat_mul(v___x_269_, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_box(0);
v___x_274_ = lean_mk_array(v_nbuckets_271_, v___x_273_);
v___x_275_ = lean_array_propagate_mark(v_data_268_, v___x_274_);
v___x_276_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v___x_272_, v_data_268_, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(lean_object* v_a_277_, lean_object* v_b_278_, lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_dec(v_b_278_);
lean_dec(v_a_277_);
return v_x_279_;
}
else
{
lean_object* v_key_280_; lean_object* v_value_281_; lean_object* v_tail_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_294_; 
v_key_280_ = lean_ctor_get(v_x_279_, 0);
v_value_281_ = lean_ctor_get(v_x_279_, 1);
v_tail_282_ = lean_ctor_get(v_x_279_, 2);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_279_);
if (v_isSharedCheck_294_ == 0)
{
v___x_284_ = v_x_279_;
v_isShared_285_ = v_isSharedCheck_294_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_tail_282_);
lean_inc(v_value_281_);
lean_inc(v_key_280_);
lean_dec(v_x_279_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_294_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
uint8_t v___x_286_; 
v___x_286_ = l_Lean_instBEqFVarId_beq(v_key_280_, v_a_277_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_277_, v_b_278_, v_tail_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 2, v___x_287_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_key_280_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_value_281_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
lean_object* v___x_292_; 
lean_dec(v_value_281_);
lean_dec(v_key_280_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v_b_278_);
lean_ctor_set(v___x_284_, 0, v_a_277_);
v___x_292_ = v___x_284_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_277_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_b_278_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_tail_282_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(lean_object* v_a_295_, lean_object* v_x_296_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
uint8_t v___x_297_; 
v___x_297_ = 0;
return v___x_297_;
}
else
{
lean_object* v_key_298_; lean_object* v_tail_299_; uint8_t v___x_300_; 
v_key_298_ = lean_ctor_get(v_x_296_, 0);
v_tail_299_ = lean_ctor_get(v_x_296_, 2);
v___x_300_ = l_Lean_instBEqFVarId_beq(v_key_298_, v_a_295_);
if (v___x_300_ == 0)
{
v_x_296_ = v_tail_299_;
goto _start;
}
else
{
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg___boxed(lean_object* v_a_302_, lean_object* v_x_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_302_, v_x_303_);
lean_dec(v_x_303_);
lean_dec(v_a_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(lean_object* v_m_306_, lean_object* v_a_307_, lean_object* v_b_308_){
_start:
{
lean_object* v_size_309_; lean_object* v_buckets_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_353_; 
v_size_309_ = lean_ctor_get(v_m_306_, 0);
v_buckets_310_ = lean_ctor_get(v_m_306_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_m_306_);
if (v_isSharedCheck_353_ == 0)
{
v___x_312_ = v_m_306_;
v_isShared_313_ = v_isSharedCheck_353_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_buckets_310_);
lean_inc(v_size_309_);
lean_dec(v_m_306_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_353_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v_fold_318_; uint64_t v___x_319_; uint64_t v___x_320_; uint64_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; lean_object* v_bkt_327_; uint8_t v___x_328_; 
v___x_314_ = lean_array_get_size(v_buckets_310_);
v___x_315_ = l_Lean_instHashableFVarId_hash(v_a_307_);
v___x_316_ = 32ULL;
v___x_317_ = lean_uint64_shift_right(v___x_315_, v___x_316_);
v_fold_318_ = lean_uint64_xor(v___x_315_, v___x_317_);
v___x_319_ = 16ULL;
v___x_320_ = lean_uint64_shift_right(v_fold_318_, v___x_319_);
v___x_321_ = lean_uint64_xor(v_fold_318_, v___x_320_);
v___x_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = lean_usize_of_nat(v___x_314_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_sub(v___x_323_, v___x_324_);
v___x_326_ = lean_usize_land(v___x_322_, v___x_325_);
v_bkt_327_ = lean_array_uget_borrowed(v_buckets_310_, v___x_326_);
v___x_328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_307_, v_bkt_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v_size_x27_330_; lean_object* v___x_331_; lean_object* v_buckets_x27_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v_size_x27_330_ = lean_nat_add(v_size_309_, v___x_329_);
lean_dec(v_size_309_);
lean_inc(v_bkt_327_);
v___x_331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_331_, 0, v_a_307_);
lean_ctor_set(v___x_331_, 1, v_b_308_);
lean_ctor_set(v___x_331_, 2, v_bkt_327_);
v_buckets_x27_332_ = lean_array_uset(v_buckets_310_, v___x_326_, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(4u);
v___x_334_ = lean_nat_mul(v_size_x27_330_, v___x_333_);
v___x_335_ = lean_unsigned_to_nat(3u);
v___x_336_ = lean_nat_div(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_array_get_size(v_buckets_x27_332_);
v___x_338_ = lean_nat_dec_le(v___x_336_, v___x_337_);
lean_dec(v___x_336_);
if (v___x_338_ == 0)
{
lean_object* v_val_339_; lean_object* v___x_341_; 
v_val_339_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_buckets_x27_332_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v_val_339_);
lean_ctor_set(v___x_312_, 0, v_size_x27_330_);
v___x_341_ = v___x_312_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_size_x27_330_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_val_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_344_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v_buckets_x27_332_);
lean_ctor_set(v___x_312_, 0, v_size_x27_330_);
v___x_344_ = v___x_312_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_size_x27_330_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_buckets_x27_332_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v___x_346_; lean_object* v_buckets_x27_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
lean_inc(v_bkt_327_);
v___x_346_ = lean_box(0);
v_buckets_x27_347_ = lean_array_uset(v_buckets_310_, v___x_326_, v___x_346_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_307_, v_b_308_, v_bkt_327_);
v___x_349_ = lean_array_uset(v_buckets_x27_347_, v___x_326_, v___x_348_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___x_349_);
v___x_351_ = v___x_312_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_size_309_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(lean_object* v_declName_354_, lean_object* v_as_355_, size_t v_i_356_, size_t v_stop_357_){
_start:
{
uint8_t v___x_358_; 
v___x_358_ = lean_usize_dec_eq(v_i_356_, v_stop_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v_toSignature_360_; lean_object* v_name_361_; uint8_t v___x_362_; 
v___x_359_ = lean_array_uget_borrowed(v_as_355_, v_i_356_);
v_toSignature_360_ = lean_ctor_get(v___x_359_, 0);
v_name_361_ = lean_ctor_get(v_toSignature_360_, 0);
v___x_362_ = lean_name_eq(v_name_361_, v_declName_354_);
if (v___x_362_ == 0)
{
size_t v___x_363_; size_t v___x_364_; 
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_add(v_i_356_, v___x_363_);
v_i_356_ = v___x_364_;
goto _start;
}
else
{
return v___x_362_;
}
}
else
{
uint8_t v___x_366_; 
v___x_366_ = 0;
return v___x_366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3___boxed(lean_object* v_declName_367_, lean_object* v_as_368_, lean_object* v_i_369_, lean_object* v_stop_370_){
_start:
{
size_t v_i_boxed_371_; size_t v_stop_boxed_372_; uint8_t v_res_373_; lean_object* v_r_374_; 
v_i_boxed_371_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_stop_boxed_372_ = lean_unbox_usize(v_stop_370_);
lean_dec(v_stop_370_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_367_, v_as_368_, v_i_boxed_371_, v_stop_boxed_372_);
lean_dec_ref(v_as_368_);
lean_dec(v_declName_367_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(uint8_t v_isRoot_375_, uint8_t v___x_376_, lean_object* v_as_377_, size_t v_i_378_, size_t v_stop_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = lean_usize_dec_eq(v_i_378_, v_stop_379_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; uint8_t v___y_383_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_381_ = 1;
v___x_387_ = lean_array_uget_borrowed(v_as_377_, v_i_378_);
v___x_388_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v___x_387_);
if (v___x_388_ == 0)
{
v___y_383_ = v_isRoot_375_;
goto v___jp_382_;
}
else
{
v___y_383_ = v___x_376_;
goto v___jp_382_;
}
v___jp_382_:
{
if (v___y_383_ == 0)
{
size_t v___x_384_; size_t v___x_385_; 
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_add(v_i_378_, v___x_384_);
v_i_378_ = v___x_385_;
goto _start;
}
else
{
return v___x_381_;
}
}
}
else
{
uint8_t v___x_389_; 
v___x_389_ = 0;
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object* v_isRoot_390_, lean_object* v___x_391_, lean_object* v_as_392_, lean_object* v_i_393_, lean_object* v_stop_394_){
_start:
{
uint8_t v_isRoot_boxed_395_; uint8_t v___x_15468__boxed_396_; size_t v_i_boxed_397_; size_t v_stop_boxed_398_; uint8_t v_res_399_; lean_object* v_r_400_; 
v_isRoot_boxed_395_ = lean_unbox(v_isRoot_390_);
v___x_15468__boxed_396_ = lean_unbox(v___x_391_);
v_i_boxed_397_ = lean_unbox_usize(v_i_393_);
lean_dec(v_i_393_);
v_stop_boxed_398_ = lean_unbox_usize(v_stop_394_);
lean_dec(v_stop_394_);
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_boxed_395_, v___x_15468__boxed_396_, v_as_392_, v_i_boxed_397_, v_stop_boxed_398_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(uint8_t v___x_402_, lean_object* v_as_403_, size_t v_i_404_, size_t v_stop_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(lean_object* v_as_439_, size_t v_i_440_, size_t v_stop_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = lean_usize_dec_eq(v_i_440_, v_stop_441_);
if (v___x_453_ == 0)
{
uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = 1;
v___x_455_ = lean_array_uget_borrowed(v_as_439_, v_i_440_);
lean_inc(v___x_455_);
v___x_456_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_455_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_466_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_466_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_466_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_466_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
uint8_t v___x_461_; 
v___x_461_ = lean_unbox(v_a_457_);
lean_dec(v_a_457_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_box(v___x_454_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_462_);
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
else
{
lean_del_object(v___x_459_);
goto v___jp_449_;
}
}
}
else
{
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_476_; 
v_a_467_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_476_ == 0)
{
v___x_469_ = v___x_456_;
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_456_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_476_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
uint8_t v___x_471_; 
v___x_471_ = lean_unbox(v_a_467_);
lean_dec(v_a_467_);
if (v___x_471_ == 0)
{
lean_del_object(v___x_469_);
goto v___jp_449_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_box(v___x_454_);
if (v_isShared_470_ == 0)
{
lean_ctor_set_tag(v___x_469_, 0);
lean_ctor_set(v___x_469_, 0, v___x_472_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
else
{
return v___x_456_;
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
v___jp_449_:
{
size_t v___x_450_; size_t v___x_451_; 
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_440_, v___x_450_);
v_i_440_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t v_isRoot_480_, lean_object* v_v_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
switch(lean_obj_tag(v_v_481_))
{
case 0:
{
lean_object* v_value_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_538_; 
v_value_493_ = lean_ctor_get(v_v_481_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_v_481_);
if (v_isSharedCheck_538_ == 0)
{
v___x_495_ = v_v_481_;
v_isShared_496_ = v_isSharedCheck_538_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_value_493_);
lean_dec(v_v_481_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_538_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
switch(lean_obj_tag(v_value_493_))
{
case 1:
{
lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_505_; 
lean_del_object(v___x_495_);
v_isSharedCheck_505_ = !lean_is_exclusive(v_value_493_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_value_493_, 0);
lean_dec(v_unused_506_);
v___x_498_ = v_value_493_;
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
else
{
lean_dec(v_value_493_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_500_ = 1;
v___x_501_ = lean_box(v___x_500_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 0);
lean_ctor_set(v___x_498_, 0, v___x_501_);
v___x_503_ = v___x_498_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
case 0:
{
lean_del_object(v___x_495_);
if (v_isRoot_480_ == 0)
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_515_; 
v_isSharedCheck_515_ = !lean_is_exclusive(v_value_493_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_value_493_, 0);
lean_dec(v_unused_516_);
v___x_508_ = v_value_493_;
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_value_493_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = 1;
v___x_511_ = lean_box(v___x_510_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
else
{
lean_object* v_val_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_527_; 
v_val_517_ = lean_ctor_get(v_value_493_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_value_493_);
if (v_isSharedCheck_527_ == 0)
{
v___x_519_ = v_value_493_;
v_isShared_520_ = v_isSharedCheck_527_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_val_517_);
lean_dec(v_value_493_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_527_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_521_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0, &l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0);
v___x_522_ = lean_nat_dec_le(v___x_521_, v_val_517_);
lean_dec(v_val_517_);
v___x_523_ = lean_box(v___x_522_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_523_);
v___x_525_ = v___x_519_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
default: 
{
lean_dec_ref(v_value_493_);
if (v_isRoot_480_ == 0)
{
uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_528_ = 1;
v___x_529_ = lean_box(v___x_528_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_529_);
v___x_531_ = v___x_495_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_533_ = 0;
v___x_534_ = lean_box(v___x_533_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_534_);
v___x_536_ = v___x_495_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
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
uint8_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = 1;
v___x_540_ = lean_box(v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
else
{
uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = 0;
v___x_543_ = lean_box(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
case 2:
{
lean_object* v_struct_545_; lean_object* v___x_546_; 
v_struct_545_ = lean_ctor_get(v_v_481_, 2);
lean_inc(v_struct_545_);
lean_dec_ref_known(v_v_481_, 3);
v___x_546_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_struct_545_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
return v___x_546_;
}
case 3:
{
lean_object* v_declName_547_; lean_object* v_args_548_; lean_object* v_sccDecls_549_; lean_object* v___x_550_; uint8_t v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; uint8_t v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; uint8_t v___y_604_; uint8_t v___y_608_; uint8_t v___y_609_; uint8_t v___y_613_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_declName_547_ = lean_ctor_get(v_v_481_, 0);
lean_inc(v_declName_547_);
v_args_548_ = lean_ctor_get(v_v_481_, 2);
lean_inc_ref(v_args_548_);
lean_dec_ref_known(v_v_481_, 3);
v_sccDecls_549_ = lean_ctor_get(v_a_482_, 1);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_array_get_size(v_sccDecls_549_);
v___x_633_ = lean_nat_dec_lt(v___x_550_, v___x_632_);
if (v___x_633_ == 0)
{
v___y_613_ = v___x_633_;
goto v___jp_612_;
}
else
{
if (v___x_633_ == 0)
{
v___y_613_ = v___x_633_;
goto v___jp_612_;
}
else
{
size_t v___x_634_; size_t v___x_635_; uint8_t v___x_636_; 
v___x_634_ = ((size_t)0ULL);
v___x_635_ = lean_usize_of_nat(v___x_632_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_547_, v_sccDecls_549_, v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
v___y_613_ = v___x_636_;
goto v___jp_612_;
}
else
{
uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec_ref(v_args_548_);
lean_dec(v_declName_547_);
v___x_637_ = 0;
v___x_638_ = lean_box(v___x_637_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
}
v___jp_551_:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_array_get_size(v_args_548_);
v___x_560_ = lean_nat_dec_lt(v___x_550_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec_ref(v_args_548_);
goto v___jp_489_;
}
else
{
if (v___x_560_ == 0)
{
lean_dec_ref(v_args_548_);
goto v___jp_489_;
}
else
{
size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
v___x_561_ = ((size_t)0ULL);
v___x_562_ = lean_usize_of_nat(v___x_559_);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___y_552_, v_args_548_, v___x_561_, v___x_562_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec_ref(v_args_548_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_573_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_573_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_573_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
uint8_t v___x_568_; 
v___x_568_ = lean_unbox(v_a_564_);
lean_dec(v_a_564_);
if (v___x_568_ == 0)
{
lean_del_object(v___x_566_);
goto v___jp_489_;
}
else
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_box(v___y_552_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_569_);
v___x_571_ = v___x_566_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
return v___x_563_;
}
}
}
}
v___jp_574_:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_547_, v___y_581_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_594_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_594_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_594_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_594_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
if (lean_obj_tag(v_a_583_) == 1)
{
lean_object* v_val_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_val_587_ = lean_ctor_get(v_a_583_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v_a_583_, 1);
v___x_588_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_587_);
lean_dec(v_val_587_);
v___x_589_ = lean_nat_dec_eq(v___x_588_, v___x_550_);
lean_dec(v___x_588_);
if (v___x_589_ == 0)
{
lean_del_object(v___x_585_);
v___y_552_ = v___y_575_;
v___y_553_ = v___y_576_;
v___y_554_ = v___y_577_;
v___y_555_ = v___y_578_;
v___y_556_ = v___y_579_;
v___y_557_ = v___y_580_;
v___y_558_ = v___y_581_;
goto v___jp_551_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_592_; 
lean_dec_ref(v_args_548_);
v___x_590_ = lean_box(v___y_575_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_590_);
v___x_592_ = v___x_585_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
lean_del_object(v___x_585_);
lean_dec(v_a_583_);
v___y_552_ = v___y_575_;
v___y_553_ = v___y_576_;
v___y_554_ = v___y_577_;
v___y_555_ = v___y_578_;
v___y_556_ = v___y_579_;
v___y_557_ = v___y_580_;
v___y_558_ = v___y_581_;
goto v___jp_551_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v_args_548_);
v_a_595_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_582_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_582_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
v___jp_603_:
{
if (v___y_604_ == 0)
{
v___y_575_ = v___y_604_;
v___y_576_ = v_a_482_;
v___y_577_ = v_a_483_;
v___y_578_ = v_a_484_;
v___y_579_ = v_a_485_;
v___y_580_ = v_a_486_;
v___y_581_ = v_a_487_;
goto v___jp_574_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec_ref(v_args_548_);
lean_dec(v_declName_547_);
v___x_605_ = lean_box(v___y_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
v___jp_607_:
{
if (v___y_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec_ref(v_args_548_);
lean_dec(v_declName_547_);
v___x_610_ = lean_box(v___y_608_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
else
{
v___y_604_ = v___y_608_;
goto v___jp_603_;
}
}
v___jp_612_:
{
lean_object* v___x_614_; lean_object* v_env_615_; uint8_t v___x_616_; 
v___x_614_ = lean_st_ref_get(v_a_487_);
v_env_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_ref(v_env_615_);
lean_dec(v___x_614_);
lean_inc(v_declName_547_);
v___x_616_ = l_Lean_hasNeverExtractAttribute(v_env_615_, v_declName_547_);
if (v___x_616_ == 0)
{
if (v_isRoot_480_ == 0)
{
lean_dec(v_declName_547_);
v___y_552_ = v___x_616_;
v___y_553_ = v_a_482_;
v___y_554_ = v_a_483_;
v___y_555_ = v_a_484_;
v___y_556_ = v_a_485_;
v___y_557_ = v_a_486_;
v___y_558_ = v_a_487_;
goto v___jp_551_;
}
else
{
lean_object* v___x_617_; lean_object* v_env_618_; lean_object* v___x_619_; 
v___x_617_ = lean_st_ref_get(v_a_487_);
v_env_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc_ref(v_env_618_);
lean_dec(v___x_617_);
lean_inc(v_declName_547_);
v___x_619_ = l_Lean_Environment_find_x3f(v_env_618_, v_declName_547_, v___x_616_);
if (lean_obj_tag(v___x_619_) == 1)
{
lean_object* v_val_620_; 
v_val_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_val_620_);
lean_dec_ref_known(v___x_619_, 1);
switch(lean_obj_tag(v_val_620_))
{
case 1:
{
lean_object* v_val_621_; lean_object* v_toConstantVal_622_; lean_object* v_type_623_; uint8_t v___x_624_; 
v_val_621_ = lean_ctor_get(v_val_620_, 0);
lean_inc_ref(v_val_621_);
lean_dec_ref_known(v_val_620_, 1);
v_toConstantVal_622_ = lean_ctor_get(v_val_621_, 0);
lean_inc_ref(v_toConstantVal_622_);
lean_dec_ref(v_val_621_);
v_type_623_ = lean_ctor_get(v_toConstantVal_622_, 2);
lean_inc_ref(v_type_623_);
lean_dec_ref(v_toConstantVal_622_);
v___x_624_ = l_Lean_Expr_isForall(v_type_623_);
lean_dec_ref(v_type_623_);
v___y_608_ = v___x_616_;
v___y_609_ = v___x_624_;
goto v___jp_607_;
}
case 6:
{
lean_object* v___x_625_; uint8_t v___x_626_; 
lean_dec_ref_known(v_val_620_, 1);
v___x_625_ = lean_array_get_size(v_args_548_);
v___x_626_ = lean_nat_dec_lt(v___x_550_, v___x_625_);
if (v___x_626_ == 0)
{
v___y_608_ = v___x_616_;
v___y_609_ = v___x_616_;
goto v___jp_607_;
}
else
{
if (v___x_626_ == 0)
{
v___y_608_ = v___x_616_;
v___y_609_ = v___x_616_;
goto v___jp_607_;
}
else
{
size_t v___x_627_; size_t v___x_628_; uint8_t v___x_629_; 
v___x_627_ = ((size_t)0ULL);
v___x_628_ = lean_usize_of_nat(v___x_625_);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_480_, v___x_616_, v_args_548_, v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
v___y_608_ = v___x_616_;
v___y_609_ = v___x_616_;
goto v___jp_607_;
}
else
{
if (v___x_616_ == 0)
{
v___y_604_ = v___x_616_;
goto v___jp_603_;
}
else
{
v___y_608_ = v___x_616_;
v___y_609_ = v___x_616_;
goto v___jp_607_;
}
}
}
}
}
default: 
{
lean_dec(v_val_620_);
v___y_604_ = v___x_616_;
goto v___jp_603_;
}
}
}
else
{
lean_dec(v___x_619_);
v___y_575_ = v___x_616_;
v___y_576_ = v_a_482_;
v___y_577_ = v_a_483_;
v___y_578_ = v_a_484_;
v___y_579_ = v_a_485_;
v___y_580_ = v_a_486_;
v___y_581_ = v_a_487_;
goto v___jp_574_;
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec_ref(v_args_548_);
lean_dec(v_declName_547_);
v___x_630_ = lean_box(v___y_613_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
}
default: 
{
lean_object* v_fvarId_640_; lean_object* v_args_641_; lean_object* v___x_642_; 
v_fvarId_640_ = lean_ctor_get(v_v_481_, 0);
lean_inc(v_fvarId_640_);
v_args_641_ = lean_ctor_get(v_v_481_, 1);
lean_inc_ref(v_args_641_);
lean_dec_ref_known(v_v_481_, 2);
v___x_642_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_640_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___y_645_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = lean_array_get_size(v_args_641_);
v___x_657_ = lean_nat_dec_lt(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v_args_641_);
v___x_658_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_657_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
v___y_645_ = v___x_658_;
goto v___jp_644_;
}
else
{
if (v___x_657_ == 0)
{
lean_object* v___x_659_; 
lean_dec_ref(v_args_641_);
v___x_659_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_657_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
v___y_645_ = v___x_659_;
goto v___jp_644_;
}
else
{
size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; 
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_656_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_args_641_, v___x_660_, v___x_661_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
lean_dec_ref(v_args_641_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; uint8_t v___x_664_; lean_object* v___x_665_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v___x_664_ = lean_unbox(v_a_663_);
lean_dec(v_a_663_);
v___x_665_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_664_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
v___y_645_ = v___x_665_;
goto v___jp_644_;
}
else
{
v___y_645_ = v___x_662_;
goto v___jp_644_;
}
}
}
v___jp_644_:
{
if (lean_obj_tag(v___y_645_) == 0)
{
uint8_t v___x_646_; 
v___x_646_ = lean_unbox(v_a_643_);
if (v___x_646_ == 0)
{
lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
v_isSharedCheck_653_ = !lean_is_exclusive(v___y_645_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v___y_645_, 0);
lean_dec(v_unused_654_);
v___x_648_ = v___y_645_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_dec(v___y_645_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v_a_643_);
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_643_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
lean_dec(v_a_643_);
return v___y_645_;
}
}
else
{
lean_dec(v_a_643_);
return v___y_645_;
}
}
}
else
{
lean_dec_ref(v_args_641_);
return v___x_642_;
}
}
}
v___jp_489_:
{
uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = 1;
v___x_491_ = lean_box(v___x_490_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(lean_object* v_fvarId_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
uint8_t v___x_674_; lean_object* v___x_675_; 
v___x_674_ = 0;
v___x_675_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_674_, v_fvarId_666_, v_a_670_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_689_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_689_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_689_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_689_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
if (lean_obj_tag(v_a_676_) == 1)
{
lean_object* v_val_680_; lean_object* v_value_681_; uint8_t v___x_682_; lean_object* v___x_683_; 
lean_del_object(v___x_678_);
v_val_680_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_val_680_);
lean_dec_ref_known(v_a_676_, 1);
v_value_681_ = lean_ctor_get(v_val_680_, 3);
lean_inc(v_value_681_);
lean_dec(v_val_680_);
v___x_682_ = 0;
v___x_683_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_682_, v_value_681_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_);
return v___x_683_;
}
else
{
uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
lean_dec(v_a_676_);
v___x_684_ = 0;
v___x_685_ = lean_box(v___x_684_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_685_);
v___x_687_ = v___x_678_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_675_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_675_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object* v_fvarId_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v___x_706_; lean_object* v_fvarDecisionCache_707_; lean_object* v___x_708_; 
v___x_706_ = lean_st_ref_get(v_a_700_);
v_fvarDecisionCache_707_ = lean_ctor_get(v___x_706_, 1);
lean_inc_ref(v_fvarDecisionCache_707_);
lean_dec(v___x_706_);
v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_fvarDecisionCache_707_, v_fvarId_698_);
lean_dec_ref(v_fvarDecisionCache_707_);
if (lean_obj_tag(v___x_708_) == 1)
{
lean_object* v_val_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec(v_fvarId_698_);
v_val_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_val_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 0);
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_val_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_object* v___x_717_; 
lean_dec(v___x_708_);
v___x_717_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_737_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_737_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_737_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_737_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v_decls_723_; lean_object* v_fvarDecisionCache_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_736_; 
v___x_722_ = lean_st_ref_take(v_a_700_);
v_decls_723_ = lean_ctor_get(v___x_722_, 0);
v_fvarDecisionCache_724_ = lean_ctor_get(v___x_722_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_736_ == 0)
{
v___x_726_ = v___x_722_;
v_isShared_727_ = v_isSharedCheck_736_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_fvarDecisionCache_724_);
lean_inc(v_decls_723_);
lean_dec(v___x_722_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_736_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_inc(v_a_718_);
v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_fvarDecisionCache_724_, v_fvarId_698_, v_a_718_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_728_);
v___x_730_ = v___x_726_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_decls_723_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_735_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_st_ref_put(v_a_700_, v___x_730_);
if (v_isShared_721_ == 0)
{
v___x_733_ = v___x_720_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_718_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_698_);
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object* v_arg_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
if (lean_obj_tag(v_arg_738_) == 1)
{
lean_object* v_fvarId_746_; lean_object* v___x_747_; 
v_fvarId_746_ = lean_ctor_get(v_arg_738_, 0);
lean_inc(v_fvarId_746_);
lean_dec_ref_known(v_arg_738_, 1);
v___x_747_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_746_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
return v___x_747_;
}
else
{
uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec(v_arg_738_);
v___x_748_ = 1;
v___x_749_ = lean_box(v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object* v_arg_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v_arg_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(lean_object* v_fvarId_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_fvarId_760_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object* v_fvarId_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object* v___x_778_, lean_object* v_as_779_, lean_object* v_i_780_, lean_object* v_stop_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
uint8_t v___x_15521__boxed_789_; size_t v_i_boxed_790_; size_t v_stop_boxed_791_; lean_object* v_res_792_; 
v___x_15521__boxed_789_ = lean_unbox(v___x_778_);
v_i_boxed_790_ = lean_unbox_usize(v_i_780_);
lean_dec(v_i_780_);
v_stop_boxed_791_ = lean_unbox_usize(v_stop_781_);
lean_dec(v_stop_781_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___x_15521__boxed_789_, v_as_779_, v_i_boxed_790_, v_stop_boxed_791_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v_as_779_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(lean_object* v_as_793_, lean_object* v_i_794_, lean_object* v_stop_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
size_t v_i_boxed_803_; size_t v_stop_boxed_804_; lean_object* v_res_805_; 
v_i_boxed_803_ = lean_unbox_usize(v_i_794_);
lean_dec(v_i_794_);
v_stop_boxed_804_ = lean_unbox_usize(v_stop_795_);
lean_dec(v_stop_795_);
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_as_793_, v_i_boxed_803_, v_stop_boxed_804_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec_ref(v_as_793_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object* v_isRoot_806_, lean_object* v_v_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
uint8_t v_isRoot_boxed_815_; lean_object* v_res_816_; 
v_isRoot_boxed_815_ = lean_unbox(v_isRoot_806_);
v_res_816_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v_isRoot_boxed_815_, v_v_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object* v_00_u03b2_817_, lean_object* v_m_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_818_, v_a_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___boxed(lean_object* v_00_u03b2_821_, lean_object* v_m_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(v_00_u03b2_821_, v_m_822_, v_a_823_);
lean_dec(v_a_823_);
lean_dec_ref(v_m_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(lean_object* v_00_u03b2_825_, lean_object* v_m_826_, lean_object* v_a_827_, lean_object* v_b_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_m_826_, v_a_827_, v_b_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(lean_object* v_00_u03b2_830_, lean_object* v_a_831_, lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_831_, v_x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___boxed(lean_object* v_00_u03b2_834_, lean_object* v_a_835_, lean_object* v_x_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(v_00_u03b2_834_, v_a_835_, v_x_836_);
lean_dec(v_x_836_);
lean_dec(v_a_835_);
return v_res_837_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(lean_object* v_00_u03b2_838_, lean_object* v_a_839_, lean_object* v_x_840_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_839_, v_x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___boxed(lean_object* v_00_u03b2_842_, lean_object* v_a_843_, lean_object* v_x_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(v_00_u03b2_842_, v_a_843_, v_x_844_);
lean_dec(v_x_844_);
lean_dec(v_a_843_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10(lean_object* v_00_u03b2_847_, lean_object* v_data_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_data_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11(lean_object* v_00_u03b2_850_, lean_object* v_a_851_, lean_object* v_b_852_, lean_object* v_x_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_851_, v_b_852_, v_x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_855_, lean_object* v_i_856_, lean_object* v_source_857_, lean_object* v_target_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v_i_856_, v_source_857_, v_target_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_x_861_, v_x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(lean_object* v_prevArrayId_869_, lean_object* v_decl_870_, lean_object* v_k_871_, lean_object* v_illegalSet_872_, lean_object* v_size_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_decl_885_; lean_object* v_k_886_; lean_object* v_illegalSet_887_; lean_object* v_zero_895_; uint8_t v_isZero_896_; 
v_zero_895_ = lean_unsigned_to_nat(0u);
v_isZero_896_ = lean_nat_dec_eq(v_size_873_, v_zero_895_);
if (v_isZero_896_ == 1)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
lean_dec(v_prevArrayId_869_);
v___x_897_ = lean_box(0);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
else
{
lean_object* v_value_899_; 
v_value_899_ = lean_ctor_get(v_decl_870_, 3);
if (lean_obj_tag(v_value_899_) == 3)
{
lean_object* v_declName_900_; 
v_declName_900_ = lean_ctor_get(v_value_899_, 0);
if (lean_obj_tag(v_declName_900_) == 1)
{
lean_object* v_pre_901_; 
v_pre_901_ = lean_ctor_get(v_declName_900_, 0);
if (lean_obj_tag(v_pre_901_) == 1)
{
lean_object* v_pre_902_; 
v_pre_902_ = lean_ctor_get(v_pre_901_, 0);
if (lean_obj_tag(v_pre_902_) == 0)
{
lean_object* v_fvarId_903_; lean_object* v_args_904_; lean_object* v_str_905_; lean_object* v_str_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_fvarId_903_ = lean_ctor_get(v_decl_870_, 0);
v_args_904_ = lean_ctor_get(v_value_899_, 2);
v_str_905_ = lean_ctor_get(v_declName_900_, 1);
v_str_906_ = lean_ctor_get(v_pre_901_, 1);
v___x_907_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_908_ = lean_string_dec_eq(v_str_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
lean_dec(v_prevArrayId_869_);
goto v___jp_881_;
}
else
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_910_ = lean_string_dec_eq(v_str_905_, v___x_909_);
if (v___x_910_ == 0)
{
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
lean_dec(v_prevArrayId_869_);
goto v___jp_881_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_911_ = lean_array_get_size(v_args_904_);
v___x_912_ = lean_unsigned_to_nat(3u);
v___x_913_ = lean_nat_dec_eq(v___x_911_, v___x_912_);
if (v___x_913_ == 0)
{
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
lean_dec(v_prevArrayId_869_);
goto v___jp_881_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_unsigned_to_nat(1u);
v___x_915_ = lean_array_fget(v_args_904_, v___x_914_);
if (lean_obj_tag(v___x_915_) == 1)
{
lean_object* v_fvarId_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_1033_; 
v_fvarId_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_1033_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_fvarId_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_1033_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
uint8_t v___x_920_; 
v___x_920_ = l_Lean_instBEqFVarId_beq(v_fvarId_916_, v_prevArrayId_869_);
lean_dec(v_prevArrayId_869_);
lean_dec(v_fvarId_916_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
v___x_921_ = lean_box(0);
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 0);
lean_ctor_set(v___x_918_, 0, v___x_921_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
else
{
lean_object* v_n_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
lean_del_object(v___x_918_);
v_n_925_ = lean_nat_sub(v_size_873_, v___x_914_);
lean_dec(v_size_873_);
v___x_926_ = lean_unsigned_to_nat(2u);
v___x_927_ = lean_array_fget_borrowed(v_args_904_, v___x_926_);
lean_inc(v___x_927_);
v___x_928_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_927_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_1024_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_1024_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_1024_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
uint8_t v___x_933_; 
v___x_933_ = lean_unbox(v_a_929_);
lean_dec(v_a_929_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_936_; 
lean_dec(v_n_925_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
v___x_934_ = lean_box(0);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_934_);
v___x_936_ = v___x_931_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
else
{
uint8_t v___x_938_; 
v___x_938_ = lean_nat_dec_eq(v_n_925_, v_zero_895_);
if (v___x_938_ == 0)
{
lean_inc(v_fvarId_903_);
lean_dec_ref(v_decl_870_);
if (lean_obj_tag(v_k_871_) == 0)
{
lean_object* v_decl_939_; lean_object* v_k_940_; lean_object* v___x_941_; 
lean_del_object(v___x_931_);
v_decl_939_ = lean_ctor_get(v_k_871_, 0);
lean_inc_ref(v_decl_939_);
v_k_940_ = lean_ctor_get(v_k_871_, 1);
lean_inc_ref(v_k_940_);
lean_dec_ref_known(v_k_871_, 2);
lean_inc(v_fvarId_903_);
v___x_941_ = l_Lean_FVarIdSet_insert(v_illegalSet_872_, v_fvarId_903_);
v_prevArrayId_869_ = v_fvarId_903_;
v_decl_870_ = v_decl_939_;
v_k_871_ = v_k_940_;
v_illegalSet_872_ = v___x_941_;
v_size_873_ = v_n_925_;
goto _start;
}
else
{
lean_object* v___x_943_; lean_object* v___x_945_; 
lean_dec(v_n_925_);
lean_dec(v_fvarId_903_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
v___x_943_ = lean_box(0);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_943_);
v___x_945_ = v___x_931_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
else
{
lean_del_object(v___x_931_);
lean_dec(v_n_925_);
if (lean_obj_tag(v_k_871_) == 0)
{
lean_object* v_decl_947_; lean_object* v_value_948_; 
v_decl_947_ = lean_ctor_get(v_k_871_, 0);
lean_inc_ref(v_decl_947_);
v_value_948_ = lean_ctor_get(v_decl_947_, 3);
lean_inc(v_value_948_);
if (lean_obj_tag(v_value_948_) == 3)
{
lean_object* v_declName_949_; 
v_declName_949_ = lean_ctor_get(v_value_948_, 0);
lean_inc(v_declName_949_);
if (lean_obj_tag(v_declName_949_) == 1)
{
lean_object* v_pre_950_; 
v_pre_950_ = lean_ctor_get(v_declName_949_, 0);
lean_inc(v_pre_950_);
if (lean_obj_tag(v_pre_950_) == 1)
{
lean_object* v_pre_951_; 
v_pre_951_ = lean_ctor_get(v_pre_950_, 0);
lean_inc(v_pre_951_);
if (lean_obj_tag(v_pre_951_) == 0)
{
lean_object* v_k_952_; lean_object* v_fvarId_953_; lean_object* v_binderName_954_; lean_object* v_type_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1022_; 
v_k_952_ = lean_ctor_get(v_k_871_, 1);
v_fvarId_953_ = lean_ctor_get(v_decl_947_, 0);
v_binderName_954_ = lean_ctor_get(v_decl_947_, 1);
v_type_955_ = lean_ctor_get(v_decl_947_, 2);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_decl_947_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_decl_947_, 3);
lean_dec(v_unused_1023_);
v___x_957_ = v_decl_947_;
v_isShared_958_ = v_isSharedCheck_1022_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_type_955_);
lean_inc(v_binderName_954_);
lean_inc(v_fvarId_953_);
lean_dec(v_decl_947_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1022_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_us_959_; lean_object* v_args_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1020_; 
v_us_959_ = lean_ctor_get(v_value_948_, 1);
v_args_960_ = lean_ctor_get(v_value_948_, 2);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_value_948_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_value_948_, 0);
lean_dec(v_unused_1021_);
v___x_962_ = v_value_948_;
v_isShared_963_ = v_isSharedCheck_1020_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_args_960_);
lean_inc(v_us_959_);
lean_dec(v_value_948_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1020_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_str_964_; lean_object* v_str_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_str_964_ = lean_ctor_get(v_declName_949_, 1);
lean_inc_ref(v_str_964_);
lean_dec_ref_known(v_declName_949_, 2);
v_str_965_ = lean_ctor_get(v_pre_950_, 1);
lean_inc_ref(v_str_965_);
lean_dec_ref_known(v_pre_950_, 2);
v___x_966_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2));
v___x_967_ = lean_string_dec_eq(v_str_965_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3));
v___x_969_ = lean_string_dec_eq(v_str_965_, v___x_968_);
lean_dec_ref(v_str_965_);
if (v___x_969_ == 0)
{
lean_dec_ref(v_str_964_);
lean_del_object(v___x_962_);
lean_dec_ref(v_args_960_);
lean_dec(v_us_959_);
lean_del_object(v___x_957_);
lean_dec_ref(v_type_955_);
lean_dec(v_binderName_954_);
lean_dec(v_fvarId_953_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
else
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_971_ = lean_string_dec_eq(v_str_964_, v___x_970_);
lean_dec_ref(v_str_964_);
if (v___x_971_ == 0)
{
lean_del_object(v___x_962_);
lean_dec_ref(v_args_960_);
lean_dec(v_us_959_);
lean_del_object(v___x_957_);
lean_dec_ref(v_type_955_);
lean_dec(v_binderName_954_);
lean_dec(v_fvarId_953_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
else
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_array_get_size(v_args_960_);
v___x_973_ = lean_nat_dec_eq(v___x_972_, v___x_914_);
if (v___x_973_ == 0)
{
lean_del_object(v___x_962_);
lean_dec_ref(v_args_960_);
lean_dec(v_us_959_);
lean_del_object(v___x_957_);
lean_dec_ref(v_type_955_);
lean_dec(v_binderName_954_);
lean_dec(v_fvarId_953_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_array_fget(v_args_960_, v_zero_895_);
lean_dec_ref(v_args_960_);
if (lean_obj_tag(v___x_974_) == 1)
{
lean_object* v_fvarId_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_994_; 
v_fvarId_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_994_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_994_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_fvarId_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_994_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
uint8_t v___x_979_; 
v___x_979_ = l_Lean_instBEqFVarId_beq(v_fvarId_975_, v_fvarId_903_);
if (v___x_979_ == 0)
{
lean_del_object(v___x_977_);
lean_dec(v_fvarId_975_);
lean_del_object(v___x_962_);
lean_dec(v_us_959_);
lean_del_object(v___x_957_);
lean_dec_ref(v_type_955_);
lean_dec(v_binderName_954_);
lean_dec(v_fvarId_953_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_983_; 
lean_inc_ref(v_k_952_);
lean_inc(v_fvarId_903_);
lean_dec_ref_known(v_k_871_, 2);
lean_dec_ref(v_decl_870_);
v___x_980_ = l_Lean_Name_str___override(v_pre_951_, v___x_968_);
v___x_981_ = l_Lean_Name_str___override(v___x_980_, v___x_970_);
if (v_isShared_978_ == 0)
{
v___x_983_ = v___x_977_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_fvarId_975_);
v___x_983_ = v_reuseFailAlloc_993_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_984_ = lean_mk_empty_array_with_capacity(v___x_914_);
v___x_985_ = lean_array_push(v___x_984_, v___x_983_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 2, v___x_985_);
lean_ctor_set(v___x_962_, 0, v___x_981_);
v___x_987_ = v___x_962_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_us_959_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v___x_985_);
v___x_987_ = v_reuseFailAlloc_992_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_989_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 3, v___x_987_);
v___x_989_ = v___x_957_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_fvarId_953_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_binderName_954_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v_type_955_);
lean_ctor_set(v_reuseFailAlloc_991_, 3, v___x_987_);
v___x_989_ = v_reuseFailAlloc_991_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_FVarIdSet_insert(v_illegalSet_872_, v_fvarId_903_);
v_decl_885_ = v___x_989_;
v_k_886_ = v_k_952_;
v_illegalSet_887_ = v___x_990_;
goto v___jp_884_;
}
}
}
}
}
}
else
{
lean_dec(v___x_974_);
lean_del_object(v___x_962_);
lean_dec(v_us_959_);
lean_del_object(v___x_957_);
lean_dec_ref(v_type_955_);
lean_dec(v_binderName_954_);
lean_dec(v_fvarId_953_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
}
}
}
}
else
{
lean_object* v___x_995_; uint8_t v___x_996_; 
lean_dec_ref(v_str_965_);
v___x_995_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_996_ = lean_string_dec_eq(v_str_964_, v___x_995_);
lean_dec_ref(v_str_964_);
if (v___x_996_ == 0)
{
lean_del_object(v___x_962_);
lean_dec_ref(v_args_960_);
lean_dec(v_us_959_);
lean_del_object(v___x_957_);
lean_dec_ref(v_type_955_);
lean_dec(v_binderName_954_);
lean_dec(v_fvarId_953_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
else
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_array_get_size(v_args_960_);
v___x_998_ = lean_nat_dec_eq(v___x_997_, v___x_914_);
if (v___x_998_ == 0)
{
lean_del_object(v___x_962_);
lean_dec_ref(v_args_960_);
lean_dec(v_us_959_);
lean_del_object(v___x_957_);
lean_dec_ref(v_type_955_);
lean_dec(v_binderName_954_);
lean_dec(v_fvarId_953_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
else
{
lean_object* v___x_999_; 
v___x_999_ = lean_array_fget(v_args_960_, v_zero_895_);
lean_dec_ref(v_args_960_);
if (lean_obj_tag(v___x_999_) == 1)
{
lean_object* v_fvarId_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1019_; 
v_fvarId_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1019_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_fvarId_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1019_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
uint8_t v___x_1004_; 
v___x_1004_ = l_Lean_instBEqFVarId_beq(v_fvarId_1000_, v_fvarId_903_);
if (v___x_1004_ == 0)
{
lean_del_object(v___x_1002_);
lean_dec(v_fvarId_1000_);
lean_del_object(v___x_962_);
lean_dec(v_us_959_);
lean_del_object(v___x_957_);
lean_dec_ref(v_type_955_);
lean_dec(v_binderName_954_);
lean_dec(v_fvarId_953_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
lean_inc_ref(v_k_952_);
lean_inc(v_fvarId_903_);
lean_dec_ref_known(v_k_871_, 2);
lean_dec_ref(v_decl_870_);
v___x_1005_ = l_Lean_Name_str___override(v_pre_951_, v___x_966_);
v___x_1006_ = l_Lean_Name_str___override(v___x_1005_, v___x_995_);
if (v_isShared_1003_ == 0)
{
v___x_1008_ = v___x_1002_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_fvarId_1000_);
v___x_1008_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = lean_mk_empty_array_with_capacity(v___x_914_);
v___x_1010_ = lean_array_push(v___x_1009_, v___x_1008_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 2, v___x_1010_);
lean_ctor_set(v___x_962_, 0, v___x_1006_);
v___x_1012_ = v___x_962_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_us_959_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 3, v___x_1012_);
v___x_1014_ = v___x_957_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_fvarId_953_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_binderName_954_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_type_955_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v___x_1012_);
v___x_1014_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_FVarIdSet_insert(v_illegalSet_872_, v_fvarId_903_);
v_decl_885_ = v___x_1014_;
v_k_886_ = v_k_952_;
v_illegalSet_887_ = v___x_1015_;
goto v___jp_884_;
}
}
}
}
}
}
else
{
lean_dec(v___x_999_);
lean_del_object(v___x_962_);
lean_dec(v_us_959_);
lean_del_object(v___x_957_);
lean_dec_ref(v_type_955_);
lean_dec(v_binderName_954_);
lean_dec(v_fvarId_953_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
}
}
}
}
}
}
else
{
lean_dec(v_pre_951_);
lean_dec_ref_known(v_pre_950_, 2);
lean_dec_ref_known(v_declName_949_, 2);
lean_dec_ref_known(v_value_948_, 3);
lean_dec_ref(v_decl_947_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
}
else
{
lean_dec_ref_known(v_declName_949_, 2);
lean_dec(v_pre_950_);
lean_dec_ref_known(v_value_948_, 3);
lean_dec_ref(v_decl_947_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
}
else
{
lean_dec(v_declName_949_);
lean_dec_ref_known(v_value_948_, 3);
lean_dec_ref(v_decl_947_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
}
else
{
lean_dec(v_value_948_);
lean_dec_ref(v_decl_947_);
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
}
else
{
v_decl_885_ = v_decl_870_;
v_k_886_ = v_k_871_;
v_illegalSet_887_ = v_illegalSet_872_;
goto v___jp_884_;
}
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec(v_n_925_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
v_a_1025_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_928_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_928_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
}
else
{
lean_dec(v___x_915_);
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
lean_dec(v_prevArrayId_869_);
goto v___jp_881_;
}
}
}
}
}
else
{
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
lean_dec(v_prevArrayId_869_);
goto v___jp_881_;
}
}
else
{
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
lean_dec(v_prevArrayId_869_);
goto v___jp_881_;
}
}
else
{
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
lean_dec(v_prevArrayId_869_);
goto v___jp_881_;
}
}
else
{
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
lean_dec(v_prevArrayId_869_);
goto v___jp_881_;
}
}
v___jp_881_:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_box(0);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
v___jp_884_:
{
uint8_t v___x_888_; uint8_t v___x_889_; 
v___x_888_ = 0;
v___x_889_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_888_, v_k_886_, v_illegalSet_887_);
lean_dec(v_illegalSet_887_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_decl_885_);
lean_ctor_set(v___x_890_, 1, v_k_886_);
v___x_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_dec_ref(v_k_886_);
lean_dec_ref(v_decl_885_);
v___x_893_ = lean_box(0);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___boxed(lean_object* v_prevArrayId_1034_, lean_object* v_decl_1035_, lean_object* v_k_1036_, lean_object* v_illegalSet_1037_, lean_object* v_size_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_prevArrayId_1034_, v_decl_1035_, v_k_1036_, v_illegalSet_1037_, v_size_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(lean_object* v_decl_1049_, lean_object* v_k_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v_value_1067_; 
v_value_1067_ = lean_ctor_get(v_decl_1049_, 3);
if (lean_obj_tag(v_value_1067_) == 3)
{
lean_object* v_declName_1068_; 
v_declName_1068_ = lean_ctor_get(v_value_1067_, 0);
if (lean_obj_tag(v_declName_1068_) == 1)
{
lean_object* v_pre_1069_; 
v_pre_1069_ = lean_ctor_get(v_declName_1068_, 0);
if (lean_obj_tag(v_pre_1069_) == 1)
{
lean_object* v_pre_1070_; 
v_pre_1070_ = lean_ctor_get(v_pre_1069_, 0);
if (lean_obj_tag(v_pre_1070_) == 0)
{
lean_object* v_args_1071_; lean_object* v_str_1072_; lean_object* v_str_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v_args_1071_ = lean_ctor_get(v_value_1067_, 2);
v_str_1072_ = lean_ctor_get(v_declName_1068_, 1);
v_str_1073_ = lean_ctor_get(v_pre_1069_, 1);
v___x_1074_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1075_ = lean_string_dec_eq(v_str_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1064_;
}
else
{
lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_1077_ = lean_string_dec_eq(v_str_1072_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1064_;
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1078_ = lean_array_get_size(v_args_1071_);
v___x_1079_ = lean_unsigned_to_nat(3u);
v___x_1080_ = lean_nat_dec_eq(v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1064_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = lean_array_fget_borrowed(v_args_1071_, v___x_1081_);
if (lean_obj_tag(v___x_1082_) == 1)
{
lean_object* v_fvarId_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; 
v_fvarId_1083_ = lean_ctor_get(v___x_1082_, 0);
v___x_1084_ = lean_box(1);
v___x_1085_ = 0;
v___x_1086_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_1085_, v_fvarId_1083_, v_a_1054_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1141_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1141_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1141_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
if (lean_obj_tag(v_a_1087_) == 1)
{
lean_object* v_val_1091_; lean_object* v_fvarId_1092_; lean_object* v_value_1093_; lean_object* v_sizeFVar_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; 
lean_del_object(v___x_1089_);
v_val_1091_ = lean_ctor_get(v_a_1087_, 0);
lean_inc(v_val_1091_);
lean_dec_ref_known(v_a_1087_, 1);
v_fvarId_1092_ = lean_ctor_get(v_val_1091_, 0);
lean_inc(v_fvarId_1092_);
v_value_1093_ = lean_ctor_get(v_val_1091_, 3);
lean_inc(v_value_1093_);
lean_dec(v_val_1091_);
if (lean_obj_tag(v_value_1093_) == 3)
{
lean_object* v_declName_1116_; 
v_declName_1116_ = lean_ctor_get(v_value_1093_, 0);
lean_inc(v_declName_1116_);
if (lean_obj_tag(v_declName_1116_) == 1)
{
lean_object* v_pre_1117_; 
v_pre_1117_ = lean_ctor_get(v_declName_1116_, 0);
lean_inc(v_pre_1117_);
if (lean_obj_tag(v_pre_1117_) == 1)
{
lean_object* v_pre_1118_; 
v_pre_1118_ = lean_ctor_get(v_pre_1117_, 0);
if (lean_obj_tag(v_pre_1118_) == 0)
{
lean_object* v_args_1119_; lean_object* v_str_1120_; lean_object* v_str_1121_; uint8_t v___x_1122_; 
v_args_1119_ = lean_ctor_get(v_value_1093_, 2);
lean_inc_ref(v_args_1119_);
lean_dec_ref_known(v_value_1093_, 3);
v_str_1120_ = lean_ctor_get(v_declName_1116_, 1);
lean_inc_ref(v_str_1120_);
lean_dec_ref_known(v_declName_1116_, 2);
v_str_1121_ = lean_ctor_get(v_pre_1117_, 1);
lean_inc_ref(v_str_1121_);
lean_dec_ref_known(v_pre_1117_, 2);
v___x_1122_ = lean_string_dec_eq(v_str_1121_, v___x_1074_);
lean_dec_ref(v_str_1121_);
if (v___x_1122_ == 0)
{
lean_dec_ref(v_str_1120_);
lean_dec_ref(v_args_1119_);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1124_ = lean_string_dec_eq(v_str_1120_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1126_ = lean_string_dec_eq(v_str_1120_, v___x_1125_);
lean_dec_ref(v_str_1120_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v_args_1119_);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_array_get_size(v_args_1119_);
v___x_1128_ = lean_unsigned_to_nat(2u);
v___x_1129_ = lean_nat_dec_eq(v___x_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_dec_ref(v_args_1119_);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_array_fget(v_args_1119_, v___x_1081_);
lean_dec_ref(v_args_1119_);
if (lean_obj_tag(v___x_1130_) == 1)
{
lean_object* v_fvarId_1131_; 
v_fvarId_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_fvarId_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v_sizeFVar_1095_ = v_fvarId_1131_;
v___y_1096_ = v_a_1051_;
v___y_1097_ = v_a_1052_;
v___y_1098_ = v_a_1053_;
v___y_1099_ = v_a_1054_;
v___y_1100_ = v_a_1055_;
v___y_1101_ = v_a_1056_;
goto v___jp_1094_;
}
else
{
lean_dec(v___x_1130_);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
}
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
lean_dec_ref(v_str_1120_);
v___x_1132_ = lean_array_get_size(v_args_1119_);
v___x_1133_ = lean_unsigned_to_nat(2u);
v___x_1134_ = lean_nat_dec_eq(v___x_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_dec_ref(v_args_1119_);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_array_fget(v_args_1119_, v___x_1081_);
lean_dec_ref(v_args_1119_);
if (lean_obj_tag(v___x_1135_) == 1)
{
lean_object* v_fvarId_1136_; 
v_fvarId_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_fvarId_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v_sizeFVar_1095_ = v_fvarId_1136_;
v___y_1096_ = v_a_1051_;
v___y_1097_ = v_a_1052_;
v___y_1098_ = v_a_1053_;
v___y_1099_ = v_a_1054_;
v___y_1100_ = v_a_1055_;
v___y_1101_ = v_a_1056_;
goto v___jp_1094_;
}
else
{
lean_dec(v___x_1135_);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1117_, 2);
lean_dec_ref_known(v_declName_1116_, 2);
lean_dec_ref_known(v_value_1093_, 3);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
}
else
{
lean_dec_ref_known(v_declName_1116_, 2);
lean_dec(v_pre_1117_);
lean_dec_ref_known(v_value_1093_, 3);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
}
else
{
lean_dec(v_declName_1116_);
lean_dec_ref_known(v_value_1093_, 3);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
}
else
{
lean_dec(v_value_1093_);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
v___jp_1094_:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1085_, v_sizeFVar_1095_, v___y_1099_);
lean_dec(v_sizeFVar_1095_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 1);
if (lean_obj_tag(v_a_1103_) == 1)
{
lean_object* v_val_1104_; 
v_val_1104_ = lean_ctor_get(v_a_1103_, 0);
lean_inc(v_val_1104_);
lean_dec_ref_known(v_a_1103_, 1);
if (lean_obj_tag(v_val_1104_) == 0)
{
lean_object* v_value_1105_; 
v_value_1105_ = lean_ctor_get(v_val_1104_, 0);
lean_inc_ref(v_value_1105_);
lean_dec_ref_known(v_val_1104_, 1);
if (lean_obj_tag(v_value_1105_) == 0)
{
lean_object* v_val_1106_; lean_object* v___x_1107_; 
v_val_1106_ = lean_ctor_get(v_value_1105_, 0);
lean_inc(v_val_1106_);
lean_dec_ref_known(v_value_1105_, 1);
v___x_1107_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_fvarId_1092_, v_decl_1049_, v_k_1050_, v___x_1084_, v_val_1106_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1107_;
}
else
{
lean_dec_ref(v_value_1105_);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1058_;
}
}
else
{
lean_dec(v_val_1104_);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1058_;
}
}
else
{
lean_dec(v_a_1103_);
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1058_;
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v_fvarId_1092_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
v_a_1108_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1102_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1102_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_dec(v_a_1087_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
v___x_1137_ = lean_box(0);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1137_);
v___x_1139_ = v___x_1089_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
v_a_1142_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1086_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1086_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
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
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1064_;
}
}
}
}
}
else
{
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1064_;
}
}
else
{
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1064_;
}
}
else
{
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1064_;
}
}
else
{
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1064_;
}
v___jp_1058_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
v___jp_1061_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
v___jp_1064_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___boxed(lean_object* v_decl_1150_, lean_object* v_k_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1150_, v_k_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
return v_res_1159_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1);
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(lean_object* v_env_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v___x_1168_; lean_object* v_nextMacroScope_1169_; lean_object* v_ngen_1170_; lean_object* v_auxDeclNGen_1171_; lean_object* v_traceState_1172_; lean_object* v_messages_1173_; lean_object* v_infoState_1174_; lean_object* v_snapshotTasks_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1186_; 
v___x_1168_ = lean_st_ref_take(v___y_1166_);
v_nextMacroScope_1169_ = lean_ctor_get(v___x_1168_, 1);
v_ngen_1170_ = lean_ctor_get(v___x_1168_, 2);
v_auxDeclNGen_1171_ = lean_ctor_get(v___x_1168_, 3);
v_traceState_1172_ = lean_ctor_get(v___x_1168_, 4);
v_messages_1173_ = lean_ctor_get(v___x_1168_, 6);
v_infoState_1174_ = lean_ctor_get(v___x_1168_, 7);
v_snapshotTasks_1175_ = lean_ctor_get(v___x_1168_, 8);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; lean_object* v_unused_1188_; 
v_unused_1187_ = lean_ctor_get(v___x_1168_, 5);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v___x_1168_, 0);
lean_dec(v_unused_1188_);
v___x_1177_ = v___x_1168_;
v_isShared_1178_ = v_isSharedCheck_1186_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snapshotTasks_1175_);
lean_inc(v_infoState_1174_);
lean_inc(v_messages_1173_);
lean_inc(v_traceState_1172_);
lean_inc(v_auxDeclNGen_1171_);
lean_inc(v_ngen_1170_);
lean_inc(v_nextMacroScope_1169_);
lean_dec(v___x_1168_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1186_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 5, v___x_1180_);
lean_ctor_set(v___x_1177_, 0, v_env_1165_);
v___x_1182_ = v___x_1177_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_env_1165_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_nextMacroScope_1169_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_ngen_1170_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_auxDeclNGen_1171_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v_traceState_1172_);
lean_ctor_set(v_reuseFailAlloc_1185_, 5, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1185_, 6, v_messages_1173_);
lean_ctor_set(v_reuseFailAlloc_1185_, 7, v_infoState_1174_);
lean_ctor_set(v_reuseFailAlloc_1185_, 8, v_snapshotTasks_1175_);
v___x_1182_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_st_ref_put(v___y_1166_, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1179_);
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___boxed(lean_object* v_env_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1189_, v___y_1190_);
lean_dec(v___y_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(lean_object* v_env_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1193_, v___y_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(lean_object* v_env_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_env_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(size_t v_sz_1211_, size_t v_i_1212_, lean_object* v_bs_1213_, uint8_t v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_usize_dec_lt(v_i_1212_, v_sz_1211_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v_bs_1213_);
return v___x_1222_;
}
else
{
uint8_t v___x_1223_; lean_object* v_v_1224_; lean_object* v___x_1225_; lean_object* v_bs_x27_1226_; lean_object* v___x_1227_; 
v___x_1223_ = 0;
v_v_1224_ = lean_array_uget(v_bs_1213_, v_i_1212_);
v___x_1225_ = lean_unsigned_to_nat(0u);
v_bs_x27_1226_ = lean_array_uset(v_bs_1213_, v_i_1212_, v___x_1225_);
v___x_1227_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_1223_, v_v_1224_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; size_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_add(v_i_1212_, v___x_1229_);
v___x_1231_ = lean_array_uset(v_bs_x27_1226_, v_i_1212_, v_a_1228_);
v_i_1212_ = v___x_1230_;
v_bs_1213_ = v___x_1231_;
goto _start;
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v_bs_x27_1226_);
v_a_1233_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1227_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1227_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(lean_object* v_sz_1241_, lean_object* v_i_1242_, lean_object* v_bs_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
size_t v_sz_boxed_1251_; size_t v_i_boxed_1252_; uint8_t v___y_8186__boxed_1253_; lean_object* v_res_1254_; 
v_sz_boxed_1251_ = lean_unbox_usize(v_sz_1241_);
lean_dec(v_sz_1241_);
v_i_boxed_1252_ = lean_unbox_usize(v_i_1242_);
lean_dec(v_i_1242_);
v___y_8186__boxed_1253_ = lean_unbox(v___y_1244_);
v_res_1254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_boxed_1251_, v_i_boxed_1252_, v_bs_1243_, v___y_8186__boxed_1253_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
return v_res_1254_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_unsigned_to_nat(16u);
v___x_1259_ = lean_mk_array(v___x_1258_, v___x_1257_);
return v___x_1259_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___x_1260_);
return v___x_1262_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3(void){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(lean_object* v_decl_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_type_1280_; lean_object* v_value_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_type_1280_ = lean_ctor_get(v_decl_1272_, 2);
lean_inc_ref(v_type_1280_);
v_value_1281_ = lean_ctor_get(v_decl_1272_, 3);
v___x_1282_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0));
v___x_1283_ = lean_st_mk_ref(v___x_1282_);
lean_inc(v_value_1281_);
v___x_1284_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_1281_, v___x_1283_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; lean_object* v_a_1294_; lean_object* v___x_1376_; size_t v_sz_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
lean_dec_ref_known(v___x_1284_, 1);
v___x_1285_ = lean_st_ref_get(v___x_1283_);
lean_dec(v___x_1283_);
v___x_1286_ = l_Array_reverse___redArg(v___x_1285_);
v___x_1287_ = 0;
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_decl_1272_);
v___x_1289_ = lean_array_push(v___x_1286_, v___x_1288_);
v___x_1290_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_1291_ = 0;
v___x_1292_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3);
v___x_1376_ = lean_st_mk_ref(v___x_1290_);
v_sz_1377_ = lean_array_size(v___x_1289_);
v___x_1378_ = ((size_t)0ULL);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_1377_, v___x_1378_, v___x_1289_, v___x_1291_, v___x_1376_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1381_ = lean_st_ref_get(v___x_1376_);
lean_dec(v___x_1376_);
lean_dec(v___x_1381_);
v_a_1294_ = v_a_1380_;
goto v___jp_1293_;
}
else
{
lean_dec(v___x_1376_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1382_; 
v_a_1382_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1379_, 1);
v_a_1294_ = v_a_1382_;
goto v___jp_1293_;
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v_type_1280_);
v_a_1383_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1379_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1379_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
v___jp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v_env_1305_; lean_object* v___x_1306_; 
v___x_1295_ = lean_array_get_size(v_a_1294_);
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_nat_sub(v___x_1295_, v___x_1296_);
v___x_1298_ = lean_array_get_borrowed(v___x_1292_, v_a_1294_, v___x_1297_);
lean_dec(v___x_1297_);
v___x_1299_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1298_);
v___x_1300_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
v___x_1301_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_a_1294_, v___x_1300_);
lean_dec_ref(v_a_1294_);
v___x_1302_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4));
lean_inc_ref(v___x_1301_);
v___x_1303_ = l_Lean_Compiler_LCNF_Code_toExpr(v___x_1287_, v___x_1301_, v___x_1302_);
v___x_1304_ = lean_st_ref_get(v_a_1278_);
v_env_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc_ref_n(v_env_1305_, 2);
lean_dec(v___x_1304_);
v___x_1306_ = l_Lean_getClosedTermName_x3f(v_env_1305_, v___x_1303_);
if (lean_obj_tag(v___x_1306_) == 1)
{
lean_object* v_val_1307_; lean_object* v___x_1308_; 
lean_dec_ref(v_env_1305_);
lean_dec_ref(v___x_1303_);
lean_dec_ref(v_type_1280_);
v_val_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_val_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1287_, v___x_1301_, v_a_1276_);
lean_dec_ref(v___x_1301_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v___x_1308_, 0);
lean_dec(v_unused_1316_);
v___x_1310_ = v___x_1308_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_dec(v___x_1308_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v_val_1307_);
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_val_1307_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_val_1307_);
v_a_1317_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1308_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1308_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v___x_1325_; lean_object* v_baseName_1326_; lean_object* v_decls_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v___x_1306_);
v___x_1325_ = lean_st_ref_get(v_a_1274_);
v_baseName_1326_ = lean_ctor_get(v_a_1273_, 0);
v_decls_1327_ = lean_ctor_get(v___x_1325_, 0);
lean_inc_ref(v_decls_1327_);
lean_dec(v___x_1325_);
v___x_1328_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6));
v___x_1329_ = lean_array_get_size(v_decls_1327_);
lean_dec_ref(v_decls_1327_);
v___x_1330_ = lean_name_append_index_after(v___x_1328_, v___x_1329_);
lean_inc(v_baseName_1326_);
v___x_1331_ = l_Lean_Name_append(v_baseName_1326_, v___x_1330_);
lean_inc(v___x_1331_);
v___x_1332_ = l_Lean_cacheClosedTermName(v_env_1305_, v___x_1303_, v___x_1331_);
v___x_1333_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v___x_1332_, v_a_1278_);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v___x_1333_, 0);
lean_dec(v_unused_1375_);
v___x_1335_ = v___x_1333_;
v_isShared_1336_ = v_isSharedCheck_1374_;
goto v_resetjp_1334_;
}
else
{
lean_dec(v___x_1333_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1374_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1337_ = lean_box(0);
v___x_1338_ = 1;
lean_inc(v___x_1331_);
v___x_1339_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1339_, 0, v___x_1331_);
lean_ctor_set(v___x_1339_, 1, v___x_1337_);
lean_ctor_set(v___x_1339_, 2, v_type_1280_);
lean_ctor_set(v___x_1339_, 3, v___x_1302_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*4, v___x_1338_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1301_);
v___x_1341_ = v___x_1335_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1301_);
v___x_1341_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7));
v___x_1343_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1343_, 0, v___x_1339_);
lean_ctor_set(v___x_1343_, 1, v___x_1341_);
lean_ctor_set(v___x_1343_, 2, v___x_1342_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*3, v___x_1291_);
lean_inc_ref(v___x_1343_);
v___x_1344_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1343_, v_a_1278_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1363_; 
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; 
v_unused_1364_ = lean_ctor_get(v___x_1344_, 0);
lean_dec(v_unused_1364_);
v___x_1346_ = v___x_1344_;
v_isShared_1347_ = v_isSharedCheck_1363_;
goto v_resetjp_1345_;
}
else
{
lean_dec(v___x_1344_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1363_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v_decls_1349_; lean_object* v_fvarDecisionCache_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1362_; 
v___x_1348_ = lean_st_ref_take(v_a_1274_);
v_decls_1349_ = lean_ctor_get(v___x_1348_, 0);
v_fvarDecisionCache_1350_ = lean_ctor_get(v___x_1348_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1352_ = v___x_1348_;
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_fvarDecisionCache_1350_);
lean_inc(v_decls_1349_);
lean_dec(v___x_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1362_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_array_push(v_decls_1349_, v___x_1343_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1354_);
v___x_1356_ = v___x_1352_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_fvarDecisionCache_1350_);
v___x_1356_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_st_ref_put(v_a_1274_, v___x_1356_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1331_);
v___x_1359_ = v___x_1346_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1331_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref_known(v___x_1343_, 3);
lean_dec(v___x_1331_);
v_a_1365_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1344_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1344_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
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
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_dec(v___x_1283_);
lean_dec_ref(v_type_1280_);
lean_dec_ref(v_decl_1272_);
v_a_1391_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1284_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1284_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___boxed(lean_object* v_decl_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
return v_res_1407_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(lean_object* v_msg_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0);
v___x_1411_ = lean_panic_fn_borrowed(v___x_1410_, v_msg_1409_);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1415_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2));
v___x_1416_ = lean_unsigned_to_nat(9u);
v___x_1417_ = lean_unsigned_to_nat(650u);
v___x_1418_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1));
v___x_1419_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0));
v___x_1420_ = l_mkPanicMessageWithDecl(v___x_1419_, v___x_1418_, v___x_1417_, v___x_1416_, v___x_1415_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* v_code_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_decl_1432_; lean_object* v_k_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; 
switch(lean_obj_tag(v_code_1423_))
{
case 0:
{
lean_object* v_decl_1547_; lean_object* v_k_1548_; lean_object* v_value_1549_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; 
v_decl_1547_ = lean_ctor_get(v_code_1423_, 0);
v_k_1548_ = lean_ctor_get(v_code_1423_, 1);
v_value_1549_ = lean_ctor_get(v_decl_1547_, 3);
lean_inc(v_value_1549_);
if (lean_obj_tag(v_value_1549_) == 3)
{
lean_object* v_declName_1746_; 
v_declName_1746_ = lean_ctor_get(v_value_1549_, 0);
if (lean_obj_tag(v_declName_1746_) == 1)
{
lean_object* v_pre_1747_; 
v_pre_1747_ = lean_ctor_get(v_declName_1746_, 0);
if (lean_obj_tag(v_pre_1747_) == 1)
{
lean_object* v_pre_1748_; 
v_pre_1748_ = lean_ctor_get(v_pre_1747_, 0);
if (lean_obj_tag(v_pre_1748_) == 0)
{
lean_object* v_args_1749_; lean_object* v_str_1750_; lean_object* v_str_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v_sizeId_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; 
v_args_1749_ = lean_ctor_get(v_value_1549_, 2);
v_str_1750_ = lean_ctor_get(v_declName_1746_, 1);
v_str_1751_ = lean_ctor_get(v_pre_1747_, 1);
v___x_1752_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1753_ = lean_string_dec_eq(v_str_1751_, v___x_1752_);
if (v___x_1753_ == 0)
{
v___y_1551_ = v_a_1424_;
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_2092_ = lean_string_dec_eq(v_str_1750_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_2094_ = lean_string_dec_eq(v_str_1750_, v___x_2093_);
if (v___x_2094_ == 0)
{
v___y_1551_ = v_a_1424_;
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2095_ = lean_array_get_size(v_args_1749_);
v___x_2096_ = lean_unsigned_to_nat(2u);
v___x_2097_ = lean_nat_dec_eq(v___x_2095_, v___x_2096_);
if (v___x_2097_ == 0)
{
v___y_1551_ = v_a_1424_;
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_unsigned_to_nat(1u);
v___x_2099_ = lean_array_fget_borrowed(v_args_1749_, v___x_2098_);
if (lean_obj_tag(v___x_2099_) == 1)
{
lean_object* v_fvarId_2100_; 
v_fvarId_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_fvarId_2100_);
v_sizeId_1959_ = v_fvarId_2100_;
v___y_1960_ = v_a_1424_;
v___y_1961_ = v_a_1425_;
v___y_1962_ = v_a_1426_;
v___y_1963_ = v_a_1427_;
v___y_1964_ = v_a_1428_;
v___y_1965_ = v_a_1429_;
goto v___jp_1958_;
}
else
{
v___y_1551_ = v_a_1424_;
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
goto v___jp_1550_;
}
}
}
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2101_ = lean_array_get_size(v_args_1749_);
v___x_2102_ = lean_unsigned_to_nat(2u);
v___x_2103_ = lean_nat_dec_eq(v___x_2101_, v___x_2102_);
if (v___x_2103_ == 0)
{
v___y_1551_ = v_a_1424_;
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = lean_array_fget_borrowed(v_args_1749_, v___x_2104_);
if (lean_obj_tag(v___x_2105_) == 1)
{
lean_object* v_fvarId_2106_; 
v_fvarId_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_fvarId_2106_);
v_sizeId_1959_ = v_fvarId_2106_;
v___y_1960_ = v_a_1424_;
v___y_1961_ = v_a_1425_;
v___y_1962_ = v_a_1426_;
v___y_1963_ = v_a_1427_;
v___y_1964_ = v_a_1428_;
v___y_1965_ = v_a_1429_;
goto v___jp_1958_;
}
else
{
v___y_1551_ = v_a_1424_;
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
goto v___jp_1550_;
}
}
}
}
v___jp_1754_:
{
lean_object* v___x_1761_; 
lean_inc_ref(v_k_1548_);
lean_inc_ref(v_decl_1547_);
v___x_1761_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1547_, v_k_1548_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
if (lean_obj_tag(v_a_1762_) == 1)
{
lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1834_; 
v_isSharedCheck_1834_ = !lean_is_exclusive(v_value_1549_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; lean_object* v_unused_1836_; lean_object* v_unused_1837_; 
v_unused_1835_ = lean_ctor_get(v_value_1549_, 2);
lean_dec(v_unused_1835_);
v_unused_1836_ = lean_ctor_get(v_value_1549_, 1);
lean_dec(v_unused_1836_);
v_unused_1837_ = lean_ctor_get(v_value_1549_, 0);
lean_dec(v_unused_1837_);
v___x_1764_ = v_value_1549_;
v_isShared_1765_ = v_isSharedCheck_1834_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v_value_1549_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1834_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v_val_1766_; lean_object* v_fst_1767_; lean_object* v_snd_1768_; lean_object* v___x_1769_; 
v_val_1766_ = lean_ctor_get(v_a_1762_, 0);
lean_inc(v_val_1766_);
lean_dec_ref_known(v_a_1762_, 1);
v_fst_1767_ = lean_ctor_get(v_val_1766_, 0);
lean_inc_n(v_fst_1767_, 2);
v_snd_1768_ = lean_ctor_get(v_val_1766_, 1);
lean_inc(v_snd_1768_);
lean_dec(v_val_1766_);
v___x_1769_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1767_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = 0;
v___x_1772_ = lean_box(0);
v___x_1773_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 2, v___x_1773_);
lean_ctor_set(v___x_1764_, 1, v___x_1772_);
lean_ctor_set(v___x_1764_, 0, v_a_1770_);
v___x_1775_ = v___x_1764_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1770_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1825_, 2, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1771_, v_fst_1767_, v___x_1775_, v___y_1758_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1768_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1816_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1781_ = v___x_1778_;
v_isShared_1782_ = v_isSharedCheck_1816_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1778_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1816_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
size_t v___x_1783_; size_t v___x_1784_; uint8_t v___x_1785_; 
v___x_1783_ = lean_ptr_addr(v_k_1548_);
v___x_1784_ = lean_ptr_addr(v_a_1779_);
v___x_1785_ = lean_usize_dec_eq(v___x_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1795_; 
v_isSharedCheck_1795_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; lean_object* v_unused_1797_; 
v_unused_1796_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1796_);
v_unused_1797_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1797_);
v___x_1787_ = v_code_1423_;
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
else
{
lean_dec(v_code_1423_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v_a_1779_);
lean_ctor_set(v___x_1787_, 0, v_a_1777_);
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1777_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_a_1779_);
v___x_1790_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1792_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1790_);
v___x_1792_ = v___x_1781_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
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
else
{
size_t v___x_1798_; size_t v___x_1799_; uint8_t v___x_1800_; 
v___x_1798_ = lean_ptr_addr(v_decl_1547_);
v___x_1799_ = lean_ptr_addr(v_a_1777_);
v___x_1800_ = lean_usize_dec_eq(v___x_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1810_; 
v_isSharedCheck_1810_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; lean_object* v_unused_1812_; 
v_unused_1811_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1811_);
v_unused_1812_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1812_);
v___x_1802_ = v_code_1423_;
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
else
{
lean_dec(v_code_1423_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1810_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v_a_1779_);
lean_ctor_set(v___x_1802_, 0, v_a_1777_);
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1777_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_a_1779_);
v___x_1805_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1807_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1805_);
v___x_1807_ = v___x_1781_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v___x_1814_; 
lean_dec(v_a_1779_);
lean_dec(v_a_1777_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v_code_1423_);
v___x_1814_ = v___x_1781_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_code_1423_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
else
{
lean_dec(v_a_1777_);
lean_dec_ref_known(v_code_1423_, 2);
return v___x_1778_;
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_snd_1768_);
lean_dec_ref_known(v_code_1423_, 2);
v_a_1817_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1776_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1776_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_snd_1768_);
lean_dec(v_fst_1767_);
lean_del_object(v___x_1764_);
lean_dec_ref_known(v_code_1423_, 2);
v_a_1826_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1769_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1769_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
else
{
lean_object* v___x_1838_; 
lean_dec(v_a_1762_);
v___x_1838_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1753_, v_value_1549_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; uint8_t v___x_1840_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
v___x_1840_ = lean_unbox(v_a_1839_);
lean_dec(v_a_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
lean_inc_ref(v_k_1548_);
v___x_1841_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1548_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1878_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1878_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1878_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
size_t v___x_1846_; size_t v___x_1847_; uint8_t v___x_1848_; 
v___x_1846_ = lean_ptr_addr(v_k_1548_);
v___x_1847_ = lean_ptr_addr(v_a_1842_);
v___x_1848_ = lean_usize_dec_eq(v___x_1846_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1858_; 
lean_inc_ref(v_decl_1547_);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; lean_object* v_unused_1860_; 
v_unused_1859_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1860_);
v___x_1850_ = v_code_1423_;
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
else
{
lean_dec(v_code_1423_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1858_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v_a_1842_);
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_decl_1547_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_a_1842_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1853_);
v___x_1855_ = v___x_1844_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
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
else
{
size_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = lean_ptr_addr(v_decl_1547_);
v___x_1862_ = lean_usize_dec_eq(v___x_1861_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1872_; 
lean_inc_ref(v_decl_1547_);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; lean_object* v_unused_1874_; 
v_unused_1873_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1874_);
v___x_1864_ = v_code_1423_;
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
else
{
lean_dec(v_code_1423_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 1, v_a_1842_);
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_decl_1547_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_a_1842_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1867_);
v___x_1869_ = v___x_1844_;
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
lean_object* v___x_1876_; 
lean_dec(v_a_1842_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v_code_1423_);
v___x_1876_ = v___x_1844_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_code_1423_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1423_, 2);
return v___x_1841_;
}
}
else
{
lean_object* v___x_1879_; 
lean_inc_ref(v_decl_1547_);
v___x_1879_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1547_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1879_, 1);
v___x_1881_ = 0;
v___x_1882_ = lean_box(0);
v___x_1883_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1884_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1884_, 0, v_a_1880_);
lean_ctor_set(v___x_1884_, 1, v___x_1882_);
lean_ctor_set(v___x_1884_, 2, v___x_1883_);
lean_inc_ref(v_decl_1547_);
v___x_1885_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1881_, v_decl_1547_, v___x_1884_, v___y_1758_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
lean_inc_ref(v_k_1548_);
v___x_1887_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1548_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1925_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1890_ = v___x_1887_;
v_isShared_1891_ = v_isSharedCheck_1925_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1925_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
size_t v___x_1892_; size_t v___x_1893_; uint8_t v___x_1894_; 
v___x_1892_ = lean_ptr_addr(v_k_1548_);
v___x_1893_ = lean_ptr_addr(v_a_1888_);
v___x_1894_ = lean_usize_dec_eq(v___x_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1904_; 
v_isSharedCheck_1904_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; lean_object* v_unused_1906_; 
v_unused_1905_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1906_);
v___x_1896_ = v_code_1423_;
v_isShared_1897_ = v_isSharedCheck_1904_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v_code_1423_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1904_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v_a_1888_);
lean_ctor_set(v___x_1896_, 0, v_a_1886_);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1886_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_a_1888_);
v___x_1899_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
lean_object* v___x_1901_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1899_);
v___x_1901_ = v___x_1890_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
size_t v___x_1907_; size_t v___x_1908_; uint8_t v___x_1909_; 
v___x_1907_ = lean_ptr_addr(v_decl_1547_);
v___x_1908_ = lean_ptr_addr(v_a_1886_);
v___x_1909_ = lean_usize_dec_eq(v___x_1907_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1919_; 
v_isSharedCheck_1919_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; lean_object* v_unused_1921_; 
v_unused_1920_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1920_);
v_unused_1921_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1921_);
v___x_1911_ = v_code_1423_;
v_isShared_1912_ = v_isSharedCheck_1919_;
goto v_resetjp_1910_;
}
else
{
lean_dec(v_code_1423_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1919_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 1, v_a_1888_);
lean_ctor_set(v___x_1911_, 0, v_a_1886_);
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1886_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_a_1888_);
v___x_1914_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1914_);
v___x_1916_ = v___x_1890_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v___x_1923_; 
lean_dec(v_a_1888_);
lean_dec(v_a_1886_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v_code_1423_);
v___x_1923_ = v___x_1890_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_code_1423_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
else
{
lean_dec(v_a_1886_);
lean_dec_ref_known(v_code_1423_, 2);
return v___x_1887_;
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref_known(v_code_1423_, 2);
v_a_1926_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1885_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1885_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref_known(v_code_1423_, 2);
v_a_1934_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1879_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1879_);
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
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref_known(v_code_1423_, 2);
v_a_1942_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1838_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1838_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref_known(v_value_1549_, 3);
lean_dec_ref_known(v_code_1423_, 2);
v_a_1950_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1761_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1761_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
v___jp_1958_:
{
uint8_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = 0;
v___x_1967_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1966_, v_sizeId_1959_, v___y_1963_);
lean_dec(v_sizeId_1959_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
if (lean_obj_tag(v_a_1968_) == 1)
{
lean_object* v_val_1969_; 
v_val_1969_ = lean_ctor_get(v_a_1968_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v_a_1968_, 1);
if (lean_obj_tag(v_val_1969_) == 0)
{
lean_object* v_value_1970_; 
v_value_1970_ = lean_ctor_get(v_val_1969_, 0);
lean_inc_ref(v_value_1970_);
lean_dec_ref_known(v_val_1969_, 1);
if (lean_obj_tag(v_value_1970_) == 0)
{
lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2079_; 
v_isSharedCheck_2079_ = !lean_is_exclusive(v_value_1549_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; lean_object* v_unused_2081_; lean_object* v_unused_2082_; 
v_unused_2080_ = lean_ctor_get(v_value_1549_, 2);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v_value_1549_, 1);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v_value_1549_, 0);
lean_dec(v_unused_2082_);
v___x_1972_ = v_value_1549_;
v_isShared_1973_ = v_isSharedCheck_2079_;
goto v_resetjp_1971_;
}
else
{
lean_dec(v_value_1549_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2079_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_val_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v_val_1974_ = lean_ctor_get(v_value_1970_, 0);
lean_inc(v_val_1974_);
lean_dec_ref_known(v_value_1970_, 1);
v___x_1975_ = lean_unsigned_to_nat(0u);
v___x_1976_ = lean_nat_dec_eq(v_val_1974_, v___x_1975_);
lean_dec(v_val_1974_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_del_object(v___x_1972_);
lean_inc_ref(v_k_1548_);
v___x_1977_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1548_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2014_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_2014_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2014_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
size_t v___x_1982_; size_t v___x_1983_; uint8_t v___x_1984_; 
v___x_1982_ = lean_ptr_addr(v_k_1548_);
v___x_1983_ = lean_ptr_addr(v_a_1978_);
v___x_1984_ = lean_usize_dec_eq(v___x_1982_, v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1994_; 
lean_inc_ref(v_decl_1547_);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; lean_object* v_unused_1996_; 
v_unused_1995_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1995_);
v_unused_1996_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1996_);
v___x_1986_ = v_code_1423_;
v_isShared_1987_ = v_isSharedCheck_1994_;
goto v_resetjp_1985_;
}
else
{
lean_dec(v_code_1423_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1994_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 1, v_a_1978_);
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_decl_1547_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_a_1978_);
v___x_1989_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1989_);
v___x_1991_ = v___x_1980_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
size_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = lean_ptr_addr(v_decl_1547_);
v___x_1998_ = lean_usize_dec_eq(v___x_1997_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2008_; 
lean_inc_ref(v_decl_1547_);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; lean_object* v_unused_2010_; 
v_unused_2009_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_2009_);
v_unused_2010_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_2010_);
v___x_2000_ = v_code_1423_;
v_isShared_2001_ = v_isSharedCheck_2008_;
goto v_resetjp_1999_;
}
else
{
lean_dec(v_code_1423_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2008_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v_a_1978_);
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_decl_1547_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_a_1978_);
v___x_2003_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
lean_object* v___x_2005_; 
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_2003_);
v___x_2005_ = v___x_1980_;
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
lean_object* v___x_2012_; 
lean_dec(v_a_1978_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v_code_1423_);
v___x_2012_ = v___x_1980_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_code_1423_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1423_, 2);
return v___x_1977_;
}
}
else
{
lean_object* v___x_2015_; 
lean_inc_ref(v_decl_1547_);
v___x_2015_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1547_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = lean_box(0);
v___x_2018_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 2, v___x_2018_);
lean_ctor_set(v___x_1972_, 1, v___x_2017_);
lean_ctor_set(v___x_1972_, 0, v_a_2016_);
v___x_2020_ = v___x_1972_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2016_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2070_, 2, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; 
lean_inc_ref(v_decl_1547_);
v___x_2021_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1966_, v_decl_1547_, v___x_2020_, v___y_1963_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
lean_inc_ref(v_k_1548_);
v___x_2023_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1548_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2061_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2061_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2061_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
size_t v___x_2028_; size_t v___x_2029_; uint8_t v___x_2030_; 
v___x_2028_ = lean_ptr_addr(v_k_1548_);
v___x_2029_ = lean_ptr_addr(v_a_2024_);
v___x_2030_ = lean_usize_dec_eq(v___x_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2040_; 
v_isSharedCheck_2040_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; lean_object* v_unused_2042_; 
v_unused_2041_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_2041_);
v_unused_2042_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_2042_);
v___x_2032_ = v_code_1423_;
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
else
{
lean_dec(v_code_1423_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2040_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 1, v_a_2024_);
lean_ctor_set(v___x_2032_, 0, v_a_2022_);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2022_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_a_2024_);
v___x_2035_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2035_);
v___x_2037_ = v___x_2026_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
size_t v___x_2043_; size_t v___x_2044_; uint8_t v___x_2045_; 
v___x_2043_ = lean_ptr_addr(v_decl_1547_);
v___x_2044_ = lean_ptr_addr(v_a_2022_);
v___x_2045_ = lean_usize_dec_eq(v___x_2043_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2055_; 
v_isSharedCheck_2055_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; lean_object* v_unused_2057_; 
v_unused_2056_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_2057_);
v___x_2047_ = v_code_1423_;
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
else
{
lean_dec(v_code_1423_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2055_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v_a_2024_);
lean_ctor_set(v___x_2047_, 0, v_a_2022_);
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2022_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_a_2024_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2052_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2050_);
v___x_2052_ = v___x_2026_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
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
else
{
lean_object* v___x_2059_; 
lean_dec(v_a_2024_);
lean_dec(v_a_2022_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v_code_1423_);
v___x_2059_ = v___x_2026_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_code_1423_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
else
{
lean_dec(v_a_2022_);
lean_dec_ref_known(v_code_1423_, 2);
return v___x_2023_;
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref_known(v_code_1423_, 2);
v_a_2062_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2021_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2021_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_del_object(v___x_1972_);
lean_dec_ref_known(v_code_1423_, 2);
v_a_2071_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2015_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2015_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_1970_);
v___y_1755_ = v___y_1960_;
v___y_1756_ = v___y_1961_;
v___y_1757_ = v___y_1962_;
v___y_1758_ = v___y_1963_;
v___y_1759_ = v___y_1964_;
v___y_1760_ = v___y_1965_;
goto v___jp_1754_;
}
}
else
{
lean_dec(v_val_1969_);
v___y_1755_ = v___y_1960_;
v___y_1756_ = v___y_1961_;
v___y_1757_ = v___y_1962_;
v___y_1758_ = v___y_1963_;
v___y_1759_ = v___y_1964_;
v___y_1760_ = v___y_1965_;
goto v___jp_1754_;
}
}
else
{
lean_dec(v_a_1968_);
v___y_1755_ = v___y_1960_;
v___y_1756_ = v___y_1961_;
v___y_1757_ = v___y_1962_;
v___y_1758_ = v___y_1963_;
v___y_1759_ = v___y_1964_;
v___y_1760_ = v___y_1965_;
goto v___jp_1754_;
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec_ref_known(v_value_1549_, 3);
lean_dec_ref_known(v_code_1423_, 2);
v_a_2083_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_1967_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_1967_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
else
{
v___y_1551_ = v_a_1424_;
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
goto v___jp_1550_;
}
}
else
{
v___y_1551_ = v_a_1424_;
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
goto v___jp_1550_;
}
}
else
{
v___y_1551_ = v_a_1424_;
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
goto v___jp_1550_;
}
}
else
{
v___y_1551_ = v_a_1424_;
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
goto v___jp_1550_;
}
v___jp_1550_:
{
lean_object* v___x_1557_; 
lean_inc_ref(v_k_1548_);
lean_inc_ref(v_decl_1547_);
v___x_1557_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1547_, v_k_1548_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
if (lean_obj_tag(v_a_1558_) == 1)
{
lean_object* v_val_1559_; lean_object* v_fst_1560_; lean_object* v_snd_1561_; lean_object* v___x_1562_; 
lean_dec(v_value_1549_);
v_val_1559_ = lean_ctor_get(v_a_1558_, 0);
lean_inc(v_val_1559_);
lean_dec_ref_known(v_a_1558_, 1);
v_fst_1560_ = lean_ctor_get(v_val_1559_, 0);
lean_inc_n(v_fst_1560_, 2);
v_snd_1561_ = lean_ctor_get(v_val_1559_, 1);
lean_inc(v_snd_1561_);
lean_dec(v_val_1559_);
v___x_1562_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1560_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = 0;
v___x_1565_ = lean_box(0);
v___x_1566_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1567_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1567_, 0, v_a_1563_);
lean_ctor_set(v___x_1567_, 1, v___x_1565_);
lean_ctor_set(v___x_1567_, 2, v___x_1566_);
v___x_1568_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1564_, v_fst_1560_, v___x_1567_, v___y_1554_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v___x_1570_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1561_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1608_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1608_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1608_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
size_t v___x_1575_; size_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1575_ = lean_ptr_addr(v_k_1548_);
v___x_1576_ = lean_ptr_addr(v_a_1571_);
v___x_1577_ = lean_usize_dec_eq(v___x_1575_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1587_; 
v_isSharedCheck_1587_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; lean_object* v_unused_1589_; 
v_unused_1588_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1589_);
v___x_1579_ = v_code_1423_;
v_isShared_1580_ = v_isSharedCheck_1587_;
goto v_resetjp_1578_;
}
else
{
lean_dec(v_code_1423_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1587_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 1, v_a_1571_);
lean_ctor_set(v___x_1579_, 0, v_a_1569_);
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1569_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_a_1571_);
v___x_1582_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1584_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1582_);
v___x_1584_ = v___x_1573_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
else
{
size_t v___x_1590_; size_t v___x_1591_; uint8_t v___x_1592_; 
v___x_1590_ = lean_ptr_addr(v_decl_1547_);
v___x_1591_ = lean_ptr_addr(v_a_1569_);
v___x_1592_ = lean_usize_dec_eq(v___x_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1602_; 
v_isSharedCheck_1602_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; lean_object* v_unused_1604_; 
v_unused_1603_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1604_);
v___x_1594_ = v_code_1423_;
v_isShared_1595_ = v_isSharedCheck_1602_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v_code_1423_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1602_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 1, v_a_1571_);
lean_ctor_set(v___x_1594_, 0, v_a_1569_);
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1569_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_a_1571_);
v___x_1597_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1599_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1597_);
v___x_1599_ = v___x_1573_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
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
else
{
lean_object* v___x_1606_; 
lean_dec(v_a_1571_);
lean_dec(v_a_1569_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v_code_1423_);
v___x_1606_ = v___x_1573_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_code_1423_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
else
{
lean_dec(v_a_1569_);
lean_dec_ref_known(v_code_1423_, 2);
return v___x_1570_;
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v_snd_1561_);
lean_dec_ref_known(v_code_1423_, 2);
v_a_1609_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1568_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1568_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v_snd_1561_);
lean_dec(v_fst_1560_);
lean_dec_ref_known(v_code_1423_, 2);
v_a_1617_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1562_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1562_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
uint8_t v___x_1625_; lean_object* v___x_1626_; 
lean_dec(v_a_1558_);
v___x_1625_ = 1;
v___x_1626_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1625_, v_value_1549_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; uint8_t v___x_1628_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = lean_unbox(v_a_1627_);
lean_dec(v_a_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
lean_inc_ref(v_k_1548_);
v___x_1629_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1548_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1666_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1666_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1666_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
size_t v___x_1634_; size_t v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = lean_ptr_addr(v_k_1548_);
v___x_1635_ = lean_ptr_addr(v_a_1630_);
v___x_1636_ = lean_usize_dec_eq(v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1646_; 
lean_inc_ref(v_decl_1547_);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; lean_object* v_unused_1648_; 
v_unused_1647_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1648_);
v___x_1638_ = v_code_1423_;
v_isShared_1639_ = v_isSharedCheck_1646_;
goto v_resetjp_1637_;
}
else
{
lean_dec(v_code_1423_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1646_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 1, v_a_1630_);
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_decl_1547_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_a_1630_);
v___x_1641_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1641_);
v___x_1643_ = v___x_1632_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
size_t v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = lean_ptr_addr(v_decl_1547_);
v___x_1650_ = lean_usize_dec_eq(v___x_1649_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1660_; 
lean_inc_ref(v_decl_1547_);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; lean_object* v_unused_1662_; 
v_unused_1661_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1662_);
v___x_1652_ = v_code_1423_;
v_isShared_1653_ = v_isSharedCheck_1660_;
goto v_resetjp_1651_;
}
else
{
lean_dec(v_code_1423_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1660_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v_a_1630_);
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_decl_1547_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_a_1630_);
v___x_1655_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1657_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1655_);
v___x_1657_ = v___x_1632_;
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
lean_object* v___x_1664_; 
lean_dec(v_a_1630_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v_code_1423_);
v___x_1664_ = v___x_1632_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_code_1423_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1423_, 2);
return v___x_1629_;
}
}
else
{
lean_object* v___x_1667_; 
lean_inc_ref(v_decl_1547_);
v___x_1667_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1547_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v___x_1669_ = 0;
v___x_1670_ = lean_box(0);
v___x_1671_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1672_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1672_, 0, v_a_1668_);
lean_ctor_set(v___x_1672_, 1, v___x_1670_);
lean_ctor_set(v___x_1672_, 2, v___x_1671_);
lean_inc_ref(v_decl_1547_);
v___x_1673_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1669_, v_decl_1547_, v___x_1672_, v___y_1554_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
lean_inc_ref(v_k_1548_);
v___x_1675_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1548_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1713_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1713_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1713_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
size_t v___x_1680_; size_t v___x_1681_; uint8_t v___x_1682_; 
v___x_1680_ = lean_ptr_addr(v_k_1548_);
v___x_1681_ = lean_ptr_addr(v_a_1676_);
v___x_1682_ = lean_usize_dec_eq(v___x_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1692_; 
v_isSharedCheck_1692_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; lean_object* v_unused_1694_; 
v_unused_1693_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1694_);
v___x_1684_ = v_code_1423_;
v_isShared_1685_ = v_isSharedCheck_1692_;
goto v_resetjp_1683_;
}
else
{
lean_dec(v_code_1423_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1692_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v_a_1676_);
lean_ctor_set(v___x_1684_, 0, v_a_1674_);
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1674_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_a_1676_);
v___x_1687_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1687_);
v___x_1689_ = v___x_1678_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
else
{
size_t v___x_1695_; size_t v___x_1696_; uint8_t v___x_1697_; 
v___x_1695_ = lean_ptr_addr(v_decl_1547_);
v___x_1696_ = lean_ptr_addr(v_a_1674_);
v___x_1697_ = lean_usize_dec_eq(v___x_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1707_; 
v_isSharedCheck_1707_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; lean_object* v_unused_1709_; 
v_unused_1708_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1709_);
v___x_1699_ = v_code_1423_;
v_isShared_1700_ = v_isSharedCheck_1707_;
goto v_resetjp_1698_;
}
else
{
lean_dec(v_code_1423_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1707_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v_a_1676_);
lean_ctor_set(v___x_1699_, 0, v_a_1674_);
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1674_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_a_1676_);
v___x_1702_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1704_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1702_);
v___x_1704_ = v___x_1678_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v___x_1711_; 
lean_dec(v_a_1676_);
lean_dec(v_a_1674_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v_code_1423_);
v___x_1711_ = v___x_1678_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_code_1423_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
else
{
lean_dec(v_a_1674_);
lean_dec_ref_known(v_code_1423_, 2);
return v___x_1675_;
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref_known(v_code_1423_, 2);
v_a_1714_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1673_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1673_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec_ref_known(v_code_1423_, 2);
v_a_1722_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1667_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1667_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec_ref_known(v_code_1423_, 2);
v_a_1730_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1626_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1626_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec(v_value_1549_);
lean_dec_ref_known(v_code_1423_, 2);
v_a_1738_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1557_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1557_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2107_; lean_object* v_k_2108_; 
v_decl_2107_ = lean_ctor_get(v_code_1423_, 0);
v_k_2108_ = lean_ctor_get(v_code_1423_, 1);
lean_inc_ref(v_k_2108_);
lean_inc_ref(v_decl_2107_);
v_decl_1432_ = v_decl_2107_;
v_k_1433_ = v_k_2108_;
v___y_1434_ = v_a_1424_;
v___y_1435_ = v_a_1425_;
v___y_1436_ = v_a_1426_;
v___y_1437_ = v_a_1427_;
v___y_1438_ = v_a_1428_;
v___y_1439_ = v_a_1429_;
goto v___jp_1431_;
}
case 2:
{
lean_object* v_decl_2109_; lean_object* v_k_2110_; 
v_decl_2109_ = lean_ctor_get(v_code_1423_, 0);
v_k_2110_ = lean_ctor_get(v_code_1423_, 1);
lean_inc_ref(v_k_2110_);
lean_inc_ref(v_decl_2109_);
v_decl_1432_ = v_decl_2109_;
v_k_1433_ = v_k_2110_;
v___y_1434_ = v_a_1424_;
v___y_1435_ = v_a_1425_;
v___y_1436_ = v_a_1426_;
v___y_1437_ = v_a_1427_;
v___y_1438_ = v_a_1428_;
v___y_1439_ = v_a_1429_;
goto v___jp_1431_;
}
case 4:
{
lean_object* v_cases_2111_; lean_object* v_typeName_2112_; lean_object* v_resultType_2113_; lean_object* v_discr_2114_; lean_object* v_alts_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2154_; 
v_cases_2111_ = lean_ctor_get(v_code_1423_, 0);
lean_inc_ref(v_cases_2111_);
v_typeName_2112_ = lean_ctor_get(v_cases_2111_, 0);
v_resultType_2113_ = lean_ctor_get(v_cases_2111_, 1);
v_discr_2114_ = lean_ctor_get(v_cases_2111_, 2);
v_alts_2115_ = lean_ctor_get(v_cases_2111_, 3);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_cases_2111_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2117_ = v_cases_2111_;
v_isShared_2118_ = v_isSharedCheck_2154_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_alts_2115_);
lean_inc(v_discr_2114_);
lean_inc(v_resultType_2113_);
lean_inc(v_typeName_2112_);
lean_dec(v_cases_2111_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2154_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2115_);
v___x_2120_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v___x_2119_, v_alts_2115_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2145_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2145_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2145_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
size_t v___x_2125_; size_t v___x_2126_; uint8_t v___x_2127_; 
v___x_2125_ = lean_ptr_addr(v_alts_2115_);
lean_dec_ref(v_alts_2115_);
v___x_2126_ = lean_ptr_addr(v_a_2121_);
v___x_2127_ = lean_usize_dec_eq(v___x_2125_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2140_; 
v_isSharedCheck_2140_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_2140_ == 0)
{
lean_object* v_unused_2141_; 
v_unused_2141_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_2141_);
v___x_2129_ = v_code_1423_;
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
else
{
lean_dec(v_code_1423_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2140_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 3, v_a_2121_);
v___x_2132_ = v___x_2117_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_typeName_2112_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_resultType_2113_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_discr_2114_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_a_2121_);
v___x_2132_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2134_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2132_);
v___x_2134_ = v___x_2129_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2134_);
v___x_2136_ = v___x_2123_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
else
{
lean_object* v___x_2143_; 
lean_dec(v_a_2121_);
lean_del_object(v___x_2117_);
lean_dec(v_discr_2114_);
lean_dec_ref(v_resultType_2113_);
lean_dec(v_typeName_2112_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v_code_1423_);
v___x_2143_ = v___x_2123_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_code_1423_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_del_object(v___x_2117_);
lean_dec_ref(v_alts_2115_);
lean_dec(v_discr_2114_);
lean_dec_ref(v_resultType_2113_);
lean_dec(v_typeName_2112_);
lean_dec_ref_known(v_code_1423_, 1);
v_a_2146_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2120_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2120_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
default: 
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_code_1423_);
return v___x_2155_;
}
}
v___jp_1431_:
{
lean_object* v_params_1440_; lean_object* v_type_1441_; lean_object* v_value_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; 
v_params_1440_ = lean_ctor_get(v_decl_1432_, 2);
lean_inc_ref(v_params_1440_);
v_type_1441_ = lean_ctor_get(v_decl_1432_, 3);
lean_inc_ref(v_type_1441_);
v_value_1442_ = lean_ctor_get(v_decl_1432_, 4);
v___x_1443_ = 0;
lean_inc_ref(v_value_1442_);
v___x_1444_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_value_1442_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1443_, v_decl_1432_, v_type_1441_, v_params_1440_, v_a_1445_, v___y_1437_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___x_1446_, 1);
v___x_1448_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1448_) == 0)
{
switch(lean_obj_tag(v_code_1423_))
{
case 1:
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1488_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1488_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1488_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_decl_1453_; lean_object* v_k_1454_; size_t v___x_1455_; size_t v___x_1456_; uint8_t v___x_1457_; 
v_decl_1453_ = lean_ctor_get(v_code_1423_, 0);
v_k_1454_ = lean_ctor_get(v_code_1423_, 1);
v___x_1455_ = lean_ptr_addr(v_k_1454_);
v___x_1456_ = lean_ptr_addr(v_a_1449_);
v___x_1457_ = lean_usize_dec_eq(v___x_1455_, v___x_1456_);
if (v___x_1457_ == 0)
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1467_; 
v_isSharedCheck_1467_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; lean_object* v_unused_1469_; 
v_unused_1468_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1468_);
v_unused_1469_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1469_);
v___x_1459_ = v_code_1423_;
v_isShared_1460_ = v_isSharedCheck_1467_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v_code_1423_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1467_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 1, v_a_1449_);
lean_ctor_set(v___x_1459_, 0, v_a_1447_);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1447_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_a_1449_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1462_);
v___x_1464_ = v___x_1451_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
else
{
size_t v___x_1470_; size_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1470_ = lean_ptr_addr(v_decl_1453_);
v___x_1471_ = lean_ptr_addr(v_a_1447_);
v___x_1472_ = lean_usize_dec_eq(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1482_; 
v_isSharedCheck_1482_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; lean_object* v_unused_1484_; 
v_unused_1483_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1484_);
v___x_1474_ = v_code_1423_;
v_isShared_1475_ = v_isSharedCheck_1482_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v_code_1423_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1482_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v_a_1449_);
lean_ctor_set(v___x_1474_, 0, v_a_1447_);
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1447_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_a_1449_);
v___x_1477_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1477_);
v___x_1479_ = v___x_1451_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v___x_1486_; 
lean_dec(v_a_1449_);
lean_dec(v_a_1447_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v_code_1423_);
v___x_1486_ = v___x_1451_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_code_1423_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
case 2:
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1528_; 
v_a_1489_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1491_ = v___x_1448_;
v_isShared_1492_ = v_isSharedCheck_1528_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1448_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1528_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_decl_1493_; lean_object* v_k_1494_; size_t v___x_1495_; size_t v___x_1496_; uint8_t v___x_1497_; 
v_decl_1493_ = lean_ctor_get(v_code_1423_, 0);
v_k_1494_ = lean_ctor_get(v_code_1423_, 1);
v___x_1495_ = lean_ptr_addr(v_k_1494_);
v___x_1496_ = lean_ptr_addr(v_a_1489_);
v___x_1497_ = lean_usize_dec_eq(v___x_1495_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1507_; 
v_isSharedCheck_1507_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; lean_object* v_unused_1509_; 
v_unused_1508_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1509_);
v___x_1499_ = v_code_1423_;
v_isShared_1500_ = v_isSharedCheck_1507_;
goto v_resetjp_1498_;
}
else
{
lean_dec(v_code_1423_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1507_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 1, v_a_1489_);
lean_ctor_set(v___x_1499_, 0, v_a_1447_);
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1447_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_a_1489_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1502_);
v___x_1504_ = v___x_1491_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
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
size_t v___x_1510_; size_t v___x_1511_; uint8_t v___x_1512_; 
v___x_1510_ = lean_ptr_addr(v_decl_1493_);
v___x_1511_ = lean_ptr_addr(v_a_1447_);
v___x_1512_ = lean_usize_dec_eq(v___x_1510_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1522_; 
v_isSharedCheck_1522_ = !lean_is_exclusive(v_code_1423_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; lean_object* v_unused_1524_; 
v_unused_1523_ = lean_ctor_get(v_code_1423_, 1);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_code_1423_, 0);
lean_dec(v_unused_1524_);
v___x_1514_ = v_code_1423_;
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
else
{
lean_dec(v_code_1423_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v_a_1489_);
lean_ctor_set(v___x_1514_, 0, v_a_1447_);
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1447_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_a_1489_);
v___x_1517_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1517_);
v___x_1519_ = v___x_1491_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
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
else
{
lean_object* v___x_1526_; 
lean_dec(v_a_1489_);
lean_dec(v_a_1447_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v_code_1423_);
v___x_1526_ = v___x_1491_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_code_1423_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
default: 
{
lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1537_; 
lean_dec(v_a_1447_);
lean_dec_ref(v_code_1423_);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v___x_1448_, 0);
lean_dec(v_unused_1538_);
v___x_1530_ = v___x_1448_;
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
else
{
lean_dec(v___x_1448_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1532_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3, &l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3);
v___x_1533_ = l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(v___x_1532_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1533_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
else
{
lean_dec(v_a_1447_);
lean_dec_ref(v_code_1423_);
return v___x_1448_;
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v_k_1433_);
lean_dec_ref(v_code_1423_);
v_a_1539_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1446_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1446_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_dec_ref(v_type_1441_);
lean_dec_ref(v_params_1440_);
lean_dec_ref(v_k_1433_);
lean_dec_ref(v_decl_1432_);
lean_dec_ref(v_code_1423_);
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object* v_i_2156_, lean_object* v_as_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2165_ = lean_array_get_size(v_as_2157_);
v___x_2166_ = lean_nat_dec_lt(v_i_2156_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; 
lean_dec(v_i_2156_);
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_as_2157_);
return v___x_2167_;
}
else
{
lean_object* v_a_2168_; lean_object* v___y_2170_; 
v_a_2168_ = lean_array_fget_borrowed(v_as_2157_, v_i_2156_);
switch(lean_obj_tag(v_a_2168_))
{
case 0:
{
lean_object* v_code_2192_; 
v_code_2192_ = lean_ctor_get(v_a_2168_, 2);
lean_inc_ref(v_code_2192_);
v___y_2170_ = v_code_2192_;
goto v___jp_2169_;
}
case 1:
{
lean_object* v_code_2193_; 
v_code_2193_ = lean_ctor_get(v_a_2168_, 1);
lean_inc_ref(v_code_2193_);
v___y_2170_ = v_code_2193_;
goto v___jp_2169_;
}
default: 
{
lean_object* v_code_2194_; 
v_code_2194_ = lean_ctor_get(v_a_2168_, 0);
lean_inc_ref(v_code_2194_);
v___y_2170_ = v_code_2194_;
goto v___jp_2169_;
}
}
v___jp_2169_:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v___y_2170_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; size_t v___x_2174_; size_t v___x_2175_; uint8_t v___x_2176_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
lean_inc(v_a_2168_);
v___x_2173_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2168_, v_a_2172_);
v___x_2174_ = lean_ptr_addr(v_a_2168_);
v___x_2175_ = lean_ptr_addr(v___x_2173_);
v___x_2176_ = lean_usize_dec_eq(v___x_2174_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_unsigned_to_nat(1u);
v___x_2178_ = lean_nat_add(v_i_2156_, v___x_2177_);
v___x_2179_ = lean_array_fset(v_as_2157_, v_i_2156_, v___x_2173_);
lean_dec(v_i_2156_);
v_i_2156_ = v___x_2178_;
v_as_2157_ = v___x_2179_;
goto _start;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec_ref(v___x_2173_);
v___x_2181_ = lean_unsigned_to_nat(1u);
v___x_2182_ = lean_nat_add(v_i_2156_, v___x_2181_);
lean_dec(v_i_2156_);
v_i_2156_ = v___x_2182_;
goto _start;
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v_as_2157_);
lean_dec(v_i_2156_);
v_a_2184_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2171_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2171_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object* v_i_2195_, lean_object* v_as_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_2195_, v_as_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object* v_code_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_code_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(lean_object* v_f_2214_, lean_object* v_v_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
if (lean_obj_tag(v_v_2215_) == 0)
{
lean_object* v_code_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2247_; 
v_code_2223_ = lean_ctor_get(v_v_2215_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_v_2215_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2225_ = v_v_2215_;
v_isShared_2226_ = v_isSharedCheck_2247_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_code_2223_);
lean_dec(v_v_2215_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2247_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; 
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
lean_inc(v___y_2217_);
lean_inc_ref(v___y_2216_);
v___x_2227_ = lean_apply_8(v_f_2214_, v_code_2223_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, lean_box(0));
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2238_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2238_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2238_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v_a_2228_);
v___x_2233_ = v___x_2225_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2235_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2233_);
v___x_2235_ = v___x_2230_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_del_object(v___x_2225_);
v_a_2239_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2227_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2227_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
else
{
lean_object* v___x_2248_; 
lean_dec_ref(v_f_2214_);
v___x_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2248_, 0, v_v_2215_);
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(lean_object* v_f_2249_, lean_object* v_v_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2249_, v_v_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(uint8_t v_pu_2259_, lean_object* v_f_2260_, lean_object* v_v_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2260_, v_v_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(lean_object* v_pu_2270_, lean_object* v_f_2271_, lean_object* v_v_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
uint8_t v_pu_boxed_2280_; lean_object* v_res_2281_; 
v_pu_boxed_2280_ = lean_unbox(v_pu_2270_);
v_res_2281_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_boxed_2280_, v_f_2271_, v_v_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object* v_decl_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_toSignature_2291_; lean_object* v_value_2292_; uint8_t v_recursive_2293_; lean_object* v_inlineAttr_x3f_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2319_; 
v_toSignature_2291_ = lean_ctor_get(v_decl_2283_, 0);
v_value_2292_ = lean_ctor_get(v_decl_2283_, 1);
v_recursive_2293_ = lean_ctor_get_uint8(v_decl_2283_, sizeof(void*)*3);
v_inlineAttr_x3f_2294_ = lean_ctor_get(v_decl_2283_, 2);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_decl_2283_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2296_ = v_decl_2283_;
v_isShared_2297_ = v_isSharedCheck_2319_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_inlineAttr_x3f_2294_);
lean_inc(v_value_2292_);
lean_inc(v_toSignature_2291_);
lean_dec(v_decl_2283_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2319_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0));
v___x_2299_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v___x_2298_, v_value_2292_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2310_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2310_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2310_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v_a_2300_);
v___x_2305_ = v___x_2296_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_toSignature_2291_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_a_2300_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_inlineAttr_x3f_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*3, v_recursive_2293_);
v___x_2305_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2307_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2305_);
v___x_2307_ = v___x_2302_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_del_object(v___x_2296_);
lean_dec(v_inlineAttr_x3f_2294_);
lean_dec_ref(v_toSignature_2291_);
v_a_2311_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2299_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2299_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(lean_object* v_decl_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
return v_res_2328_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_2332_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0));
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v___x_2331_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* v_decl_2334_, lean_object* v_sccDecls_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_toSignature_2341_; lean_object* v_name_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_toSignature_2341_ = lean_ctor_get(v_decl_2334_, 0);
v_name_2342_ = lean_ctor_get(v_toSignature_2341_, 0);
lean_inc(v_name_2342_);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v_name_2342_);
lean_ctor_set(v___x_2343_, 1, v_sccDecls_2335_);
v___x_2344_ = lean_unsigned_to_nat(0u);
v___x_2345_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1);
v___x_2346_ = lean_st_mk_ref(v___x_2345_);
v___x_2347_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2334_, v___x_2343_, v___x_2346_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
lean_dec_ref_known(v___x_2343_, 2);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2373_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2373_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2373_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v_decls_2353_; lean_object* v_decl_2355_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2352_ = lean_st_ref_get(v___x_2346_);
lean_dec(v___x_2346_);
v_decls_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc_ref(v_decls_2353_);
lean_dec(v___x_2352_);
v___x_2360_ = lean_array_get_size(v_decls_2353_);
v___x_2361_ = lean_nat_dec_eq(v___x_2360_, v___x_2344_);
if (v___x_2361_ == 0)
{
uint8_t v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = 0;
v___x_2363_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2362_, v_a_2348_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v_decl_2355_ = v_a_2364_;
goto v___jp_2354_;
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref(v_decls_2353_);
lean_del_object(v___x_2350_);
v_a_2365_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2363_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2363_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
v_decl_2355_ = v_a_2348_;
goto v___jp_2354_;
}
v___jp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_array_push(v_decls_2353_, v_decl_2355_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2356_);
v___x_2358_ = v___x_2350_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v___x_2346_);
v_a_2374_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2347_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2347_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(lean_object* v_decl_2382_, lean_object* v_sccDecls_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v_decl_2382_, v_sccDecls_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(lean_object* v_decls_2390_, lean_object* v_as_2391_, size_t v_i_2392_, size_t v_stop_2393_, lean_object* v_b_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_a_2401_; uint8_t v___x_2405_; 
v___x_2405_ = lean_usize_dec_eq(v_i_2392_, v_stop_2393_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = lean_array_uget_borrowed(v_as_2391_, v_i_2392_);
lean_inc_ref(v_decls_2390_);
lean_inc(v___x_2406_);
v___x_2407_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v___x_2406_, v_decls_2390_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = l_Array_append___redArg(v_b_2394_, v_a_2408_);
lean_dec(v_a_2408_);
v_a_2401_ = v___x_2409_;
goto v___jp_2400_;
}
else
{
lean_dec_ref(v_b_2394_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2410_; 
v_a_2410_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2407_, 1);
v_a_2401_ = v_a_2410_;
goto v___jp_2400_;
}
else
{
lean_dec_ref(v_decls_2390_);
return v___x_2407_;
}
}
}
else
{
lean_object* v___x_2411_; 
lean_dec_ref(v_decls_2390_);
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v_b_2394_);
return v___x_2411_;
}
v___jp_2400_:
{
size_t v___x_2402_; size_t v___x_2403_; 
v___x_2402_ = ((size_t)1ULL);
v___x_2403_ = lean_usize_add(v_i_2392_, v___x_2402_);
v_i_2392_ = v___x_2403_;
v_b_2394_ = v_a_2401_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object* v_decls_2412_, lean_object* v_as_2413_, lean_object* v_i_2414_, lean_object* v_stop_2415_, lean_object* v_b_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
size_t v_i_boxed_2422_; size_t v_stop_boxed_2423_; lean_object* v_res_2424_; 
v_i_boxed_2422_ = lean_unbox_usize(v_i_2414_);
lean_dec(v_i_2414_);
v_stop_boxed_2423_ = lean_unbox_usize(v_stop_2415_);
lean_dec(v_stop_2415_);
v_res_2424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2412_, v_as_2413_, v_i_boxed_2422_, v_stop_boxed_2423_, v_b_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec_ref(v_as_2413_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* v___x_2425_, lean_object* v_decls_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_2427_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2457_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2457_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2457_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
uint8_t v_extractClosed_2437_; 
v_extractClosed_2437_ = lean_ctor_get_uint8(v_a_2433_, sizeof(void*)*4 + 1);
lean_dec(v_a_2433_);
if (v_extractClosed_2437_ == 0)
{
lean_object* v___x_2439_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v_decls_2426_);
v___x_2439_ = v___x_2435_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_decls_2426_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v___x_2441_ = lean_mk_empty_array_with_capacity(v___x_2425_);
v___x_2442_ = lean_array_get_size(v_decls_2426_);
v___x_2443_ = lean_nat_dec_lt(v___x_2425_, v___x_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2445_; 
lean_dec_ref(v_decls_2426_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2441_);
v___x_2445_ = v___x_2435_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2441_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
else
{
uint8_t v___x_2447_; 
v___x_2447_ = lean_nat_dec_le(v___x_2442_, v___x_2442_);
if (v___x_2447_ == 0)
{
if (v___x_2443_ == 0)
{
lean_object* v___x_2449_; 
lean_dec_ref(v_decls_2426_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2441_);
v___x_2449_ = v___x_2435_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2441_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
else
{
size_t v___x_2451_; size_t v___x_2452_; lean_object* v___x_2453_; 
lean_del_object(v___x_2435_);
v___x_2451_ = ((size_t)0ULL);
v___x_2452_ = lean_usize_of_nat(v___x_2442_);
lean_inc_ref(v_decls_2426_);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2426_, v_decls_2426_, v___x_2451_, v___x_2452_, v___x_2441_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec_ref(v_decls_2426_);
return v___x_2453_;
}
}
else
{
size_t v___x_2454_; size_t v___x_2455_; lean_object* v___x_2456_; 
lean_del_object(v___x_2435_);
v___x_2454_ = ((size_t)0ULL);
v___x_2455_ = lean_usize_of_nat(v___x_2442_);
lean_inc_ref(v_decls_2426_);
v___x_2456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2426_, v_decls_2426_, v___x_2454_, v___x_2455_, v___x_2441_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec_ref(v_decls_2426_);
return v___x_2456_;
}
}
}
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec_ref(v_decls_2426_);
v_a_2458_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2432_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2432_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object* v___x_2466_, lean_object* v_decls_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(v___x_2466_, v_decls_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___x_2466_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2556_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2557_ = 1;
v___x_2558_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2559_ = l_Lean_registerTraceClass(v___x_2556_, v___x_2557_, v___x_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
return v_res_2561_;
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
