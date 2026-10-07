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
uint8_t v___x_34_; 
v___x_34_ = lean_nat_dec_le(v___x_30_, v___x_30_);
if (v___x_34_ == 0)
{
if (v___x_32_ == 0)
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_31_);
return v___x_35_;
}
else
{
size_t v___x_36_; size_t v___x_37_; lean_object* v___x_38_; 
v___x_36_ = ((size_t)0ULL);
v___x_37_ = lean_usize_of_nat(v___x_30_);
v___x_38_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_28_, v___x_36_, v___x_37_, v___x_31_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_38_;
}
}
else
{
size_t v___x_39_; size_t v___x_40_; lean_object* v___x_41_; 
v___x_39_ = ((size_t)0ULL);
v___x_40_ = lean_usize_of_nat(v___x_30_);
v___x_41_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_28_, v___x_39_, v___x_40_, v___x_31_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_41_;
}
}
}
case 4:
{
lean_object* v_fvarId_42_; lean_object* v_args_43_; lean_object* v___x_44_; 
v_fvarId_42_ = lean_ctor_get(v_v_19_, 0);
v_args_43_ = lean_ctor_get(v_v_19_, 1);
v___x_44_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_42_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_65_; 
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v___x_44_, 0);
lean_dec(v_unused_66_);
v___x_46_ = v___x_44_;
v_isShared_47_ = v_isSharedCheck_65_;
goto v_resetjp_45_;
}
else
{
lean_dec(v___x_44_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_65_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_array_get_size(v_args_43_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_nat_dec_lt(v___x_48_, v___x_49_);
if (v___x_51_ == 0)
{
lean_object* v___x_53_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_50_);
v___x_53_ = v___x_46_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_50_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
else
{
uint8_t v___x_55_; 
v___x_55_ = lean_nat_dec_le(v___x_49_, v___x_49_);
if (v___x_55_ == 0)
{
if (v___x_51_ == 0)
{
lean_object* v___x_57_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_50_);
v___x_57_ = v___x_46_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_50_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
else
{
size_t v___x_59_; size_t v___x_60_; lean_object* v___x_61_; 
lean_del_object(v___x_46_);
v___x_59_ = ((size_t)0ULL);
v___x_60_ = lean_usize_of_nat(v___x_49_);
v___x_61_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_43_, v___x_59_, v___x_60_, v___x_50_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_61_;
}
}
else
{
size_t v___x_62_; size_t v___x_63_; lean_object* v___x_64_; 
lean_del_object(v___x_46_);
v___x_62_ = ((size_t)0ULL);
v___x_63_ = lean_usize_of_nat(v___x_49_);
v___x_64_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_43_, v___x_62_, v___x_63_, v___x_50_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_64_;
}
}
}
}
else
{
return v___x_44_;
}
}
default: 
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_box(0);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(lean_object* v_fvarId_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
uint8_t v___x_76_; lean_object* v___x_77_; 
v___x_76_ = 0;
v___x_77_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_76_, v_fvarId_69_, v_a_72_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_99_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_99_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_99_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_99_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
if (lean_obj_tag(v_a_78_) == 1)
{
lean_object* v_val_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_94_; 
lean_del_object(v___x_80_);
v_val_82_ = lean_ctor_get(v_a_78_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v_a_78_);
if (v_isSharedCheck_94_ == 0)
{
v___x_84_ = v_a_78_;
v_isShared_85_ = v_isSharedCheck_94_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_val_82_);
lean_dec(v_a_78_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_94_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = lean_st_ref_take(v_a_70_);
lean_inc(v_val_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set_tag(v___x_84_, 0);
v___x_88_ = v___x_84_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_val_82_);
v___x_88_ = v_reuseFailAlloc_93_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_value_91_; lean_object* v___x_92_; 
v___x_89_ = lean_array_push(v___x_86_, v___x_88_);
v___x_90_ = lean_st_ref_put(v_a_70_, v___x_89_);
v_value_91_ = lean_ctor_get(v_val_82_, 3);
lean_inc(v_value_91_);
lean_dec(v_val_82_);
v___x_92_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_91_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
lean_dec(v_value_91_);
return v___x_92_;
}
}
}
else
{
lean_object* v___x_95_; lean_object* v___x_97_; 
lean_dec(v_a_78_);
v___x_95_ = lean_box(0);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_95_);
v___x_97_ = v___x_80_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
v_a_100_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_77_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_77_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg(lean_object* v_arg_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
if (lean_obj_tag(v_arg_108_) == 1)
{
lean_object* v_fvarId_115_; lean_object* v___x_116_; 
v_fvarId_115_ = lean_ctor_get(v_arg_108_, 0);
v___x_116_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_115_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
return v___x_116_;
}
else
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_box(0);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg___boxed(lean_object* v_arg_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(v_arg_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec(v_arg_119_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0___boxed(lean_object* v_as_127_, lean_object* v_i_128_, lean_object* v_stop_129_, lean_object* v_b_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
size_t v_i_boxed_137_; size_t v_stop_boxed_138_; lean_object* v_res_139_; 
v_i_boxed_137_ = lean_unbox_usize(v_i_128_);
lean_dec(v_i_128_);
v_stop_boxed_138_ = lean_unbox_usize(v_stop_129_);
lean_dec(v_stop_129_);
v_res_139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_as_127_, v_i_boxed_137_, v_stop_boxed_138_, v_b_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v_as_127_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar___boxed(lean_object* v_fvarId_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_fvarId_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec(v_fvarId_140_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___boxed(lean_object* v_v_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_v_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec(v_v_148_);
return v_res_155_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(lean_object* v_arg_156_){
_start:
{
if (lean_obj_tag(v_arg_156_) == 1)
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = 1;
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg___boxed(lean_object* v_arg_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v_arg_159_);
lean_dec(v_arg_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t v_____do__lift_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
if (v_____do__lift_162_ == 0)
{
uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = 1;
v___x_171_ = lean_box(v___x_170_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
else
{
uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = 0;
v___x_174_ = lean_box(v___x_173_);
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object* v_____do__lift_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
uint8_t v_____do__lift_14824__boxed_184_; lean_object* v_res_185_; 
v_____do__lift_14824__boxed_184_ = lean_unbox(v_____do__lift_176_);
v_res_185_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v_____do__lift_14824__boxed_184_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(lean_object* v_a_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_187_) == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
return v___x_188_;
}
else
{
lean_object* v_key_189_; lean_object* v_value_190_; lean_object* v_tail_191_; uint8_t v___x_192_; 
v_key_189_ = lean_ctor_get(v_x_187_, 0);
v_value_190_ = lean_ctor_get(v_x_187_, 1);
v_tail_191_ = lean_ctor_get(v_x_187_, 2);
v___x_192_ = l_Lean_instBEqFVarId_beq(v_key_189_, v_a_186_);
if (v___x_192_ == 0)
{
v_x_187_ = v_tail_191_;
goto _start;
}
else
{
lean_object* v___x_194_; 
lean_inc(v_value_190_);
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v_value_190_);
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg___boxed(lean_object* v_a_195_, lean_object* v_x_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_195_, v_x_196_);
lean_dec(v_x_196_);
lean_dec(v_a_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(lean_object* v_m_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_buckets_200_; lean_object* v___x_201_; uint64_t v___x_202_; uint64_t v___x_203_; uint64_t v___x_204_; uint64_t v_fold_205_; uint64_t v___x_206_; uint64_t v___x_207_; uint64_t v___x_208_; size_t v___x_209_; size_t v___x_210_; size_t v___x_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v_buckets_200_ = lean_ctor_get(v_m_198_, 1);
v___x_201_ = lean_array_get_size(v_buckets_200_);
v___x_202_ = l_Lean_instHashableFVarId_hash(v_a_199_);
v___x_203_ = 32ULL;
v___x_204_ = lean_uint64_shift_right(v___x_202_, v___x_203_);
v_fold_205_ = lean_uint64_xor(v___x_202_, v___x_204_);
v___x_206_ = 16ULL;
v___x_207_ = lean_uint64_shift_right(v_fold_205_, v___x_206_);
v___x_208_ = lean_uint64_xor(v_fold_205_, v___x_207_);
v___x_209_ = lean_uint64_to_usize(v___x_208_);
v___x_210_ = lean_usize_of_nat(v___x_201_);
v___x_211_ = ((size_t)1ULL);
v___x_212_ = lean_usize_sub(v___x_210_, v___x_211_);
v___x_213_ = lean_usize_land(v___x_209_, v___x_212_);
v___x_214_ = lean_array_uget_borrowed(v_buckets_200_, v___x_213_);
v___x_215_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_199_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg___boxed(lean_object* v_m_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_m_216_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
return v_x_219_;
}
else
{
lean_object* v_key_221_; lean_object* v_value_222_; lean_object* v_tail_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_246_; 
v_key_221_ = lean_ctor_get(v_x_220_, 0);
v_value_222_ = lean_ctor_get(v_x_220_, 1);
v_tail_223_ = lean_ctor_get(v_x_220_, 2);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_220_);
if (v_isSharedCheck_246_ == 0)
{
v___x_225_ = v_x_220_;
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_tail_223_);
lean_inc(v_value_222_);
lean_inc(v_key_221_);
lean_dec(v_x_220_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_246_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v___x_230_; uint64_t v_fold_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_227_ = lean_array_get_size(v_x_219_);
v___x_228_ = l_Lean_instHashableFVarId_hash(v_key_221_);
v___x_229_ = 32ULL;
v___x_230_ = lean_uint64_shift_right(v___x_228_, v___x_229_);
v_fold_231_ = lean_uint64_xor(v___x_228_, v___x_230_);
v___x_232_ = 16ULL;
v___x_233_ = lean_uint64_shift_right(v_fold_231_, v___x_232_);
v___x_234_ = lean_uint64_xor(v_fold_231_, v___x_233_);
v___x_235_ = lean_uint64_to_usize(v___x_234_);
v___x_236_ = lean_usize_of_nat(v___x_227_);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_sub(v___x_236_, v___x_237_);
v___x_239_ = lean_usize_land(v___x_235_, v___x_238_);
v___x_240_ = lean_array_uget_borrowed(v_x_219_, v___x_239_);
lean_inc(v___x_240_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 2, v___x_240_);
v___x_242_ = v___x_225_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_key_221_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_value_222_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v___x_240_);
v___x_242_ = v_reuseFailAlloc_245_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = lean_array_uset(v_x_219_, v___x_239_, v___x_242_);
v_x_219_ = v___x_243_;
v_x_220_ = v_tail_223_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(lean_object* v_i_247_, lean_object* v_source_248_, lean_object* v_target_249_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_array_get_size(v_source_248_);
v___x_251_ = lean_nat_dec_lt(v_i_247_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec_ref(v_source_248_);
lean_dec(v_i_247_);
return v_target_249_;
}
else
{
lean_object* v_es_252_; lean_object* v___x_253_; lean_object* v_source_254_; lean_object* v_target_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_es_252_ = lean_array_fget(v_source_248_, v_i_247_);
v___x_253_ = lean_box(0);
v_source_254_ = lean_array_fset(v_source_248_, v_i_247_, v___x_253_);
v_target_255_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_target_249_, v_es_252_);
v___x_256_ = lean_unsigned_to_nat(1u);
v___x_257_ = lean_nat_add(v_i_247_, v___x_256_);
lean_dec(v_i_247_);
v_i_247_ = v___x_257_;
v_source_248_ = v_source_254_;
v_target_249_ = v_target_255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(lean_object* v_data_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_nbuckets_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_260_ = lean_array_get_size(v_data_259_);
v___x_261_ = lean_unsigned_to_nat(2u);
v_nbuckets_262_ = lean_nat_mul(v___x_260_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_box(0);
v___x_265_ = lean_mk_array(v_nbuckets_262_, v___x_264_);
v___x_266_ = lean_array_propagate_mark(v_data_259_, v___x_265_);
v___x_267_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v___x_263_, v_data_259_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(lean_object* v_a_268_, lean_object* v_b_269_, lean_object* v_x_270_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
lean_dec(v_b_269_);
lean_dec(v_a_268_);
return v_x_270_;
}
else
{
lean_object* v_key_271_; lean_object* v_value_272_; lean_object* v_tail_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_285_; 
v_key_271_ = lean_ctor_get(v_x_270_, 0);
v_value_272_ = lean_ctor_get(v_x_270_, 1);
v_tail_273_ = lean_ctor_get(v_x_270_, 2);
v_isSharedCheck_285_ = !lean_is_exclusive(v_x_270_);
if (v_isSharedCheck_285_ == 0)
{
v___x_275_ = v_x_270_;
v_isShared_276_ = v_isSharedCheck_285_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_tail_273_);
lean_inc(v_value_272_);
lean_inc(v_key_271_);
lean_dec(v_x_270_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_285_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
uint8_t v___x_277_; 
v___x_277_ = l_Lean_instBEqFVarId_beq(v_key_271_, v_a_268_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_268_, v_b_269_, v_tail_273_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 2, v___x_278_);
v___x_280_ = v___x_275_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_key_271_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_value_272_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
else
{
lean_object* v___x_283_; 
lean_dec(v_value_272_);
lean_dec(v_key_271_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v_b_269_);
lean_ctor_set(v___x_275_, 0, v_a_268_);
v___x_283_ = v___x_275_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_268_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_b_269_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_tail_273_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(lean_object* v_a_286_, lean_object* v_x_287_){
_start:
{
if (lean_obj_tag(v_x_287_) == 0)
{
uint8_t v___x_288_; 
v___x_288_ = 0;
return v___x_288_;
}
else
{
lean_object* v_key_289_; lean_object* v_tail_290_; uint8_t v___x_291_; 
v_key_289_ = lean_ctor_get(v_x_287_, 0);
v_tail_290_ = lean_ctor_get(v_x_287_, 2);
v___x_291_ = l_Lean_instBEqFVarId_beq(v_key_289_, v_a_286_);
if (v___x_291_ == 0)
{
v_x_287_ = v_tail_290_;
goto _start;
}
else
{
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg___boxed(lean_object* v_a_293_, lean_object* v_x_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_293_, v_x_294_);
lean_dec(v_x_294_);
lean_dec(v_a_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(lean_object* v_m_297_, lean_object* v_a_298_, lean_object* v_b_299_){
_start:
{
lean_object* v_size_300_; lean_object* v_buckets_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_344_; 
v_size_300_ = lean_ctor_get(v_m_297_, 0);
v_buckets_301_ = lean_ctor_get(v_m_297_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_m_297_);
if (v_isSharedCheck_344_ == 0)
{
v___x_303_ = v_m_297_;
v_isShared_304_ = v_isSharedCheck_344_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_buckets_301_);
lean_inc(v_size_300_);
lean_dec(v_m_297_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_344_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; uint64_t v_fold_309_; uint64_t v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v_bkt_318_; uint8_t v___x_319_; 
v___x_305_ = lean_array_get_size(v_buckets_301_);
v___x_306_ = l_Lean_instHashableFVarId_hash(v_a_298_);
v___x_307_ = 32ULL;
v___x_308_ = lean_uint64_shift_right(v___x_306_, v___x_307_);
v_fold_309_ = lean_uint64_xor(v___x_306_, v___x_308_);
v___x_310_ = 16ULL;
v___x_311_ = lean_uint64_shift_right(v_fold_309_, v___x_310_);
v___x_312_ = lean_uint64_xor(v_fold_309_, v___x_311_);
v___x_313_ = lean_uint64_to_usize(v___x_312_);
v___x_314_ = lean_usize_of_nat(v___x_305_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_sub(v___x_314_, v___x_315_);
v___x_317_ = lean_usize_land(v___x_313_, v___x_316_);
v_bkt_318_ = lean_array_uget_borrowed(v_buckets_301_, v___x_317_);
v___x_319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_298_, v_bkt_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v_size_x27_321_; lean_object* v___x_322_; lean_object* v_buckets_x27_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_320_ = lean_unsigned_to_nat(1u);
v_size_x27_321_ = lean_nat_add(v_size_300_, v___x_320_);
lean_dec(v_size_300_);
lean_inc(v_bkt_318_);
v___x_322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_322_, 0, v_a_298_);
lean_ctor_set(v___x_322_, 1, v_b_299_);
lean_ctor_set(v___x_322_, 2, v_bkt_318_);
v_buckets_x27_323_ = lean_array_uset(v_buckets_301_, v___x_317_, v___x_322_);
v___x_324_ = lean_unsigned_to_nat(4u);
v___x_325_ = lean_nat_mul(v_size_x27_321_, v___x_324_);
v___x_326_ = lean_unsigned_to_nat(3u);
v___x_327_ = lean_nat_div(v___x_325_, v___x_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_array_get_size(v_buckets_x27_323_);
v___x_329_ = lean_nat_dec_le(v___x_327_, v___x_328_);
lean_dec(v___x_327_);
if (v___x_329_ == 0)
{
lean_object* v_val_330_; lean_object* v___x_332_; 
v_val_330_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_buckets_x27_323_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_val_330_);
lean_ctor_set(v___x_303_, 0, v_size_x27_321_);
v___x_332_ = v___x_303_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_size_x27_321_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_val_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
else
{
lean_object* v___x_335_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_buckets_x27_323_);
lean_ctor_set(v___x_303_, 0, v_size_x27_321_);
v___x_335_ = v___x_303_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_size_x27_321_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_buckets_x27_323_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
else
{
lean_object* v___x_337_; lean_object* v_buckets_x27_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
lean_inc(v_bkt_318_);
v___x_337_ = lean_box(0);
v_buckets_x27_338_ = lean_array_uset(v_buckets_301_, v___x_317_, v___x_337_);
v___x_339_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_298_, v_b_299_, v_bkt_318_);
v___x_340_ = lean_array_uset(v_buckets_x27_338_, v___x_317_, v___x_339_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_340_);
v___x_342_ = v___x_303_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_size_300_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(lean_object* v_declName_345_, lean_object* v_as_346_, size_t v_i_347_, size_t v_stop_348_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = lean_usize_dec_eq(v_i_347_, v_stop_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v_toSignature_351_; lean_object* v_name_352_; uint8_t v___x_353_; 
v___x_350_ = lean_array_uget_borrowed(v_as_346_, v_i_347_);
v_toSignature_351_ = lean_ctor_get(v___x_350_, 0);
v_name_352_ = lean_ctor_get(v_toSignature_351_, 0);
v___x_353_ = lean_name_eq(v_name_352_, v_declName_345_);
if (v___x_353_ == 0)
{
size_t v___x_354_; size_t v___x_355_; 
v___x_354_ = ((size_t)1ULL);
v___x_355_ = lean_usize_add(v_i_347_, v___x_354_);
v_i_347_ = v___x_355_;
goto _start;
}
else
{
return v___x_353_;
}
}
else
{
uint8_t v___x_357_; 
v___x_357_ = 0;
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3___boxed(lean_object* v_declName_358_, lean_object* v_as_359_, lean_object* v_i_360_, lean_object* v_stop_361_){
_start:
{
size_t v_i_boxed_362_; size_t v_stop_boxed_363_; uint8_t v_res_364_; lean_object* v_r_365_; 
v_i_boxed_362_ = lean_unbox_usize(v_i_360_);
lean_dec(v_i_360_);
v_stop_boxed_363_ = lean_unbox_usize(v_stop_361_);
lean_dec(v_stop_361_);
v_res_364_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_358_, v_as_359_, v_i_boxed_362_, v_stop_boxed_363_);
lean_dec_ref(v_as_359_);
lean_dec(v_declName_358_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(uint8_t v_isRoot_366_, uint8_t v___x_367_, lean_object* v_as_368_, size_t v_i_369_, size_t v_stop_370_){
_start:
{
uint8_t v___x_371_; 
v___x_371_ = lean_usize_dec_eq(v_i_369_, v_stop_370_);
if (v___x_371_ == 0)
{
uint8_t v___x_372_; uint8_t v___y_374_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_372_ = 1;
v___x_378_ = lean_array_uget_borrowed(v_as_368_, v_i_369_);
v___x_379_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v___x_378_);
if (v___x_379_ == 0)
{
v___y_374_ = v_isRoot_366_;
goto v___jp_373_;
}
else
{
v___y_374_ = v___x_367_;
goto v___jp_373_;
}
v___jp_373_:
{
if (v___y_374_ == 0)
{
size_t v___x_375_; size_t v___x_376_; 
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_add(v_i_369_, v___x_375_);
v_i_369_ = v___x_376_;
goto _start;
}
else
{
return v___x_372_;
}
}
}
else
{
uint8_t v___x_380_; 
v___x_380_ = 0;
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object* v_isRoot_381_, lean_object* v___x_382_, lean_object* v_as_383_, lean_object* v_i_384_, lean_object* v_stop_385_){
_start:
{
uint8_t v_isRoot_boxed_386_; uint8_t v___x_15131__boxed_387_; size_t v_i_boxed_388_; size_t v_stop_boxed_389_; uint8_t v_res_390_; lean_object* v_r_391_; 
v_isRoot_boxed_386_ = lean_unbox(v_isRoot_381_);
v___x_15131__boxed_387_ = lean_unbox(v___x_382_);
v_i_boxed_388_ = lean_unbox_usize(v_i_384_);
lean_dec(v_i_384_);
v_stop_boxed_389_ = lean_unbox_usize(v_stop_385_);
lean_dec(v_stop_385_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_boxed_386_, v___x_15131__boxed_387_, v_as_383_, v_i_boxed_388_, v_stop_boxed_389_);
lean_dec_ref(v_as_383_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_cstr_to_nat("9223372036854775808");
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(uint8_t v___x_393_, lean_object* v_as_394_, size_t v_i_395_, size_t v_stop_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = lean_usize_dec_eq(v_i_395_, v_stop_396_);
if (v___x_404_ == 0)
{
uint8_t v___x_405_; uint8_t v_a_407_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_405_ = 1;
v___x_413_ = lean_array_uget_borrowed(v_as_394_, v_i_395_);
lean_inc(v___x_413_);
v___x_414_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_413_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_424_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_424_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
uint8_t v___x_419_; 
v___x_419_ = lean_unbox(v_a_415_);
lean_dec(v_a_415_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = lean_box(v___x_405_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_420_);
v___x_422_ = v___x_417_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
else
{
lean_del_object(v___x_417_);
v_a_407_ = v___x_393_;
goto v___jp_406_;
}
}
}
else
{
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_425_; uint8_t v___x_426_; 
v_a_425_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_414_, 1);
v___x_426_ = lean_unbox(v_a_425_);
lean_dec(v_a_425_);
v_a_407_ = v___x_426_;
goto v___jp_406_;
}
else
{
return v___x_414_;
}
}
v___jp_406_:
{
if (v_a_407_ == 0)
{
size_t v___x_408_; size_t v___x_409_; 
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_add(v_i_395_, v___x_408_);
v_i_395_ = v___x_409_;
goto _start;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_box(v___x_405_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
}
else
{
uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = 0;
v___x_428_ = lean_box(v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(lean_object* v_as_430_, size_t v_i_431_, size_t v_stop_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_eq(v_i_431_, v_stop_432_);
if (v___x_444_ == 0)
{
uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = 1;
v___x_446_ = lean_array_uget_borrowed(v_as_430_, v_i_431_);
lean_inc(v___x_446_);
v___x_447_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_446_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_457_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_457_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
uint8_t v___x_452_; 
v___x_452_ = lean_unbox(v_a_448_);
lean_dec(v_a_448_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = lean_box(v___x_445_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_453_);
v___x_455_ = v___x_450_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_del_object(v___x_450_);
goto v___jp_440_;
}
}
}
else
{
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_467_; 
v_a_458_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_467_ == 0)
{
v___x_460_ = v___x_447_;
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_447_);
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
lean_del_object(v___x_460_);
goto v___jp_440_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_box(v___x_445_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 0);
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
}
}
else
{
return v___x_447_;
}
}
}
else
{
uint8_t v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = 0;
v___x_469_ = lean_box(v___x_468_);
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
v___jp_440_:
{
size_t v___x_441_; size_t v___x_442_; 
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_i_431_, v___x_441_);
v_i_431_ = v___x_442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t v_isRoot_471_, lean_object* v_v_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
switch(lean_obj_tag(v_v_472_))
{
case 0:
{
lean_object* v_value_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_529_; 
v_value_484_ = lean_ctor_get(v_v_472_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_v_472_);
if (v_isSharedCheck_529_ == 0)
{
v___x_486_ = v_v_472_;
v_isShared_487_ = v_isSharedCheck_529_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_value_484_);
lean_dec(v_v_472_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_529_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
switch(lean_obj_tag(v_value_484_))
{
case 1:
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_496_; 
lean_del_object(v___x_486_);
v_isSharedCheck_496_ = !lean_is_exclusive(v_value_484_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v_value_484_, 0);
lean_dec(v_unused_497_);
v___x_489_ = v_value_484_;
v_isShared_490_ = v_isSharedCheck_496_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_value_484_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_496_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_491_ = 1;
v___x_492_ = lean_box(v___x_491_);
if (v_isShared_490_ == 0)
{
lean_ctor_set_tag(v___x_489_, 0);
lean_ctor_set(v___x_489_, 0, v___x_492_);
v___x_494_ = v___x_489_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
case 0:
{
lean_del_object(v___x_486_);
if (v_isRoot_471_ == 0)
{
lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_506_; 
v_isSharedCheck_506_ = !lean_is_exclusive(v_value_484_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_value_484_, 0);
lean_dec(v_unused_507_);
v___x_499_ = v_value_484_;
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
else
{
lean_dec(v_value_484_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_506_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_501_ = 1;
v___x_502_ = lean_box(v___x_501_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_502_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
lean_object* v_val_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_val_508_ = lean_ctor_get(v_value_484_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v_value_484_);
if (v_isSharedCheck_518_ == 0)
{
v___x_510_ = v_value_484_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_val_508_);
lean_dec(v_value_484_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_512_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0, &l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0);
v___x_513_ = lean_nat_dec_le(v___x_512_, v_val_508_);
lean_dec(v_val_508_);
v___x_514_ = lean_box(v___x_513_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_514_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
default: 
{
lean_dec_ref(v_value_484_);
if (v_isRoot_471_ == 0)
{
uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = 1;
v___x_520_ = lean_box(v___x_519_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_520_);
v___x_522_ = v___x_486_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
else
{
uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_524_ = 0;
v___x_525_ = lean_box(v___x_524_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_525_);
v___x_527_ = v___x_486_;
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
}
}
case 1:
{
if (v_isRoot_471_ == 0)
{
uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = 1;
v___x_531_ = lean_box(v___x_530_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
else
{
uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = 0;
v___x_534_ = lean_box(v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
case 2:
{
lean_object* v_struct_536_; lean_object* v___x_537_; 
v_struct_536_ = lean_ctor_get(v_v_472_, 2);
lean_inc(v_struct_536_);
lean_dec_ref_known(v_v_472_, 3);
v___x_537_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_struct_536_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_537_;
}
case 3:
{
lean_object* v_declName_538_; lean_object* v_args_539_; lean_object* v_sccDecls_540_; lean_object* v___x_541_; uint8_t v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; uint8_t v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; uint8_t v___y_595_; uint8_t v___y_599_; uint8_t v___y_600_; uint8_t v___y_604_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_declName_538_ = lean_ctor_get(v_v_472_, 0);
lean_inc(v_declName_538_);
v_args_539_ = lean_ctor_get(v_v_472_, 2);
lean_inc_ref(v_args_539_);
lean_dec_ref_known(v_v_472_, 3);
v_sccDecls_540_ = lean_ctor_get(v_a_473_, 1);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_array_get_size(v_sccDecls_540_);
v___x_624_ = lean_nat_dec_lt(v___x_541_, v___x_623_);
if (v___x_624_ == 0)
{
v___y_604_ = v___x_624_;
goto v___jp_603_;
}
else
{
if (v___x_624_ == 0)
{
v___y_604_ = v___x_624_;
goto v___jp_603_;
}
else
{
size_t v___x_625_; size_t v___x_626_; uint8_t v___x_627_; 
v___x_625_ = ((size_t)0ULL);
v___x_626_ = lean_usize_of_nat(v___x_623_);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_538_, v_sccDecls_540_, v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
v___y_604_ = v___x_627_;
goto v___jp_603_;
}
else
{
uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec_ref(v_args_539_);
lean_dec(v_declName_538_);
v___x_628_ = 0;
v___x_629_ = lean_box(v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
v___jp_542_:
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = lean_array_get_size(v_args_539_);
v___x_551_ = lean_nat_dec_lt(v___x_541_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec_ref(v_args_539_);
goto v___jp_480_;
}
else
{
if (v___x_551_ == 0)
{
lean_dec_ref(v_args_539_);
goto v___jp_480_;
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = ((size_t)0ULL);
v___x_553_ = lean_usize_of_nat(v___x_550_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___y_543_, v_args_539_, v___x_552_, v___x_553_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
lean_dec_ref(v_args_539_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_564_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_564_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_564_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_564_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint8_t v___x_559_; 
v___x_559_ = lean_unbox(v_a_555_);
lean_dec(v_a_555_);
if (v___x_559_ == 0)
{
lean_del_object(v___x_557_);
goto v___jp_480_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_box(v___y_543_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_560_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
return v___x_554_;
}
}
}
}
v___jp_565_:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_538_, v___y_572_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_585_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_585_ == 0)
{
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
if (lean_obj_tag(v_a_574_) == 1)
{
lean_object* v_val_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_val_578_ = lean_ctor_get(v_a_574_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v_a_574_, 1);
v___x_579_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_578_);
lean_dec(v_val_578_);
v___x_580_ = lean_nat_dec_eq(v___x_579_, v___x_541_);
lean_dec(v___x_579_);
if (v___x_580_ == 0)
{
lean_del_object(v___x_576_);
v___y_543_ = v___y_566_;
v___y_544_ = v___y_567_;
v___y_545_ = v___y_568_;
v___y_546_ = v___y_569_;
v___y_547_ = v___y_570_;
v___y_548_ = v___y_571_;
v___y_549_ = v___y_572_;
goto v___jp_542_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_583_; 
lean_dec_ref(v_args_539_);
v___x_581_ = lean_box(v___y_566_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_581_);
v___x_583_ = v___x_576_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
v___y_543_ = v___y_566_;
v___y_544_ = v___y_567_;
v___y_545_ = v___y_568_;
v___y_546_ = v___y_569_;
v___y_547_ = v___y_570_;
v___y_548_ = v___y_571_;
v___y_549_ = v___y_572_;
goto v___jp_542_;
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v_args_539_);
v_a_586_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_573_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_573_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
v___jp_594_:
{
if (v___y_595_ == 0)
{
v___y_566_ = v___y_595_;
v___y_567_ = v_a_473_;
v___y_568_ = v_a_474_;
v___y_569_ = v_a_475_;
v___y_570_ = v_a_476_;
v___y_571_ = v_a_477_;
v___y_572_ = v_a_478_;
goto v___jp_565_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec_ref(v_args_539_);
lean_dec(v_declName_538_);
v___x_596_ = lean_box(v___y_595_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
v___jp_598_:
{
if (v___y_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec_ref(v_args_539_);
lean_dec(v_declName_538_);
v___x_601_ = lean_box(v___y_599_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
else
{
v___y_595_ = v___y_599_;
goto v___jp_594_;
}
}
v___jp_603_:
{
lean_object* v___x_605_; lean_object* v_env_606_; uint8_t v___x_607_; 
v___x_605_ = lean_st_ref_get(v_a_478_);
v_env_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc_ref(v_env_606_);
lean_dec(v___x_605_);
lean_inc(v_declName_538_);
v___x_607_ = l_Lean_hasNeverExtractAttribute(v_env_606_, v_declName_538_);
if (v___x_607_ == 0)
{
if (v_isRoot_471_ == 0)
{
lean_dec(v_declName_538_);
v___y_543_ = v___x_607_;
v___y_544_ = v_a_473_;
v___y_545_ = v_a_474_;
v___y_546_ = v_a_475_;
v___y_547_ = v_a_476_;
v___y_548_ = v_a_477_;
v___y_549_ = v_a_478_;
goto v___jp_542_;
}
else
{
lean_object* v___x_608_; lean_object* v_env_609_; lean_object* v___x_610_; 
v___x_608_ = lean_st_ref_get(v_a_478_);
v_env_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc_ref(v_env_609_);
lean_dec(v___x_608_);
lean_inc(v_declName_538_);
v___x_610_ = l_Lean_Environment_find_x3f(v_env_609_, v_declName_538_, v___x_607_);
if (lean_obj_tag(v___x_610_) == 1)
{
lean_object* v_val_611_; 
v_val_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v___x_610_, 1);
switch(lean_obj_tag(v_val_611_))
{
case 1:
{
lean_object* v_val_612_; lean_object* v_toConstantVal_613_; lean_object* v_type_614_; uint8_t v___x_615_; 
v_val_612_ = lean_ctor_get(v_val_611_, 0);
lean_inc_ref(v_val_612_);
lean_dec_ref_known(v_val_611_, 1);
v_toConstantVal_613_ = lean_ctor_get(v_val_612_, 0);
lean_inc_ref(v_toConstantVal_613_);
lean_dec_ref(v_val_612_);
v_type_614_ = lean_ctor_get(v_toConstantVal_613_, 2);
lean_inc_ref(v_type_614_);
lean_dec_ref(v_toConstantVal_613_);
v___x_615_ = l_Lean_Expr_isForall(v_type_614_);
lean_dec_ref(v_type_614_);
v___y_599_ = v___x_607_;
v___y_600_ = v___x_615_;
goto v___jp_598_;
}
case 6:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
lean_dec_ref_known(v_val_611_, 1);
v___x_616_ = lean_array_get_size(v_args_539_);
v___x_617_ = lean_nat_dec_lt(v___x_541_, v___x_616_);
if (v___x_617_ == 0)
{
v___y_599_ = v___x_607_;
v___y_600_ = v___x_607_;
goto v___jp_598_;
}
else
{
if (v___x_617_ == 0)
{
v___y_599_ = v___x_607_;
v___y_600_ = v___x_607_;
goto v___jp_598_;
}
else
{
size_t v___x_618_; size_t v___x_619_; uint8_t v___x_620_; 
v___x_618_ = ((size_t)0ULL);
v___x_619_ = lean_usize_of_nat(v___x_616_);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_471_, v___x_607_, v_args_539_, v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
v___y_599_ = v___x_607_;
v___y_600_ = v___x_607_;
goto v___jp_598_;
}
else
{
if (v___x_607_ == 0)
{
v___y_595_ = v___x_607_;
goto v___jp_594_;
}
else
{
v___y_599_ = v___x_607_;
v___y_600_ = v___x_607_;
goto v___jp_598_;
}
}
}
}
}
default: 
{
lean_dec(v_val_611_);
v___y_595_ = v___x_607_;
goto v___jp_594_;
}
}
}
else
{
lean_dec(v___x_610_);
v___y_566_ = v___x_607_;
v___y_567_ = v_a_473_;
v___y_568_ = v_a_474_;
v___y_569_ = v_a_475_;
v___y_570_ = v_a_476_;
v___y_571_ = v_a_477_;
v___y_572_ = v_a_478_;
goto v___jp_565_;
}
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec_ref(v_args_539_);
lean_dec(v_declName_538_);
v___x_621_ = lean_box(v___y_604_);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
}
default: 
{
lean_object* v_fvarId_631_; lean_object* v_args_632_; lean_object* v___x_633_; 
v_fvarId_631_ = lean_ctor_get(v_v_472_, 0);
lean_inc(v_fvarId_631_);
v_args_632_ = lean_ctor_get(v_v_472_, 1);
lean_inc_ref(v_args_632_);
lean_dec_ref_known(v_v_472_, 2);
v___x_633_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_631_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___y_636_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = lean_array_get_size(v_args_632_);
v___x_648_ = lean_nat_dec_lt(v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
lean_dec_ref(v_args_632_);
v___x_649_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_648_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
v___y_636_ = v___x_649_;
goto v___jp_635_;
}
else
{
if (v___x_648_ == 0)
{
lean_object* v___x_650_; 
lean_dec_ref(v_args_632_);
v___x_650_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_648_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
v___y_636_ = v___x_650_;
goto v___jp_635_;
}
else
{
size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; 
v___x_651_ = ((size_t)0ULL);
v___x_652_ = lean_usize_of_nat(v___x_647_);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_args_632_, v___x_651_, v___x_652_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec_ref(v_args_632_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; uint8_t v___x_655_; lean_object* v___x_656_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = lean_unbox(v_a_654_);
lean_dec(v_a_654_);
v___x_656_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_655_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
v___y_636_ = v___x_656_;
goto v___jp_635_;
}
else
{
v___y_636_ = v___x_653_;
goto v___jp_635_;
}
}
}
v___jp_635_:
{
if (lean_obj_tag(v___y_636_) == 0)
{
uint8_t v___x_637_; 
v___x_637_ = lean_unbox(v_a_634_);
if (v___x_637_ == 0)
{
lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
v_isSharedCheck_644_ = !lean_is_exclusive(v___y_636_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v___y_636_, 0);
lean_dec(v_unused_645_);
v___x_639_ = v___y_636_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_dec(v___y_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v_a_634_);
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_634_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
else
{
lean_dec(v_a_634_);
return v___y_636_;
}
}
else
{
lean_dec(v_a_634_);
return v___y_636_;
}
}
}
else
{
lean_dec_ref(v_args_632_);
return v___x_633_;
}
}
}
v___jp_480_:
{
uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = 1;
v___x_482_ = lean_box(v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(lean_object* v_fvarId_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
uint8_t v___x_665_; lean_object* v___x_666_; 
v___x_665_ = 0;
v___x_666_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_665_, v_fvarId_657_, v_a_661_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_680_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_680_ == 0)
{
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_680_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_680_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
if (lean_obj_tag(v_a_667_) == 1)
{
lean_object* v_val_671_; lean_object* v_value_672_; uint8_t v___x_673_; lean_object* v___x_674_; 
lean_del_object(v___x_669_);
v_val_671_ = lean_ctor_get(v_a_667_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v_a_667_, 1);
v_value_672_ = lean_ctor_get(v_val_671_, 3);
lean_inc(v_value_672_);
lean_dec(v_val_671_);
v___x_673_ = 0;
v___x_674_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_673_, v_value_672_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
return v___x_674_;
}
else
{
uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
lean_dec(v_a_667_);
v___x_675_ = 0;
v___x_676_ = lean_box(v___x_675_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_676_);
v___x_678_ = v___x_669_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_681_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_666_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_666_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object* v_fvarId_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; lean_object* v_fvarDecisionCache_698_; lean_object* v___x_699_; 
v___x_697_ = lean_st_ref_get(v_a_691_);
v_fvarDecisionCache_698_ = lean_ctor_get(v___x_697_, 1);
lean_inc_ref(v_fvarDecisionCache_698_);
lean_dec(v___x_697_);
v___x_699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_fvarDecisionCache_698_, v_fvarId_689_);
lean_dec_ref(v_fvarDecisionCache_698_);
if (lean_obj_tag(v___x_699_) == 1)
{
lean_object* v_val_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v_fvarId_689_);
v_val_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_val_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 0);
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_val_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
else
{
lean_object* v___x_708_; 
lean_dec(v___x_699_);
v___x_708_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_728_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_728_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_728_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_728_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v_decls_714_; lean_object* v_fvarDecisionCache_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_727_; 
v___x_713_ = lean_st_ref_take(v_a_691_);
v_decls_714_ = lean_ctor_get(v___x_713_, 0);
v_fvarDecisionCache_715_ = lean_ctor_get(v___x_713_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_727_ == 0)
{
v___x_717_ = v___x_713_;
v_isShared_718_ = v_isSharedCheck_727_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_fvarDecisionCache_715_);
lean_inc(v_decls_714_);
lean_dec(v___x_713_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_727_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
lean_inc(v_a_709_);
v___x_719_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_fvarDecisionCache_715_, v_fvarId_689_, v_a_709_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 1, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_decls_714_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_719_);
v___x_721_ = v_reuseFailAlloc_726_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_st_ref_put(v_a_691_, v___x_721_);
if (v_isShared_712_ == 0)
{
v___x_724_ = v___x_711_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_709_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_689_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object* v_arg_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
if (lean_obj_tag(v_arg_729_) == 1)
{
lean_object* v_fvarId_737_; lean_object* v___x_738_; 
v_fvarId_737_ = lean_ctor_get(v_arg_729_, 0);
lean_inc(v_fvarId_737_);
lean_dec_ref_known(v_arg_729_, 1);
v___x_738_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_737_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
return v___x_738_;
}
else
{
uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_arg_729_);
v___x_739_ = 1;
v___x_740_ = lean_box(v___x_739_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object* v_arg_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v_arg_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(lean_object* v_fvarId_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_fvarId_751_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object* v_fvarId_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object* v___x_769_, lean_object* v_as_770_, lean_object* v_i_771_, lean_object* v_stop_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v___x_15184__boxed_780_; size_t v_i_boxed_781_; size_t v_stop_boxed_782_; lean_object* v_res_783_; 
v___x_15184__boxed_780_ = lean_unbox(v___x_769_);
v_i_boxed_781_ = lean_unbox_usize(v_i_771_);
lean_dec(v_i_771_);
v_stop_boxed_782_ = lean_unbox_usize(v_stop_772_);
lean_dec(v_stop_772_);
v_res_783_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___x_15184__boxed_780_, v_as_770_, v_i_boxed_781_, v_stop_boxed_782_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec_ref(v_as_770_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(lean_object* v_as_784_, lean_object* v_i_785_, lean_object* v_stop_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
size_t v_i_boxed_794_; size_t v_stop_boxed_795_; lean_object* v_res_796_; 
v_i_boxed_794_ = lean_unbox_usize(v_i_785_);
lean_dec(v_i_785_);
v_stop_boxed_795_ = lean_unbox_usize(v_stop_786_);
lean_dec(v_stop_786_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_as_784_, v_i_boxed_794_, v_stop_boxed_795_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec_ref(v_as_784_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object* v_isRoot_797_, lean_object* v_v_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
uint8_t v_isRoot_boxed_806_; lean_object* v_res_807_; 
v_isRoot_boxed_806_ = lean_unbox(v_isRoot_797_);
v_res_807_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v_isRoot_boxed_806_, v_v_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object* v_00_u03b2_808_, lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_809_, v_a_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___boxed(lean_object* v_00_u03b2_812_, lean_object* v_m_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(v_00_u03b2_812_, v_m_813_, v_a_814_);
lean_dec(v_a_814_);
lean_dec_ref(v_m_813_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(lean_object* v_00_u03b2_816_, lean_object* v_m_817_, lean_object* v_a_818_, lean_object* v_b_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_m_817_, v_a_818_, v_b_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(lean_object* v_00_u03b2_821_, lean_object* v_a_822_, lean_object* v_x_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_822_, v_x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___boxed(lean_object* v_00_u03b2_825_, lean_object* v_a_826_, lean_object* v_x_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(v_00_u03b2_825_, v_a_826_, v_x_827_);
lean_dec(v_x_827_);
lean_dec(v_a_826_);
return v_res_828_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(lean_object* v_00_u03b2_829_, lean_object* v_a_830_, lean_object* v_x_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_830_, v_x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___boxed(lean_object* v_00_u03b2_833_, lean_object* v_a_834_, lean_object* v_x_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(v_00_u03b2_833_, v_a_834_, v_x_835_);
lean_dec(v_x_835_);
lean_dec(v_a_834_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10(lean_object* v_00_u03b2_838_, lean_object* v_data_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_data_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11(lean_object* v_00_u03b2_841_, lean_object* v_a_842_, lean_object* v_b_843_, lean_object* v_x_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_842_, v_b_843_, v_x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_846_, lean_object* v_i_847_, lean_object* v_source_848_, lean_object* v_target_849_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v_i_847_, v_source_848_, v_target_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_x_852_, v_x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(lean_object* v_prevArrayId_860_, lean_object* v_decl_861_, lean_object* v_k_862_, lean_object* v_illegalSet_863_, lean_object* v_size_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_decl_876_; lean_object* v_k_877_; lean_object* v_illegalSet_878_; lean_object* v_zero_886_; uint8_t v_isZero_887_; 
v_zero_886_ = lean_unsigned_to_nat(0u);
v_isZero_887_ = lean_nat_dec_eq(v_size_864_, v_zero_886_);
if (v_isZero_887_ == 1)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v_size_864_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
lean_dec(v_prevArrayId_860_);
v___x_888_ = lean_box(0);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
else
{
lean_object* v_value_890_; 
v_value_890_ = lean_ctor_get(v_decl_861_, 3);
if (lean_obj_tag(v_value_890_) == 3)
{
lean_object* v_declName_891_; 
v_declName_891_ = lean_ctor_get(v_value_890_, 0);
if (lean_obj_tag(v_declName_891_) == 1)
{
lean_object* v_pre_892_; 
v_pre_892_ = lean_ctor_get(v_declName_891_, 0);
if (lean_obj_tag(v_pre_892_) == 1)
{
lean_object* v_pre_893_; 
v_pre_893_ = lean_ctor_get(v_pre_892_, 0);
if (lean_obj_tag(v_pre_893_) == 0)
{
lean_object* v_fvarId_894_; lean_object* v_args_895_; lean_object* v_str_896_; lean_object* v_str_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_fvarId_894_ = lean_ctor_get(v_decl_861_, 0);
v_args_895_ = lean_ctor_get(v_value_890_, 2);
v_str_896_ = lean_ctor_get(v_declName_891_, 1);
v_str_897_ = lean_ctor_get(v_pre_892_, 1);
v___x_898_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_899_ = lean_string_dec_eq(v_str_897_, v___x_898_);
if (v___x_899_ == 0)
{
lean_dec(v_size_864_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
lean_dec(v_prevArrayId_860_);
goto v___jp_872_;
}
else
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_901_ = lean_string_dec_eq(v_str_896_, v___x_900_);
if (v___x_901_ == 0)
{
lean_dec(v_size_864_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
lean_dec(v_prevArrayId_860_);
goto v___jp_872_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_array_get_size(v_args_895_);
v___x_903_ = lean_unsigned_to_nat(3u);
v___x_904_ = lean_nat_dec_eq(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_dec(v_size_864_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
lean_dec(v_prevArrayId_860_);
goto v___jp_872_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_array_fget(v_args_895_, v___x_905_);
if (lean_obj_tag(v___x_906_) == 1)
{
lean_object* v_fvarId_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_1024_; 
v_fvarId_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_1024_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_fvarId_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_1024_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
uint8_t v___x_911_; 
v___x_911_ = l_Lean_instBEqFVarId_beq(v_fvarId_907_, v_prevArrayId_860_);
lean_dec(v_prevArrayId_860_);
lean_dec(v_fvarId_907_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_914_; 
lean_dec(v_size_864_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
v___x_912_ = lean_box(0);
if (v_isShared_910_ == 0)
{
lean_ctor_set_tag(v___x_909_, 0);
lean_ctor_set(v___x_909_, 0, v___x_912_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
else
{
lean_object* v_n_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_del_object(v___x_909_);
v_n_916_ = lean_nat_sub(v_size_864_, v___x_905_);
lean_dec(v_size_864_);
v___x_917_ = lean_unsigned_to_nat(2u);
v___x_918_ = lean_array_fget_borrowed(v_args_895_, v___x_917_);
lean_inc(v___x_918_);
v___x_919_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_918_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_1015_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_1015_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_1015_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
uint8_t v___x_924_; 
v___x_924_ = lean_unbox(v_a_920_);
lean_dec(v_a_920_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_927_; 
lean_dec(v_n_916_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
v___x_925_ = lean_box(0);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_925_);
v___x_927_ = v___x_922_;
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
else
{
uint8_t v___x_929_; 
v___x_929_ = lean_nat_dec_eq(v_n_916_, v_zero_886_);
if (v___x_929_ == 0)
{
lean_inc(v_fvarId_894_);
lean_dec_ref(v_decl_861_);
if (lean_obj_tag(v_k_862_) == 0)
{
lean_object* v_decl_930_; lean_object* v_k_931_; lean_object* v___x_932_; 
lean_del_object(v___x_922_);
v_decl_930_ = lean_ctor_get(v_k_862_, 0);
lean_inc_ref(v_decl_930_);
v_k_931_ = lean_ctor_get(v_k_862_, 1);
lean_inc_ref(v_k_931_);
lean_dec_ref_known(v_k_862_, 2);
lean_inc(v_fvarId_894_);
v___x_932_ = l_Lean_FVarIdSet_insert(v_illegalSet_863_, v_fvarId_894_);
v_prevArrayId_860_ = v_fvarId_894_;
v_decl_861_ = v_decl_930_;
v_k_862_ = v_k_931_;
v_illegalSet_863_ = v___x_932_;
v_size_864_ = v_n_916_;
goto _start;
}
else
{
lean_object* v___x_934_; lean_object* v___x_936_; 
lean_dec(v_n_916_);
lean_dec(v_fvarId_894_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
v___x_934_ = lean_box(0);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_934_);
v___x_936_ = v___x_922_;
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
}
else
{
lean_del_object(v___x_922_);
lean_dec(v_n_916_);
if (lean_obj_tag(v_k_862_) == 0)
{
lean_object* v_decl_938_; lean_object* v_value_939_; 
v_decl_938_ = lean_ctor_get(v_k_862_, 0);
lean_inc_ref(v_decl_938_);
v_value_939_ = lean_ctor_get(v_decl_938_, 3);
lean_inc(v_value_939_);
if (lean_obj_tag(v_value_939_) == 3)
{
lean_object* v_declName_940_; 
v_declName_940_ = lean_ctor_get(v_value_939_, 0);
lean_inc(v_declName_940_);
if (lean_obj_tag(v_declName_940_) == 1)
{
lean_object* v_pre_941_; 
v_pre_941_ = lean_ctor_get(v_declName_940_, 0);
lean_inc(v_pre_941_);
if (lean_obj_tag(v_pre_941_) == 1)
{
lean_object* v_pre_942_; 
v_pre_942_ = lean_ctor_get(v_pre_941_, 0);
lean_inc(v_pre_942_);
if (lean_obj_tag(v_pre_942_) == 0)
{
lean_object* v_k_943_; lean_object* v_fvarId_944_; lean_object* v_binderName_945_; lean_object* v_type_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1013_; 
v_k_943_ = lean_ctor_get(v_k_862_, 1);
v_fvarId_944_ = lean_ctor_get(v_decl_938_, 0);
v_binderName_945_ = lean_ctor_get(v_decl_938_, 1);
v_type_946_ = lean_ctor_get(v_decl_938_, 2);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_decl_938_);
if (v_isSharedCheck_1013_ == 0)
{
lean_object* v_unused_1014_; 
v_unused_1014_ = lean_ctor_get(v_decl_938_, 3);
lean_dec(v_unused_1014_);
v___x_948_ = v_decl_938_;
v_isShared_949_ = v_isSharedCheck_1013_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_type_946_);
lean_inc(v_binderName_945_);
lean_inc(v_fvarId_944_);
lean_dec(v_decl_938_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1013_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_us_950_; lean_object* v_args_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1011_; 
v_us_950_ = lean_ctor_get(v_value_939_, 1);
v_args_951_ = lean_ctor_get(v_value_939_, 2);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_value_939_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v_value_939_, 0);
lean_dec(v_unused_1012_);
v___x_953_ = v_value_939_;
v_isShared_954_ = v_isSharedCheck_1011_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_args_951_);
lean_inc(v_us_950_);
lean_dec(v_value_939_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1011_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_str_955_; lean_object* v_str_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_str_955_ = lean_ctor_get(v_declName_940_, 1);
lean_inc_ref(v_str_955_);
lean_dec_ref_known(v_declName_940_, 2);
v_str_956_ = lean_ctor_get(v_pre_941_, 1);
lean_inc_ref(v_str_956_);
lean_dec_ref_known(v_pre_941_, 2);
v___x_957_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2));
v___x_958_ = lean_string_dec_eq(v_str_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3));
v___x_960_ = lean_string_dec_eq(v_str_956_, v___x_959_);
lean_dec_ref(v_str_956_);
if (v___x_960_ == 0)
{
lean_dec_ref(v_str_955_);
lean_del_object(v___x_953_);
lean_dec_ref(v_args_951_);
lean_dec(v_us_950_);
lean_del_object(v___x_948_);
lean_dec_ref(v_type_946_);
lean_dec(v_binderName_945_);
lean_dec(v_fvarId_944_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
else
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_962_ = lean_string_dec_eq(v_str_955_, v___x_961_);
lean_dec_ref(v_str_955_);
if (v___x_962_ == 0)
{
lean_del_object(v___x_953_);
lean_dec_ref(v_args_951_);
lean_dec(v_us_950_);
lean_del_object(v___x_948_);
lean_dec_ref(v_type_946_);
lean_dec(v_binderName_945_);
lean_dec(v_fvarId_944_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
else
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_array_get_size(v_args_951_);
v___x_964_ = lean_nat_dec_eq(v___x_963_, v___x_905_);
if (v___x_964_ == 0)
{
lean_del_object(v___x_953_);
lean_dec_ref(v_args_951_);
lean_dec(v_us_950_);
lean_del_object(v___x_948_);
lean_dec_ref(v_type_946_);
lean_dec(v_binderName_945_);
lean_dec(v_fvarId_944_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
else
{
lean_object* v___x_965_; 
v___x_965_ = lean_array_fget(v_args_951_, v_zero_886_);
lean_dec_ref(v_args_951_);
if (lean_obj_tag(v___x_965_) == 1)
{
lean_object* v_fvarId_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_985_; 
v_fvarId_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_985_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_985_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_fvarId_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_985_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
uint8_t v___x_970_; 
v___x_970_ = l_Lean_instBEqFVarId_beq(v_fvarId_966_, v_fvarId_894_);
if (v___x_970_ == 0)
{
lean_del_object(v___x_968_);
lean_dec(v_fvarId_966_);
lean_del_object(v___x_953_);
lean_dec(v_us_950_);
lean_del_object(v___x_948_);
lean_dec_ref(v_type_946_);
lean_dec(v_binderName_945_);
lean_dec(v_fvarId_944_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
lean_inc_ref(v_k_943_);
lean_inc(v_fvarId_894_);
lean_dec_ref_known(v_k_862_, 2);
lean_dec_ref(v_decl_861_);
v___x_971_ = l_Lean_Name_str___override(v_pre_942_, v___x_959_);
v___x_972_ = l_Lean_Name_str___override(v___x_971_, v___x_961_);
if (v_isShared_969_ == 0)
{
v___x_974_ = v___x_968_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_fvarId_966_);
v___x_974_ = v_reuseFailAlloc_984_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_975_ = lean_mk_empty_array_with_capacity(v___x_905_);
v___x_976_ = lean_array_push(v___x_975_, v___x_974_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 2, v___x_976_);
lean_ctor_set(v___x_953_, 0, v___x_972_);
v___x_978_ = v___x_953_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_us_950_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v___x_976_);
v___x_978_ = v_reuseFailAlloc_983_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 3, v___x_978_);
v___x_980_ = v___x_948_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_fvarId_944_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_binderName_945_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_type_946_);
lean_ctor_set(v_reuseFailAlloc_982_, 3, v___x_978_);
v___x_980_ = v_reuseFailAlloc_982_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_FVarIdSet_insert(v_illegalSet_863_, v_fvarId_894_);
v_decl_876_ = v___x_980_;
v_k_877_ = v_k_943_;
v_illegalSet_878_ = v___x_981_;
goto v___jp_875_;
}
}
}
}
}
}
else
{
lean_dec(v___x_965_);
lean_del_object(v___x_953_);
lean_dec(v_us_950_);
lean_del_object(v___x_948_);
lean_dec_ref(v_type_946_);
lean_dec(v_binderName_945_);
lean_dec(v_fvarId_944_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
}
}
}
}
else
{
lean_object* v___x_986_; uint8_t v___x_987_; 
lean_dec_ref(v_str_956_);
v___x_986_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_987_ = lean_string_dec_eq(v_str_955_, v___x_986_);
lean_dec_ref(v_str_955_);
if (v___x_987_ == 0)
{
lean_del_object(v___x_953_);
lean_dec_ref(v_args_951_);
lean_dec(v_us_950_);
lean_del_object(v___x_948_);
lean_dec_ref(v_type_946_);
lean_dec(v_binderName_945_);
lean_dec(v_fvarId_944_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
else
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = lean_array_get_size(v_args_951_);
v___x_989_ = lean_nat_dec_eq(v___x_988_, v___x_905_);
if (v___x_989_ == 0)
{
lean_del_object(v___x_953_);
lean_dec_ref(v_args_951_);
lean_dec(v_us_950_);
lean_del_object(v___x_948_);
lean_dec_ref(v_type_946_);
lean_dec(v_binderName_945_);
lean_dec(v_fvarId_944_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = lean_array_fget(v_args_951_, v_zero_886_);
lean_dec_ref(v_args_951_);
if (lean_obj_tag(v___x_990_) == 1)
{
lean_object* v_fvarId_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1010_; 
v_fvarId_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1010_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_fvarId_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1010_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
uint8_t v___x_995_; 
v___x_995_ = l_Lean_instBEqFVarId_beq(v_fvarId_991_, v_fvarId_894_);
if (v___x_995_ == 0)
{
lean_del_object(v___x_993_);
lean_dec(v_fvarId_991_);
lean_del_object(v___x_953_);
lean_dec(v_us_950_);
lean_del_object(v___x_948_);
lean_dec_ref(v_type_946_);
lean_dec(v_binderName_945_);
lean_dec(v_fvarId_944_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
lean_inc_ref(v_k_943_);
lean_inc(v_fvarId_894_);
lean_dec_ref_known(v_k_862_, 2);
lean_dec_ref(v_decl_861_);
v___x_996_ = l_Lean_Name_str___override(v_pre_942_, v___x_957_);
v___x_997_ = l_Lean_Name_str___override(v___x_996_, v___x_986_);
if (v_isShared_994_ == 0)
{
v___x_999_ = v___x_993_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_fvarId_991_);
v___x_999_ = v_reuseFailAlloc_1009_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1000_ = lean_mk_empty_array_with_capacity(v___x_905_);
v___x_1001_ = lean_array_push(v___x_1000_, v___x_999_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 2, v___x_1001_);
lean_ctor_set(v___x_953_, 0, v___x_997_);
v___x_1003_ = v___x_953_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_us_950_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 3, v___x_1003_);
v___x_1005_ = v___x_948_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_fvarId_944_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_binderName_945_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_type_946_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_FVarIdSet_insert(v_illegalSet_863_, v_fvarId_894_);
v_decl_876_ = v___x_1005_;
v_k_877_ = v_k_943_;
v_illegalSet_878_ = v___x_1006_;
goto v___jp_875_;
}
}
}
}
}
}
else
{
lean_dec(v___x_990_);
lean_del_object(v___x_953_);
lean_dec(v_us_950_);
lean_del_object(v___x_948_);
lean_dec_ref(v_type_946_);
lean_dec(v_binderName_945_);
lean_dec(v_fvarId_944_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
}
}
}
}
}
}
else
{
lean_dec(v_pre_942_);
lean_dec_ref_known(v_pre_941_, 2);
lean_dec_ref_known(v_declName_940_, 2);
lean_dec_ref_known(v_value_939_, 3);
lean_dec_ref(v_decl_938_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
}
else
{
lean_dec(v_pre_941_);
lean_dec_ref_known(v_declName_940_, 2);
lean_dec_ref_known(v_value_939_, 3);
lean_dec_ref(v_decl_938_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
}
else
{
lean_dec_ref_known(v_value_939_, 3);
lean_dec(v_declName_940_);
lean_dec_ref(v_decl_938_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
}
else
{
lean_dec(v_value_939_);
lean_dec_ref(v_decl_938_);
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
}
else
{
v_decl_876_ = v_decl_861_;
v_k_877_ = v_k_862_;
v_illegalSet_878_ = v_illegalSet_863_;
goto v___jp_875_;
}
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_n_916_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
v_a_1016_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_919_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_919_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
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
}
}
else
{
lean_dec(v___x_906_);
lean_dec(v_size_864_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
lean_dec(v_prevArrayId_860_);
goto v___jp_872_;
}
}
}
}
}
else
{
lean_dec(v_size_864_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
lean_dec(v_prevArrayId_860_);
goto v___jp_872_;
}
}
else
{
lean_dec(v_size_864_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
lean_dec(v_prevArrayId_860_);
goto v___jp_872_;
}
}
else
{
lean_dec(v_size_864_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
lean_dec(v_prevArrayId_860_);
goto v___jp_872_;
}
}
else
{
lean_dec(v_size_864_);
lean_dec(v_illegalSet_863_);
lean_dec_ref(v_k_862_);
lean_dec_ref(v_decl_861_);
lean_dec(v_prevArrayId_860_);
goto v___jp_872_;
}
}
v___jp_872_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_box(0);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
v___jp_875_:
{
uint8_t v___x_879_; uint8_t v___x_880_; 
v___x_879_ = 0;
v___x_880_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_879_, v_k_877_, v_illegalSet_878_);
lean_dec(v_illegalSet_878_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v_decl_876_);
lean_ctor_set(v___x_881_, 1, v_k_877_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec_ref(v_k_877_);
lean_dec_ref(v_decl_876_);
v___x_884_ = lean_box(0);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___boxed(lean_object* v_prevArrayId_1025_, lean_object* v_decl_1026_, lean_object* v_k_1027_, lean_object* v_illegalSet_1028_, lean_object* v_size_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_prevArrayId_1025_, v_decl_1026_, v_k_1027_, v_illegalSet_1028_, v_size_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(lean_object* v_decl_1040_, lean_object* v_k_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_value_1058_; 
v_value_1058_ = lean_ctor_get(v_decl_1040_, 3);
if (lean_obj_tag(v_value_1058_) == 3)
{
lean_object* v_declName_1059_; 
v_declName_1059_ = lean_ctor_get(v_value_1058_, 0);
if (lean_obj_tag(v_declName_1059_) == 1)
{
lean_object* v_pre_1060_; 
v_pre_1060_ = lean_ctor_get(v_declName_1059_, 0);
if (lean_obj_tag(v_pre_1060_) == 1)
{
lean_object* v_pre_1061_; 
v_pre_1061_ = lean_ctor_get(v_pre_1060_, 0);
if (lean_obj_tag(v_pre_1061_) == 0)
{
lean_object* v_args_1062_; lean_object* v_str_1063_; lean_object* v_str_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_args_1062_ = lean_ctor_get(v_value_1058_, 2);
v_str_1063_ = lean_ctor_get(v_declName_1059_, 1);
v_str_1064_ = lean_ctor_get(v_pre_1060_, 1);
v___x_1065_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1066_ = lean_string_dec_eq(v_str_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1055_;
}
else
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_1068_ = lean_string_dec_eq(v_str_1063_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1055_;
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = lean_array_get_size(v_args_1062_);
v___x_1070_ = lean_unsigned_to_nat(3u);
v___x_1071_ = lean_nat_dec_eq(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1055_;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_array_fget_borrowed(v_args_1062_, v___x_1072_);
if (lean_obj_tag(v___x_1073_) == 1)
{
lean_object* v_fvarId_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; 
v_fvarId_1074_ = lean_ctor_get(v___x_1073_, 0);
v___x_1075_ = lean_box(1);
v___x_1076_ = 0;
v___x_1077_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_1076_, v_fvarId_1074_, v_a_1045_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1132_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1132_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1132_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
if (lean_obj_tag(v_a_1078_) == 1)
{
lean_object* v_val_1082_; lean_object* v_fvarId_1083_; lean_object* v_value_1084_; lean_object* v_sizeFVar_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; 
lean_del_object(v___x_1080_);
v_val_1082_ = lean_ctor_get(v_a_1078_, 0);
lean_inc(v_val_1082_);
lean_dec_ref_known(v_a_1078_, 1);
v_fvarId_1083_ = lean_ctor_get(v_val_1082_, 0);
lean_inc(v_fvarId_1083_);
v_value_1084_ = lean_ctor_get(v_val_1082_, 3);
lean_inc(v_value_1084_);
lean_dec(v_val_1082_);
if (lean_obj_tag(v_value_1084_) == 3)
{
lean_object* v_declName_1107_; 
v_declName_1107_ = lean_ctor_get(v_value_1084_, 0);
lean_inc(v_declName_1107_);
if (lean_obj_tag(v_declName_1107_) == 1)
{
lean_object* v_pre_1108_; 
v_pre_1108_ = lean_ctor_get(v_declName_1107_, 0);
lean_inc(v_pre_1108_);
if (lean_obj_tag(v_pre_1108_) == 1)
{
lean_object* v_pre_1109_; 
v_pre_1109_ = lean_ctor_get(v_pre_1108_, 0);
if (lean_obj_tag(v_pre_1109_) == 0)
{
lean_object* v_args_1110_; lean_object* v_str_1111_; lean_object* v_str_1112_; uint8_t v___x_1113_; 
v_args_1110_ = lean_ctor_get(v_value_1084_, 2);
lean_inc_ref(v_args_1110_);
lean_dec_ref_known(v_value_1084_, 3);
v_str_1111_ = lean_ctor_get(v_declName_1107_, 1);
lean_inc_ref(v_str_1111_);
lean_dec_ref_known(v_declName_1107_, 2);
v_str_1112_ = lean_ctor_get(v_pre_1108_, 1);
lean_inc_ref(v_str_1112_);
lean_dec_ref_known(v_pre_1108_, 2);
v___x_1113_ = lean_string_dec_eq(v_str_1112_, v___x_1065_);
lean_dec_ref(v_str_1112_);
if (v___x_1113_ == 0)
{
lean_dec_ref(v_str_1111_);
lean_dec_ref(v_args_1110_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1052_;
}
else
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1115_ = lean_string_dec_eq(v_str_1111_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1117_ = lean_string_dec_eq(v_str_1111_, v___x_1116_);
lean_dec_ref(v_str_1111_);
if (v___x_1117_ == 0)
{
lean_dec_ref(v_args_1110_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1052_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1118_ = lean_array_get_size(v_args_1110_);
v___x_1119_ = lean_unsigned_to_nat(2u);
v___x_1120_ = lean_nat_dec_eq(v___x_1118_, v___x_1119_);
if (v___x_1120_ == 0)
{
lean_dec_ref(v_args_1110_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1052_;
}
else
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_array_fget(v_args_1110_, v___x_1072_);
lean_dec_ref(v_args_1110_);
if (lean_obj_tag(v___x_1121_) == 1)
{
lean_object* v_fvarId_1122_; 
v_fvarId_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_fvarId_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v_sizeFVar_1086_ = v_fvarId_1122_;
v___y_1087_ = v_a_1042_;
v___y_1088_ = v_a_1043_;
v___y_1089_ = v_a_1044_;
v___y_1090_ = v_a_1045_;
v___y_1091_ = v_a_1046_;
v___y_1092_ = v_a_1047_;
goto v___jp_1085_;
}
else
{
lean_dec(v___x_1121_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1052_;
}
}
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
lean_dec_ref(v_str_1111_);
v___x_1123_ = lean_array_get_size(v_args_1110_);
v___x_1124_ = lean_unsigned_to_nat(2u);
v___x_1125_ = lean_nat_dec_eq(v___x_1123_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_dec_ref(v_args_1110_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1052_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_array_fget(v_args_1110_, v___x_1072_);
lean_dec_ref(v_args_1110_);
if (lean_obj_tag(v___x_1126_) == 1)
{
lean_object* v_fvarId_1127_; 
v_fvarId_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_fvarId_1127_);
lean_dec_ref_known(v___x_1126_, 1);
v_sizeFVar_1086_ = v_fvarId_1127_;
v___y_1087_ = v_a_1042_;
v___y_1088_ = v_a_1043_;
v___y_1089_ = v_a_1044_;
v___y_1090_ = v_a_1045_;
v___y_1091_ = v_a_1046_;
v___y_1092_ = v_a_1047_;
goto v___jp_1085_;
}
else
{
lean_dec(v___x_1126_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1052_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1108_, 2);
lean_dec_ref_known(v_declName_1107_, 2);
lean_dec_ref_known(v_value_1084_, 3);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1052_;
}
}
else
{
lean_dec(v_pre_1108_);
lean_dec_ref_known(v_declName_1107_, 2);
lean_dec_ref_known(v_value_1084_, 3);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1052_;
}
}
else
{
lean_dec_ref_known(v_value_1084_, 3);
lean_dec(v_declName_1107_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1052_;
}
}
else
{
lean_dec(v_value_1084_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1052_;
}
v___jp_1085_:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1076_, v_sizeFVar_1086_, v___y_1090_);
lean_dec(v_sizeFVar_1086_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
if (lean_obj_tag(v_a_1094_) == 1)
{
lean_object* v_val_1095_; 
v_val_1095_ = lean_ctor_get(v_a_1094_, 0);
lean_inc(v_val_1095_);
lean_dec_ref_known(v_a_1094_, 1);
if (lean_obj_tag(v_val_1095_) == 0)
{
lean_object* v_value_1096_; 
v_value_1096_ = lean_ctor_get(v_val_1095_, 0);
lean_inc_ref(v_value_1096_);
lean_dec_ref_known(v_val_1095_, 1);
if (lean_obj_tag(v_value_1096_) == 0)
{
lean_object* v_val_1097_; lean_object* v___x_1098_; 
v_val_1097_ = lean_ctor_get(v_value_1096_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v_value_1096_, 1);
v___x_1098_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_fvarId_1083_, v_decl_1040_, v_k_1041_, v___x_1075_, v_val_1097_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
return v___x_1098_;
}
else
{
lean_dec_ref(v_value_1096_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1049_;
}
}
else
{
lean_dec(v_val_1095_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1049_;
}
}
else
{
lean_dec(v_a_1094_);
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1049_;
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_fvarId_1083_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
v_a_1099_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1093_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1093_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
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
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_dec(v_a_1078_);
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
v___x_1128_ = lean_box(0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1128_);
v___x_1130_ = v___x_1080_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
v_a_1133_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1077_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1077_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1055_;
}
}
}
}
}
else
{
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1055_;
}
}
else
{
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1055_;
}
}
else
{
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1055_;
}
}
else
{
lean_dec_ref(v_k_1041_);
lean_dec_ref(v_decl_1040_);
goto v___jp_1055_;
}
v___jp_1049_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
v___jp_1052_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
v___jp_1055_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___boxed(lean_object* v_decl_1141_, lean_object* v_k_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1141_, v_k_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
return v_res_1150_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(lean_object* v_env_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; lean_object* v_nextMacroScope_1160_; lean_object* v_ngen_1161_; lean_object* v_auxDeclNGen_1162_; lean_object* v_traceState_1163_; lean_object* v_recordedDeps_1164_; lean_object* v_messages_1165_; lean_object* v_infoState_1166_; lean_object* v_snapshotTasks_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1178_; 
v___x_1159_ = lean_st_ref_take(v___y_1157_);
v_nextMacroScope_1160_ = lean_ctor_get(v___x_1159_, 1);
v_ngen_1161_ = lean_ctor_get(v___x_1159_, 2);
v_auxDeclNGen_1162_ = lean_ctor_get(v___x_1159_, 3);
v_traceState_1163_ = lean_ctor_get(v___x_1159_, 4);
v_recordedDeps_1164_ = lean_ctor_get(v___x_1159_, 6);
v_messages_1165_ = lean_ctor_get(v___x_1159_, 7);
v_infoState_1166_ = lean_ctor_get(v___x_1159_, 8);
v_snapshotTasks_1167_ = lean_ctor_get(v___x_1159_, 9);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; 
v_unused_1179_ = lean_ctor_get(v___x_1159_, 5);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v___x_1159_, 0);
lean_dec(v_unused_1180_);
v___x_1169_ = v___x_1159_;
v_isShared_1170_ = v_isSharedCheck_1178_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snapshotTasks_1167_);
lean_inc(v_infoState_1166_);
lean_inc(v_messages_1165_);
lean_inc(v_recordedDeps_1164_);
lean_inc(v_traceState_1163_);
lean_inc(v_auxDeclNGen_1162_);
lean_inc(v_ngen_1161_);
lean_inc(v_nextMacroScope_1160_);
lean_dec(v___x_1159_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1178_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1171_ = lean_box(0);
v___x_1172_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 5, v___x_1172_);
lean_ctor_set(v___x_1169_, 0, v_env_1156_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_env_1156_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_nextMacroScope_1160_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_ngen_1161_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_auxDeclNGen_1162_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_traceState_1163_);
lean_ctor_set(v_reuseFailAlloc_1177_, 5, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1177_, 6, v_recordedDeps_1164_);
lean_ctor_set(v_reuseFailAlloc_1177_, 7, v_messages_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 8, v_infoState_1166_);
lean_ctor_set(v_reuseFailAlloc_1177_, 9, v_snapshotTasks_1167_);
v___x_1174_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_st_ref_put(v___y_1157_, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1171_);
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___boxed(lean_object* v_env_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1181_, v___y_1182_);
lean_dec(v___y_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(lean_object* v_env_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1185_, v___y_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(lean_object* v_env_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_env_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(size_t v_sz_1203_, size_t v_i_1204_, lean_object* v_bs_1205_, uint8_t v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
uint8_t v___x_1213_; 
v___x_1213_ = lean_usize_dec_lt(v_i_1204_, v_sz_1203_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_bs_1205_);
return v___x_1214_;
}
else
{
uint8_t v___x_1215_; lean_object* v_v_1216_; lean_object* v___x_1217_; lean_object* v_bs_x27_1218_; lean_object* v___x_1219_; 
v___x_1215_ = 0;
v_v_1216_ = lean_array_uget(v_bs_1205_, v_i_1204_);
v___x_1217_ = lean_unsigned_to_nat(0u);
v_bs_x27_1218_ = lean_array_uset(v_bs_1205_, v_i_1204_, v___x_1217_);
v___x_1219_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_1215_, v_v_1216_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v___x_1221_ = ((size_t)1ULL);
v___x_1222_ = lean_usize_add(v_i_1204_, v___x_1221_);
v___x_1223_ = lean_array_uset(v_bs_x27_1218_, v_i_1204_, v_a_1220_);
v_i_1204_ = v___x_1222_;
v_bs_1205_ = v___x_1223_;
goto _start;
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v_bs_x27_1218_);
v_a_1225_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1219_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1219_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(lean_object* v_sz_1233_, lean_object* v_i_1234_, lean_object* v_bs_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
size_t v_sz_boxed_1243_; size_t v_i_boxed_1244_; uint8_t v___y_8191__boxed_1245_; lean_object* v_res_1246_; 
v_sz_boxed_1243_ = lean_unbox_usize(v_sz_1233_);
lean_dec(v_sz_1233_);
v_i_boxed_1244_ = lean_unbox_usize(v_i_1234_);
lean_dec(v_i_1234_);
v___y_8191__boxed_1245_ = lean_unbox(v___y_1236_);
v_res_1246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_boxed_1243_, v_i_boxed_1244_, v_bs_1235_, v___y_8191__boxed_1245_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
return v_res_1246_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_unsigned_to_nat(16u);
v___x_1251_ = lean_mk_array(v___x_1250_, v___x_1249_);
return v___x_1251_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1);
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v___x_1252_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3(void){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default___redArg();
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(lean_object* v_decl_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_type_1272_; lean_object* v_value_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_type_1272_ = lean_ctor_get(v_decl_1264_, 2);
lean_inc_ref(v_type_1272_);
v_value_1273_ = lean_ctor_get(v_decl_1264_, 3);
v___x_1274_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0));
v___x_1275_ = lean_st_mk_ref(v___x_1274_);
v___x_1276_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_1273_, v___x_1275_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v_a_1286_; lean_object* v___x_1368_; size_t v_sz_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
lean_dec_ref_known(v___x_1276_, 1);
v___x_1277_ = lean_st_ref_get(v___x_1275_);
lean_dec(v___x_1275_);
v___x_1278_ = l_Array_reverse___redArg(v___x_1277_);
v___x_1279_ = 0;
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v_decl_1264_);
v___x_1281_ = lean_array_push(v___x_1278_, v___x_1280_);
v___x_1282_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_1283_ = 0;
v___x_1284_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3);
v___x_1368_ = lean_st_mk_ref(v___x_1282_);
v_sz_1369_ = lean_array_size(v___x_1281_);
v___x_1370_ = ((size_t)0ULL);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_1369_, v___x_1370_, v___x_1281_, v___x_1283_, v___x_1368_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1373_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = lean_st_ref_get(v___x_1368_);
lean_dec(v___x_1368_);
lean_dec(v___x_1373_);
v_a_1286_ = v_a_1372_;
goto v___jp_1285_;
}
else
{
lean_dec(v___x_1368_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1374_; 
v_a_1374_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1371_, 1);
v_a_1286_ = v_a_1374_;
goto v___jp_1285_;
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec_ref(v_type_1272_);
v_a_1375_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1371_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1371_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
v___jp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v_env_1297_; lean_object* v___x_1298_; 
v___x_1287_ = lean_array_get_size(v_a_1286_);
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_nat_sub(v___x_1287_, v___x_1288_);
v___x_1290_ = lean_array_get_borrowed(v___x_1284_, v_a_1286_, v___x_1289_);
lean_dec(v___x_1289_);
v___x_1291_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1290_);
v___x_1292_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
v___x_1293_ = l_Lean_Compiler_LCNF_attachCodeDecls___redArg(v_a_1286_, v___x_1292_);
lean_dec_ref(v_a_1286_);
v___x_1294_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4));
lean_inc_ref(v___x_1293_);
v___x_1295_ = l_Lean_Compiler_LCNF_Code_toExpr(v___x_1279_, v___x_1293_, v___x_1294_);
v___x_1296_ = lean_st_ref_get(v_a_1270_);
v_env_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc_ref_n(v_env_1297_, 2);
lean_dec(v___x_1296_);
v___x_1298_ = l_Lean_getClosedTermName_x3f(v_env_1297_, v___x_1295_);
if (lean_obj_tag(v___x_1298_) == 1)
{
lean_object* v_val_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v_env_1297_);
lean_dec_ref(v___x_1295_);
lean_dec_ref(v_type_1272_);
v_val_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1300_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1279_, v___x_1293_, v_a_1268_);
lean_dec_ref(v___x_1293_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1307_ == 0)
{
lean_object* v_unused_1308_; 
v_unused_1308_ = lean_ctor_get(v___x_1300_, 0);
lean_dec(v_unused_1308_);
v___x_1302_ = v___x_1300_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_dec(v___x_1300_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v_val_1299_);
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_val_1299_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_val_1299_);
v_a_1309_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1300_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1300_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v___x_1317_; lean_object* v_baseName_1318_; lean_object* v_decls_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v___x_1298_);
v___x_1317_ = lean_st_ref_get(v_a_1266_);
v_baseName_1318_ = lean_ctor_get(v_a_1265_, 0);
v_decls_1319_ = lean_ctor_get(v___x_1317_, 0);
lean_inc_ref(v_decls_1319_);
lean_dec(v___x_1317_);
v___x_1320_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6));
v___x_1321_ = lean_array_get_size(v_decls_1319_);
lean_dec_ref(v_decls_1319_);
v___x_1322_ = lean_name_append_index_after(v___x_1320_, v___x_1321_);
lean_inc(v_baseName_1318_);
v___x_1323_ = l_Lean_Name_append(v_baseName_1318_, v___x_1322_);
lean_inc(v___x_1323_);
v___x_1324_ = l_Lean_cacheClosedTermName(v_env_1297_, v___x_1295_, v___x_1323_);
v___x_1325_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v___x_1324_, v_a_1270_);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v___x_1325_, 0);
lean_dec(v_unused_1367_);
v___x_1327_ = v___x_1325_;
v_isShared_1328_ = v_isSharedCheck_1366_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v___x_1325_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1366_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1329_ = lean_box(0);
v___x_1330_ = 1;
lean_inc(v___x_1323_);
v___x_1331_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1331_, 0, v___x_1323_);
lean_ctor_set(v___x_1331_, 1, v___x_1329_);
lean_ctor_set(v___x_1331_, 2, v_type_1272_);
lean_ctor_set(v___x_1331_, 3, v___x_1294_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*4, v___x_1330_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1293_);
v___x_1333_ = v___x_1327_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1293_);
v___x_1333_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7));
v___x_1335_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1335_, 0, v___x_1331_);
lean_ctor_set(v___x_1335_, 1, v___x_1333_);
lean_ctor_set(v___x_1335_, 2, v___x_1334_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*3, v___x_1283_);
lean_inc_ref(v___x_1335_);
v___x_1336_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1335_, v_a_1270_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1355_; 
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; 
v_unused_1356_ = lean_ctor_get(v___x_1336_, 0);
lean_dec(v_unused_1356_);
v___x_1338_ = v___x_1336_;
v_isShared_1339_ = v_isSharedCheck_1355_;
goto v_resetjp_1337_;
}
else
{
lean_dec(v___x_1336_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1355_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v_decls_1341_; lean_object* v_fvarDecisionCache_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1354_; 
v___x_1340_ = lean_st_ref_take(v_a_1266_);
v_decls_1341_ = lean_ctor_get(v___x_1340_, 0);
v_fvarDecisionCache_1342_ = lean_ctor_get(v___x_1340_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1344_ = v___x_1340_;
v_isShared_1345_ = v_isSharedCheck_1354_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_fvarDecisionCache_1342_);
lean_inc(v_decls_1341_);
lean_dec(v___x_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1354_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_array_push(v_decls_1341_, v___x_1335_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1346_);
v___x_1348_ = v___x_1344_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_fvarDecisionCache_1342_);
v___x_1348_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_st_ref_put(v_a_1266_, v___x_1348_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 0, v___x_1323_);
v___x_1351_ = v___x_1338_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1323_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref_known(v___x_1335_, 3);
lean_dec(v___x_1323_);
v_a_1357_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1336_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1336_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
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
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec(v___x_1275_);
lean_dec_ref(v_type_1272_);
lean_dec_ref(v_decl_1264_);
v_a_1383_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1276_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1276_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___boxed(lean_object* v_decl_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
return v_res_1399_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(lean_object* v_msg_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0);
v___x_1403_ = lean_panic_fn_borrowed(v___x_1402_, v_msg_1401_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1407_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2));
v___x_1408_ = lean_unsigned_to_nat(9u);
v___x_1409_ = lean_unsigned_to_nat(650u);
v___x_1410_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1));
v___x_1411_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0));
v___x_1412_ = l_mkPanicMessageWithDecl(v___x_1411_, v___x_1410_, v___x_1409_, v___x_1408_, v___x_1407_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* v_code_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v_decl_1424_; lean_object* v_k_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; 
switch(lean_obj_tag(v_code_1415_))
{
case 0:
{
lean_object* v_decl_1539_; lean_object* v_k_1540_; lean_object* v_value_1541_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; 
v_decl_1539_ = lean_ctor_get(v_code_1415_, 0);
v_k_1540_ = lean_ctor_get(v_code_1415_, 1);
v_value_1541_ = lean_ctor_get(v_decl_1539_, 3);
lean_inc(v_value_1541_);
if (lean_obj_tag(v_value_1541_) == 3)
{
lean_object* v_declName_1738_; 
v_declName_1738_ = lean_ctor_get(v_value_1541_, 0);
if (lean_obj_tag(v_declName_1738_) == 1)
{
lean_object* v_pre_1739_; 
v_pre_1739_ = lean_ctor_get(v_declName_1738_, 0);
if (lean_obj_tag(v_pre_1739_) == 1)
{
lean_object* v_pre_1740_; 
v_pre_1740_ = lean_ctor_get(v_pre_1739_, 0);
if (lean_obj_tag(v_pre_1740_) == 0)
{
lean_object* v_args_1741_; lean_object* v_str_1742_; lean_object* v_str_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v_sizeId_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; 
v_args_1741_ = lean_ctor_get(v_value_1541_, 2);
v_str_1742_ = lean_ctor_get(v_declName_1738_, 1);
v_str_1743_ = lean_ctor_get(v_pre_1739_, 1);
v___x_1744_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1745_ = lean_string_dec_eq(v_str_1743_, v___x_1744_);
if (v___x_1745_ == 0)
{
v___y_1543_ = v_a_1416_;
v___y_1544_ = v_a_1417_;
v___y_1545_ = v_a_1418_;
v___y_1546_ = v_a_1419_;
v___y_1547_ = v_a_1420_;
v___y_1548_ = v_a_1421_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_2084_ = lean_string_dec_eq(v_str_1742_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_2086_ = lean_string_dec_eq(v_str_1742_, v___x_2085_);
if (v___x_2086_ == 0)
{
v___y_1543_ = v_a_1416_;
v___y_1544_ = v_a_1417_;
v___y_1545_ = v_a_1418_;
v___y_1546_ = v_a_1419_;
v___y_1547_ = v_a_1420_;
v___y_1548_ = v_a_1421_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2087_ = lean_array_get_size(v_args_1741_);
v___x_2088_ = lean_unsigned_to_nat(2u);
v___x_2089_ = lean_nat_dec_eq(v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
v___y_1543_ = v_a_1416_;
v___y_1544_ = v_a_1417_;
v___y_1545_ = v_a_1418_;
v___y_1546_ = v_a_1419_;
v___y_1547_ = v_a_1420_;
v___y_1548_ = v_a_1421_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = lean_unsigned_to_nat(1u);
v___x_2091_ = lean_array_fget_borrowed(v_args_1741_, v___x_2090_);
if (lean_obj_tag(v___x_2091_) == 1)
{
lean_object* v_fvarId_2092_; 
v_fvarId_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_fvarId_2092_);
v_sizeId_1951_ = v_fvarId_2092_;
v___y_1952_ = v_a_1416_;
v___y_1953_ = v_a_1417_;
v___y_1954_ = v_a_1418_;
v___y_1955_ = v_a_1419_;
v___y_1956_ = v_a_1420_;
v___y_1957_ = v_a_1421_;
goto v___jp_1950_;
}
else
{
v___y_1543_ = v_a_1416_;
v___y_1544_ = v_a_1417_;
v___y_1545_ = v_a_1418_;
v___y_1546_ = v_a_1419_;
v___y_1547_ = v_a_1420_;
v___y_1548_ = v_a_1421_;
goto v___jp_1542_;
}
}
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2093_ = lean_array_get_size(v_args_1741_);
v___x_2094_ = lean_unsigned_to_nat(2u);
v___x_2095_ = lean_nat_dec_eq(v___x_2093_, v___x_2094_);
if (v___x_2095_ == 0)
{
v___y_1543_ = v_a_1416_;
v___y_1544_ = v_a_1417_;
v___y_1545_ = v_a_1418_;
v___y_1546_ = v_a_1419_;
v___y_1547_ = v_a_1420_;
v___y_1548_ = v_a_1421_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_unsigned_to_nat(1u);
v___x_2097_ = lean_array_fget_borrowed(v_args_1741_, v___x_2096_);
if (lean_obj_tag(v___x_2097_) == 1)
{
lean_object* v_fvarId_2098_; 
v_fvarId_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_fvarId_2098_);
v_sizeId_1951_ = v_fvarId_2098_;
v___y_1952_ = v_a_1416_;
v___y_1953_ = v_a_1417_;
v___y_1954_ = v_a_1418_;
v___y_1955_ = v_a_1419_;
v___y_1956_ = v_a_1420_;
v___y_1957_ = v_a_1421_;
goto v___jp_1950_;
}
else
{
v___y_1543_ = v_a_1416_;
v___y_1544_ = v_a_1417_;
v___y_1545_ = v_a_1418_;
v___y_1546_ = v_a_1419_;
v___y_1547_ = v_a_1420_;
v___y_1548_ = v_a_1421_;
goto v___jp_1542_;
}
}
}
}
v___jp_1746_:
{
lean_object* v___x_1753_; 
lean_inc_ref(v_k_1540_);
lean_inc_ref(v_decl_1539_);
v___x_1753_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1539_, v_k_1540_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
if (lean_obj_tag(v_a_1754_) == 1)
{
lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1826_; 
v_isSharedCheck_1826_ = !lean_is_exclusive(v_value_1541_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; lean_object* v_unused_1828_; lean_object* v_unused_1829_; 
v_unused_1827_ = lean_ctor_get(v_value_1541_, 2);
lean_dec(v_unused_1827_);
v_unused_1828_ = lean_ctor_get(v_value_1541_, 1);
lean_dec(v_unused_1828_);
v_unused_1829_ = lean_ctor_get(v_value_1541_, 0);
lean_dec(v_unused_1829_);
v___x_1756_ = v_value_1541_;
v_isShared_1757_ = v_isSharedCheck_1826_;
goto v_resetjp_1755_;
}
else
{
lean_dec(v_value_1541_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1826_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_val_1758_; lean_object* v_fst_1759_; lean_object* v_snd_1760_; lean_object* v___x_1761_; 
v_val_1758_ = lean_ctor_get(v_a_1754_, 0);
lean_inc(v_val_1758_);
lean_dec_ref_known(v_a_1754_, 1);
v_fst_1759_ = lean_ctor_get(v_val_1758_, 0);
lean_inc_n(v_fst_1759_, 2);
v_snd_1760_ = lean_ctor_get(v_val_1758_, 1);
lean_inc(v_snd_1760_);
lean_dec(v_val_1758_);
v___x_1761_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1759_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; uint8_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = 0;
v___x_1764_ = lean_box(0);
v___x_1765_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 2, v___x_1765_);
lean_ctor_set(v___x_1756_, 1, v___x_1764_);
lean_ctor_set(v___x_1756_, 0, v_a_1762_);
v___x_1767_ = v___x_1756_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1762_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1763_, v_fst_1759_, v___x_1767_, v___y_1750_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1770_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1760_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1808_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1808_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1808_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
size_t v___x_1775_; size_t v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_ptr_addr(v_k_1540_);
v___x_1776_ = lean_ptr_addr(v_a_1771_);
v___x_1777_ = lean_usize_dec_eq(v___x_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1787_; 
v_isSharedCheck_1787_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; lean_object* v_unused_1789_; 
v_unused_1788_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1788_);
v_unused_1789_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1789_);
v___x_1779_ = v_code_1415_;
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
else
{
lean_dec(v_code_1415_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 1, v_a_1771_);
lean_ctor_set(v___x_1779_, 0, v_a_1769_);
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1769_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_a_1771_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1782_);
v___x_1784_ = v___x_1773_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
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
size_t v___x_1790_; size_t v___x_1791_; uint8_t v___x_1792_; 
v___x_1790_ = lean_ptr_addr(v_decl_1539_);
v___x_1791_ = lean_ptr_addr(v_a_1769_);
v___x_1792_ = lean_usize_dec_eq(v___x_1790_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1802_; 
v_isSharedCheck_1802_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; lean_object* v_unused_1804_; 
v_unused_1803_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1804_);
v___x_1794_ = v_code_1415_;
v_isShared_1795_ = v_isSharedCheck_1802_;
goto v_resetjp_1793_;
}
else
{
lean_dec(v_code_1415_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1802_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 1, v_a_1771_);
lean_ctor_set(v___x_1794_, 0, v_a_1769_);
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1769_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_a_1771_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1797_);
v___x_1799_ = v___x_1773_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v___x_1806_; 
lean_dec(v_a_1771_);
lean_dec(v_a_1769_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v_code_1415_);
v___x_1806_ = v___x_1773_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_code_1415_);
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
}
else
{
lean_dec(v_a_1769_);
lean_dec_ref_known(v_code_1415_, 2);
return v___x_1770_;
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_snd_1760_);
lean_dec_ref_known(v_code_1415_, 2);
v_a_1809_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1768_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1768_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
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
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_snd_1760_);
lean_dec(v_fst_1759_);
lean_del_object(v___x_1756_);
lean_dec_ref_known(v_code_1415_, 2);
v_a_1818_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1761_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1761_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
else
{
lean_object* v___x_1830_; 
lean_dec(v_a_1754_);
v___x_1830_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1745_, v_value_1541_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; uint8_t v___x_1832_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___x_1830_, 1);
v___x_1832_ = lean_unbox(v_a_1831_);
lean_dec(v_a_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; 
lean_inc_ref(v_k_1540_);
v___x_1833_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1540_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1870_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1870_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1870_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
size_t v___x_1838_; size_t v___x_1839_; uint8_t v___x_1840_; 
v___x_1838_ = lean_ptr_addr(v_k_1540_);
v___x_1839_ = lean_ptr_addr(v_a_1834_);
v___x_1840_ = lean_usize_dec_eq(v___x_1838_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1850_; 
lean_inc_ref(v_decl_1539_);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; lean_object* v_unused_1852_; 
v_unused_1851_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1852_);
v___x_1842_ = v_code_1415_;
v_isShared_1843_ = v_isSharedCheck_1850_;
goto v_resetjp_1841_;
}
else
{
lean_dec(v_code_1415_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1850_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 1, v_a_1834_);
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_decl_1539_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_a_1834_);
v___x_1845_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1845_);
v___x_1847_ = v___x_1836_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
size_t v___x_1853_; uint8_t v___x_1854_; 
v___x_1853_ = lean_ptr_addr(v_decl_1539_);
v___x_1854_ = lean_usize_dec_eq(v___x_1853_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1864_; 
lean_inc_ref(v_decl_1539_);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; lean_object* v_unused_1866_; 
v_unused_1865_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1866_);
v___x_1856_ = v_code_1415_;
v_isShared_1857_ = v_isSharedCheck_1864_;
goto v_resetjp_1855_;
}
else
{
lean_dec(v_code_1415_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1864_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 1, v_a_1834_);
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_decl_1539_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_a_1834_);
v___x_1859_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1861_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1859_);
v___x_1861_ = v___x_1836_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_object* v___x_1868_; 
lean_dec(v_a_1834_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v_code_1415_);
v___x_1868_ = v___x_1836_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_code_1415_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1415_, 2);
return v___x_1833_;
}
}
else
{
lean_object* v___x_1871_; 
lean_inc_ref(v_decl_1539_);
v___x_1871_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1539_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; uint8_t v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = 0;
v___x_1874_ = lean_box(0);
v___x_1875_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1876_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1876_, 0, v_a_1872_);
lean_ctor_set(v___x_1876_, 1, v___x_1874_);
lean_ctor_set(v___x_1876_, 2, v___x_1875_);
lean_inc_ref(v_decl_1539_);
v___x_1877_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1873_, v_decl_1539_, v___x_1876_, v___y_1750_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
lean_inc_ref(v_k_1540_);
v___x_1879_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1540_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1917_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1917_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1917_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
size_t v___x_1884_; size_t v___x_1885_; uint8_t v___x_1886_; 
v___x_1884_ = lean_ptr_addr(v_k_1540_);
v___x_1885_ = lean_ptr_addr(v_a_1880_);
v___x_1886_ = lean_usize_dec_eq(v___x_1884_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1896_; 
v_isSharedCheck_1896_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; lean_object* v_unused_1898_; 
v_unused_1897_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1897_);
v_unused_1898_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1898_);
v___x_1888_ = v_code_1415_;
v_isShared_1889_ = v_isSharedCheck_1896_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v_code_1415_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1896_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v_a_1880_);
lean_ctor_set(v___x_1888_, 0, v_a_1878_);
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1878_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_a_1880_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1893_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1891_);
v___x_1893_ = v___x_1882_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
size_t v___x_1899_; size_t v___x_1900_; uint8_t v___x_1901_; 
v___x_1899_ = lean_ptr_addr(v_decl_1539_);
v___x_1900_ = lean_ptr_addr(v_a_1878_);
v___x_1901_ = lean_usize_dec_eq(v___x_1899_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1911_; 
v_isSharedCheck_1911_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; lean_object* v_unused_1913_; 
v_unused_1912_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1912_);
v_unused_1913_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1913_);
v___x_1903_ = v_code_1415_;
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
else
{
lean_dec(v_code_1415_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1911_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 1, v_a_1880_);
lean_ctor_set(v___x_1903_, 0, v_a_1878_);
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1878_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_a_1880_);
v___x_1906_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1906_);
v___x_1908_ = v___x_1882_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
else
{
lean_object* v___x_1915_; 
lean_dec(v_a_1880_);
lean_dec(v_a_1878_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v_code_1415_);
v___x_1915_ = v___x_1882_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_code_1415_);
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
}
else
{
lean_dec(v_a_1878_);
lean_dec_ref_known(v_code_1415_, 2);
return v___x_1879_;
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec_ref_known(v_code_1415_, 2);
v_a_1918_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1877_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1877_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
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
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref_known(v_code_1415_, 2);
v_a_1926_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1871_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1871_);
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
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref_known(v_code_1415_, 2);
v_a_1934_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1830_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1830_);
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
lean_dec_ref_known(v_value_1541_, 3);
lean_dec_ref_known(v_code_1415_, 2);
v_a_1942_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1753_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1753_);
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
v___jp_1950_:
{
uint8_t v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = 0;
v___x_1959_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1958_, v_sizeId_1951_, v___y_1955_);
lean_dec(v_sizeId_1951_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
if (lean_obj_tag(v_a_1960_) == 1)
{
lean_object* v_val_1961_; 
v_val_1961_ = lean_ctor_get(v_a_1960_, 0);
lean_inc(v_val_1961_);
lean_dec_ref_known(v_a_1960_, 1);
if (lean_obj_tag(v_val_1961_) == 0)
{
lean_object* v_value_1962_; 
v_value_1962_ = lean_ctor_get(v_val_1961_, 0);
lean_inc_ref(v_value_1962_);
lean_dec_ref_known(v_val_1961_, 1);
if (lean_obj_tag(v_value_1962_) == 0)
{
lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2071_; 
v_isSharedCheck_2071_ = !lean_is_exclusive(v_value_1541_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; lean_object* v_unused_2073_; lean_object* v_unused_2074_; 
v_unused_2072_ = lean_ctor_get(v_value_1541_, 2);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v_value_1541_, 1);
lean_dec(v_unused_2073_);
v_unused_2074_ = lean_ctor_get(v_value_1541_, 0);
lean_dec(v_unused_2074_);
v___x_1964_ = v_value_1541_;
v_isShared_1965_ = v_isSharedCheck_2071_;
goto v_resetjp_1963_;
}
else
{
lean_dec(v_value_1541_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2071_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v_val_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_val_1966_ = lean_ctor_get(v_value_1962_, 0);
lean_inc(v_val_1966_);
lean_dec_ref_known(v_value_1962_, 1);
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = lean_nat_dec_eq(v_val_1966_, v___x_1967_);
lean_dec(v_val_1966_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
lean_del_object(v___x_1964_);
lean_inc_ref(v_k_1540_);
v___x_1969_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1540_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2006_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2006_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2006_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
size_t v___x_1974_; size_t v___x_1975_; uint8_t v___x_1976_; 
v___x_1974_ = lean_ptr_addr(v_k_1540_);
v___x_1975_ = lean_ptr_addr(v_a_1970_);
v___x_1976_ = lean_usize_dec_eq(v___x_1974_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1986_; 
lean_inc_ref(v_decl_1539_);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1987_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1988_);
v___x_1978_ = v_code_1415_;
v_isShared_1979_ = v_isSharedCheck_1986_;
goto v_resetjp_1977_;
}
else
{
lean_dec(v_code_1415_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1986_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 1, v_a_1970_);
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_decl_1539_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_a_1970_);
v___x_1981_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1983_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1981_);
v___x_1983_ = v___x_1972_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
size_t v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = lean_ptr_addr(v_decl_1539_);
v___x_1990_ = lean_usize_dec_eq(v___x_1989_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2000_; 
lean_inc_ref(v_decl_1539_);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; lean_object* v_unused_2002_; 
v_unused_2001_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_2001_);
v_unused_2002_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_2002_);
v___x_1992_ = v_code_1415_;
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
else
{
lean_dec(v_code_1415_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v_a_1970_);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_decl_1539_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_a_1970_);
v___x_1995_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1997_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1995_);
v___x_1997_ = v___x_1972_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v___x_2004_; 
lean_dec(v_a_1970_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_code_1415_);
v___x_2004_ = v___x_1972_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_code_1415_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1415_, 2);
return v___x_1969_;
}
}
else
{
lean_object* v___x_2007_; 
lean_inc_ref(v_decl_1539_);
v___x_2007_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1539_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2012_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = lean_box(0);
v___x_2010_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 2, v___x_2010_);
lean_ctor_set(v___x_1964_, 1, v___x_2009_);
lean_ctor_set(v___x_1964_, 0, v_a_2008_);
v___x_2012_ = v___x_1964_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2008_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; 
lean_inc_ref(v_decl_1539_);
v___x_2013_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1958_, v_decl_1539_, v___x_2012_, v___y_1955_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
lean_inc_ref(v_k_1540_);
v___x_2015_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1540_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2053_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2053_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2053_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
size_t v___x_2020_; size_t v___x_2021_; uint8_t v___x_2022_; 
v___x_2020_ = lean_ptr_addr(v_k_1540_);
v___x_2021_ = lean_ptr_addr(v_a_2016_);
v___x_2022_ = lean_usize_dec_eq(v___x_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2032_; 
v_isSharedCheck_2032_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; lean_object* v_unused_2034_; 
v_unused_2033_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_2034_);
v___x_2024_ = v_code_1415_;
v_isShared_2025_ = v_isSharedCheck_2032_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v_code_1415_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2032_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 1, v_a_2016_);
lean_ctor_set(v___x_2024_, 0, v_a_2014_);
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2014_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_a_2016_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2027_);
v___x_2029_ = v___x_2018_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
size_t v___x_2035_; size_t v___x_2036_; uint8_t v___x_2037_; 
v___x_2035_ = lean_ptr_addr(v_decl_1539_);
v___x_2036_ = lean_ptr_addr(v_a_2014_);
v___x_2037_ = lean_usize_dec_eq(v___x_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2047_; 
v_isSharedCheck_2047_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; lean_object* v_unused_2049_; 
v_unused_2048_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_2049_);
v___x_2039_ = v_code_1415_;
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
else
{
lean_dec(v_code_1415_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2047_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 1, v_a_2016_);
lean_ctor_set(v___x_2039_, 0, v_a_2014_);
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2014_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_a_2016_);
v___x_2042_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2044_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2042_);
v___x_2044_ = v___x_2018_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v___x_2051_; 
lean_dec(v_a_2016_);
lean_dec(v_a_2014_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v_code_1415_);
v___x_2051_ = v___x_2018_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_code_1415_);
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
}
else
{
lean_dec(v_a_2014_);
lean_dec_ref_known(v_code_1415_, 2);
return v___x_2015_;
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec_ref_known(v_code_1415_, 2);
v_a_2054_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2013_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2013_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
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
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_del_object(v___x_1964_);
lean_dec_ref_known(v_code_1415_, 2);
v_a_2063_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2007_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2007_);
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
}
else
{
lean_dec_ref(v_value_1962_);
v___y_1747_ = v___y_1952_;
v___y_1748_ = v___y_1953_;
v___y_1749_ = v___y_1954_;
v___y_1750_ = v___y_1955_;
v___y_1751_ = v___y_1956_;
v___y_1752_ = v___y_1957_;
goto v___jp_1746_;
}
}
else
{
lean_dec(v_val_1961_);
v___y_1747_ = v___y_1952_;
v___y_1748_ = v___y_1953_;
v___y_1749_ = v___y_1954_;
v___y_1750_ = v___y_1955_;
v___y_1751_ = v___y_1956_;
v___y_1752_ = v___y_1957_;
goto v___jp_1746_;
}
}
else
{
lean_dec(v_a_1960_);
v___y_1747_ = v___y_1952_;
v___y_1748_ = v___y_1953_;
v___y_1749_ = v___y_1954_;
v___y_1750_ = v___y_1955_;
v___y_1751_ = v___y_1956_;
v___y_1752_ = v___y_1957_;
goto v___jp_1746_;
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec_ref_known(v_value_1541_, 3);
lean_dec_ref_known(v_code_1415_, 2);
v_a_2075_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_1959_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_1959_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
else
{
v___y_1543_ = v_a_1416_;
v___y_1544_ = v_a_1417_;
v___y_1545_ = v_a_1418_;
v___y_1546_ = v_a_1419_;
v___y_1547_ = v_a_1420_;
v___y_1548_ = v_a_1421_;
goto v___jp_1542_;
}
}
else
{
v___y_1543_ = v_a_1416_;
v___y_1544_ = v_a_1417_;
v___y_1545_ = v_a_1418_;
v___y_1546_ = v_a_1419_;
v___y_1547_ = v_a_1420_;
v___y_1548_ = v_a_1421_;
goto v___jp_1542_;
}
}
else
{
v___y_1543_ = v_a_1416_;
v___y_1544_ = v_a_1417_;
v___y_1545_ = v_a_1418_;
v___y_1546_ = v_a_1419_;
v___y_1547_ = v_a_1420_;
v___y_1548_ = v_a_1421_;
goto v___jp_1542_;
}
}
else
{
v___y_1543_ = v_a_1416_;
v___y_1544_ = v_a_1417_;
v___y_1545_ = v_a_1418_;
v___y_1546_ = v_a_1419_;
v___y_1547_ = v_a_1420_;
v___y_1548_ = v_a_1421_;
goto v___jp_1542_;
}
v___jp_1542_:
{
lean_object* v___x_1549_; 
lean_inc_ref(v_k_1540_);
lean_inc_ref(v_decl_1539_);
v___x_1549_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1539_, v_k_1540_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
if (lean_obj_tag(v_a_1550_) == 1)
{
lean_object* v_val_1551_; lean_object* v_fst_1552_; lean_object* v_snd_1553_; lean_object* v___x_1554_; 
lean_dec(v_value_1541_);
v_val_1551_ = lean_ctor_get(v_a_1550_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v_a_1550_, 1);
v_fst_1552_ = lean_ctor_get(v_val_1551_, 0);
lean_inc_n(v_fst_1552_, 2);
v_snd_1553_ = lean_ctor_get(v_val_1551_, 1);
lean_inc(v_snd_1553_);
lean_dec(v_val_1551_);
v___x_1554_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1552_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; uint8_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = 0;
v___x_1557_ = lean_box(0);
v___x_1558_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1559_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1559_, 0, v_a_1555_);
lean_ctor_set(v___x_1559_, 1, v___x_1557_);
lean_ctor_set(v___x_1559_, 2, v___x_1558_);
v___x_1560_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1556_, v_fst_1552_, v___x_1559_, v___y_1546_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1553_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1600_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1565_ = v___x_1562_;
v_isShared_1566_ = v_isSharedCheck_1600_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1562_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1600_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
size_t v___x_1567_; size_t v___x_1568_; uint8_t v___x_1569_; 
v___x_1567_ = lean_ptr_addr(v_k_1540_);
v___x_1568_ = lean_ptr_addr(v_a_1563_);
v___x_1569_ = lean_usize_dec_eq(v___x_1567_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1579_; 
v_isSharedCheck_1579_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; lean_object* v_unused_1581_; 
v_unused_1580_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1581_);
v___x_1571_ = v_code_1415_;
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
else
{
lean_dec(v_code_1415_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1579_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 1, v_a_1563_);
lean_ctor_set(v___x_1571_, 0, v_a_1561_);
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1561_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_a_1563_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1574_);
v___x_1576_ = v___x_1565_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
size_t v___x_1582_; size_t v___x_1583_; uint8_t v___x_1584_; 
v___x_1582_ = lean_ptr_addr(v_decl_1539_);
v___x_1583_ = lean_ptr_addr(v_a_1561_);
v___x_1584_ = lean_usize_dec_eq(v___x_1582_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1594_; 
v_isSharedCheck_1594_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; lean_object* v_unused_1596_; 
v_unused_1595_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1596_);
v___x_1586_ = v_code_1415_;
v_isShared_1587_ = v_isSharedCheck_1594_;
goto v_resetjp_1585_;
}
else
{
lean_dec(v_code_1415_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1594_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 1, v_a_1563_);
lean_ctor_set(v___x_1586_, 0, v_a_1561_);
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1561_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_a_1563_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1589_);
v___x_1591_ = v___x_1565_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
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
lean_object* v___x_1598_; 
lean_dec(v_a_1563_);
lean_dec(v_a_1561_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v_code_1415_);
v___x_1598_ = v___x_1565_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_code_1415_);
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
else
{
lean_dec(v_a_1561_);
lean_dec_ref_known(v_code_1415_, 2);
return v___x_1562_;
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_snd_1553_);
lean_dec_ref_known(v_code_1415_, 2);
v_a_1601_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1560_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1560_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
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
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v_snd_1553_);
lean_dec(v_fst_1552_);
lean_dec_ref_known(v_code_1415_, 2);
v_a_1609_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1554_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1554_);
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
uint8_t v___x_1617_; lean_object* v___x_1618_; 
lean_dec(v_a_1550_);
v___x_1617_ = 1;
v___x_1618_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1617_, v_value_1541_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; uint8_t v___x_1620_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = lean_unbox(v_a_1619_);
lean_dec(v_a_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_inc_ref(v_k_1540_);
v___x_1621_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1540_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1658_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1658_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1658_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
size_t v___x_1626_; size_t v___x_1627_; uint8_t v___x_1628_; 
v___x_1626_ = lean_ptr_addr(v_k_1540_);
v___x_1627_ = lean_ptr_addr(v_a_1622_);
v___x_1628_ = lean_usize_dec_eq(v___x_1626_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1638_; 
lean_inc_ref(v_decl_1539_);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; lean_object* v_unused_1640_; 
v_unused_1639_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1640_);
v___x_1630_ = v_code_1415_;
v_isShared_1631_ = v_isSharedCheck_1638_;
goto v_resetjp_1629_;
}
else
{
lean_dec(v_code_1415_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1638_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v_a_1622_);
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_decl_1539_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_a_1622_);
v___x_1633_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1633_);
v___x_1635_ = v___x_1624_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
size_t v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = lean_ptr_addr(v_decl_1539_);
v___x_1642_ = lean_usize_dec_eq(v___x_1641_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1652_; 
lean_inc_ref(v_decl_1539_);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; lean_object* v_unused_1654_; 
v_unused_1653_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1654_);
v___x_1644_ = v_code_1415_;
v_isShared_1645_ = v_isSharedCheck_1652_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v_code_1415_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1652_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 1, v_a_1622_);
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_decl_1539_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_a_1622_);
v___x_1647_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1647_);
v___x_1649_ = v___x_1624_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
else
{
lean_object* v___x_1656_; 
lean_dec(v_a_1622_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v_code_1415_);
v___x_1656_ = v___x_1624_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_code_1415_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1415_, 2);
return v___x_1621_;
}
}
else
{
lean_object* v___x_1659_; 
lean_inc_ref(v_decl_1539_);
v___x_1659_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1539_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1659_, 1);
v___x_1661_ = 0;
v___x_1662_ = lean_box(0);
v___x_1663_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1664_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1664_, 0, v_a_1660_);
lean_ctor_set(v___x_1664_, 1, v___x_1662_);
lean_ctor_set(v___x_1664_, 2, v___x_1663_);
lean_inc_ref(v_decl_1539_);
v___x_1665_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1661_, v_decl_1539_, v___x_1664_, v___y_1546_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
lean_inc_ref(v_k_1540_);
v___x_1667_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1540_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1705_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1705_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1705_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
size_t v___x_1672_; size_t v___x_1673_; uint8_t v___x_1674_; 
v___x_1672_ = lean_ptr_addr(v_k_1540_);
v___x_1673_ = lean_ptr_addr(v_a_1668_);
v___x_1674_ = lean_usize_dec_eq(v___x_1672_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1684_; 
v_isSharedCheck_1684_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; lean_object* v_unused_1686_; 
v_unused_1685_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1686_);
v___x_1676_ = v_code_1415_;
v_isShared_1677_ = v_isSharedCheck_1684_;
goto v_resetjp_1675_;
}
else
{
lean_dec(v_code_1415_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1684_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v_a_1668_);
lean_ctor_set(v___x_1676_, 0, v_a_1666_);
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1666_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_a_1668_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1679_);
v___x_1681_ = v___x_1670_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
size_t v___x_1687_; size_t v___x_1688_; uint8_t v___x_1689_; 
v___x_1687_ = lean_ptr_addr(v_decl_1539_);
v___x_1688_ = lean_ptr_addr(v_a_1666_);
v___x_1689_ = lean_usize_dec_eq(v___x_1687_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1699_; 
v_isSharedCheck_1699_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; lean_object* v_unused_1701_; 
v_unused_1700_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1701_);
v___x_1691_ = v_code_1415_;
v_isShared_1692_ = v_isSharedCheck_1699_;
goto v_resetjp_1690_;
}
else
{
lean_dec(v_code_1415_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1699_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 1, v_a_1668_);
lean_ctor_set(v___x_1691_, 0, v_a_1666_);
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1666_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_a_1668_);
v___x_1694_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1696_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1694_);
v___x_1696_ = v___x_1670_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
else
{
lean_object* v___x_1703_; 
lean_dec(v_a_1668_);
lean_dec(v_a_1666_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v_code_1415_);
v___x_1703_ = v___x_1670_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_code_1415_);
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
}
else
{
lean_dec(v_a_1666_);
lean_dec_ref_known(v_code_1415_, 2);
return v___x_1667_;
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref_known(v_code_1415_, 2);
v_a_1706_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1665_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1665_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
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
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref_known(v_code_1415_, 2);
v_a_1714_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1659_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1659_);
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
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_dec_ref_known(v_code_1415_, 2);
v_a_1722_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___x_1618_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1618_);
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
lean_dec(v_value_1541_);
lean_dec_ref_known(v_code_1415_, 2);
v_a_1730_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1549_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1549_);
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
case 1:
{
lean_object* v_decl_2099_; lean_object* v_k_2100_; 
v_decl_2099_ = lean_ctor_get(v_code_1415_, 0);
v_k_2100_ = lean_ctor_get(v_code_1415_, 1);
lean_inc_ref(v_k_2100_);
lean_inc_ref(v_decl_2099_);
v_decl_1424_ = v_decl_2099_;
v_k_1425_ = v_k_2100_;
v___y_1426_ = v_a_1416_;
v___y_1427_ = v_a_1417_;
v___y_1428_ = v_a_1418_;
v___y_1429_ = v_a_1419_;
v___y_1430_ = v_a_1420_;
v___y_1431_ = v_a_1421_;
goto v___jp_1423_;
}
case 2:
{
lean_object* v_decl_2101_; lean_object* v_k_2102_; 
v_decl_2101_ = lean_ctor_get(v_code_1415_, 0);
v_k_2102_ = lean_ctor_get(v_code_1415_, 1);
lean_inc_ref(v_k_2102_);
lean_inc_ref(v_decl_2101_);
v_decl_1424_ = v_decl_2101_;
v_k_1425_ = v_k_2102_;
v___y_1426_ = v_a_1416_;
v___y_1427_ = v_a_1417_;
v___y_1428_ = v_a_1418_;
v___y_1429_ = v_a_1419_;
v___y_1430_ = v_a_1420_;
v___y_1431_ = v_a_1421_;
goto v___jp_1423_;
}
case 4:
{
lean_object* v_cases_2103_; lean_object* v_typeName_2104_; lean_object* v_resultType_2105_; lean_object* v_discr_2106_; lean_object* v_alts_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2146_; 
v_cases_2103_ = lean_ctor_get(v_code_1415_, 0);
lean_inc_ref(v_cases_2103_);
v_typeName_2104_ = lean_ctor_get(v_cases_2103_, 0);
v_resultType_2105_ = lean_ctor_get(v_cases_2103_, 1);
v_discr_2106_ = lean_ctor_get(v_cases_2103_, 2);
v_alts_2107_ = lean_ctor_get(v_cases_2103_, 3);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_cases_2103_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2109_ = v_cases_2103_;
v_isShared_2110_ = v_isSharedCheck_2146_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_alts_2107_);
lean_inc(v_discr_2106_);
lean_inc(v_resultType_2105_);
lean_inc(v_typeName_2104_);
lean_dec(v_cases_2103_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2146_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2107_);
v___x_2112_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v___x_2111_, v_alts_2107_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2137_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2137_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2137_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
size_t v___x_2117_; size_t v___x_2118_; uint8_t v___x_2119_; 
v___x_2117_ = lean_ptr_addr(v_alts_2107_);
lean_dec_ref(v_alts_2107_);
v___x_2118_ = lean_ptr_addr(v_a_2113_);
v___x_2119_ = lean_usize_dec_eq(v___x_2117_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2132_; 
v_isSharedCheck_2132_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_2133_);
v___x_2121_ = v_code_1415_;
v_isShared_2122_ = v_isSharedCheck_2132_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v_code_1415_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2132_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 3, v_a_2113_);
v___x_2124_ = v___x_2109_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_typeName_2104_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_resultType_2105_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_discr_2106_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_a_2113_);
v___x_2124_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2126_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2124_);
v___x_2126_ = v___x_2121_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2126_);
v___x_2128_ = v___x_2115_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
else
{
lean_object* v___x_2135_; 
lean_dec(v_a_2113_);
lean_del_object(v___x_2109_);
lean_dec(v_discr_2106_);
lean_dec_ref(v_resultType_2105_);
lean_dec(v_typeName_2104_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v_code_1415_);
v___x_2135_ = v___x_2115_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_code_1415_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_del_object(v___x_2109_);
lean_dec_ref(v_alts_2107_);
lean_dec(v_discr_2106_);
lean_dec_ref(v_resultType_2105_);
lean_dec(v_typeName_2104_);
lean_dec_ref_known(v_code_1415_, 1);
v_a_2138_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2112_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2112_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
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
}
default: 
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v_code_1415_);
return v___x_2147_;
}
}
v___jp_1423_:
{
lean_object* v_params_1432_; lean_object* v_type_1433_; lean_object* v_value_1434_; uint8_t v___x_1435_; lean_object* v___x_1436_; 
v_params_1432_ = lean_ctor_get(v_decl_1424_, 2);
lean_inc_ref(v_params_1432_);
v_type_1433_ = lean_ctor_get(v_decl_1424_, 3);
lean_inc_ref(v_type_1433_);
v_value_1434_ = lean_ctor_get(v_decl_1424_, 4);
v___x_1435_ = 0;
lean_inc_ref(v_value_1434_);
v___x_1436_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_value_1434_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1438_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref_known(v___x_1436_, 1);
v___x_1438_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1435_, v_decl_1424_, v_type_1433_, v_params_1432_, v_a_1437_, v___y_1429_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1440_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
v___x_1440_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
if (lean_obj_tag(v___x_1440_) == 0)
{
switch(lean_obj_tag(v_code_1415_))
{
case 1:
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1480_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1480_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1480_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v_decl_1445_; lean_object* v_k_1446_; size_t v___x_1447_; size_t v___x_1448_; uint8_t v___x_1449_; 
v_decl_1445_ = lean_ctor_get(v_code_1415_, 0);
v_k_1446_ = lean_ctor_get(v_code_1415_, 1);
v___x_1447_ = lean_ptr_addr(v_k_1446_);
v___x_1448_ = lean_ptr_addr(v_a_1441_);
v___x_1449_ = lean_usize_dec_eq(v___x_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1459_; 
v_isSharedCheck_1459_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; lean_object* v_unused_1461_; 
v_unused_1460_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1461_);
v___x_1451_ = v_code_1415_;
v_isShared_1452_ = v_isSharedCheck_1459_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v_code_1415_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1459_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v_a_1441_);
lean_ctor_set(v___x_1451_, 0, v_a_1439_);
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1439_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_a_1441_);
v___x_1454_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1456_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1454_);
v___x_1456_ = v___x_1443_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
size_t v___x_1462_; size_t v___x_1463_; uint8_t v___x_1464_; 
v___x_1462_ = lean_ptr_addr(v_decl_1445_);
v___x_1463_ = lean_ptr_addr(v_a_1439_);
v___x_1464_ = lean_usize_dec_eq(v___x_1462_, v___x_1463_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1474_; 
v_isSharedCheck_1474_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; lean_object* v_unused_1476_; 
v_unused_1475_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1476_);
v___x_1466_ = v_code_1415_;
v_isShared_1467_ = v_isSharedCheck_1474_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_code_1415_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1474_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v_a_1441_);
lean_ctor_set(v___x_1466_, 0, v_a_1439_);
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1439_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_a_1441_);
v___x_1469_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1471_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1469_);
v___x_1471_ = v___x_1443_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_object* v___x_1478_; 
lean_dec(v_a_1441_);
lean_dec(v_a_1439_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v_code_1415_);
v___x_1478_ = v___x_1443_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_code_1415_);
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
}
case 2:
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1520_; 
v_a_1481_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1483_ = v___x_1440_;
v_isShared_1484_ = v_isSharedCheck_1520_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1440_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1520_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_decl_1485_; lean_object* v_k_1486_; size_t v___x_1487_; size_t v___x_1488_; uint8_t v___x_1489_; 
v_decl_1485_ = lean_ctor_get(v_code_1415_, 0);
v_k_1486_ = lean_ctor_get(v_code_1415_, 1);
v___x_1487_ = lean_ptr_addr(v_k_1486_);
v___x_1488_ = lean_ptr_addr(v_a_1481_);
v___x_1489_ = lean_usize_dec_eq(v___x_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1499_; 
v_isSharedCheck_1499_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; lean_object* v_unused_1501_; 
v_unused_1500_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1501_);
v___x_1491_ = v_code_1415_;
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
else
{
lean_dec(v_code_1415_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1499_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v_a_1481_);
lean_ctor_set(v___x_1491_, 0, v_a_1439_);
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1439_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_a_1481_);
v___x_1494_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1494_);
v___x_1496_ = v___x_1483_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
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
size_t v___x_1502_; size_t v___x_1503_; uint8_t v___x_1504_; 
v___x_1502_ = lean_ptr_addr(v_decl_1485_);
v___x_1503_ = lean_ptr_addr(v_a_1439_);
v___x_1504_ = lean_usize_dec_eq(v___x_1502_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1514_; 
v_isSharedCheck_1514_ = !lean_is_exclusive(v_code_1415_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; lean_object* v_unused_1516_; 
v_unused_1515_ = lean_ctor_get(v_code_1415_, 1);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_code_1415_, 0);
lean_dec(v_unused_1516_);
v___x_1506_ = v_code_1415_;
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
else
{
lean_dec(v_code_1415_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 1, v_a_1481_);
lean_ctor_set(v___x_1506_, 0, v_a_1439_);
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1439_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_a_1481_);
v___x_1509_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1511_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1509_);
v___x_1511_ = v___x_1483_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
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
lean_object* v___x_1518_; 
lean_dec(v_a_1481_);
lean_dec(v_a_1439_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v_code_1415_);
v___x_1518_ = v___x_1483_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_code_1415_);
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
}
default: 
{
lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1529_; 
lean_dec(v_a_1439_);
lean_dec_ref(v_code_1415_);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v___x_1440_, 0);
lean_dec(v_unused_1530_);
v___x_1522_ = v___x_1440_;
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
else
{
lean_dec(v___x_1440_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1529_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1524_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3, &l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3);
v___x_1525_ = l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(v___x_1524_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1525_);
v___x_1527_ = v___x_1522_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
else
{
lean_dec(v_a_1439_);
lean_dec_ref(v_code_1415_);
return v___x_1440_;
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec_ref(v_k_1425_);
lean_dec_ref(v_code_1415_);
v_a_1531_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1438_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1438_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
else
{
lean_dec_ref(v_type_1433_);
lean_dec_ref(v_params_1432_);
lean_dec_ref(v_k_1425_);
lean_dec_ref(v_decl_1424_);
lean_dec_ref(v_code_1415_);
return v___x_1436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object* v_i_2148_, lean_object* v_as_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = lean_array_get_size(v_as_2149_);
v___x_2158_ = lean_nat_dec_lt(v_i_2148_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
lean_dec(v_i_2148_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v_as_2149_);
return v___x_2159_;
}
else
{
lean_object* v_a_2160_; lean_object* v___y_2162_; 
v_a_2160_ = lean_array_fget_borrowed(v_as_2149_, v_i_2148_);
switch(lean_obj_tag(v_a_2160_))
{
case 0:
{
lean_object* v_code_2184_; 
v_code_2184_ = lean_ctor_get(v_a_2160_, 2);
lean_inc_ref(v_code_2184_);
v___y_2162_ = v_code_2184_;
goto v___jp_2161_;
}
case 1:
{
lean_object* v_code_2185_; 
v_code_2185_ = lean_ctor_get(v_a_2160_, 1);
lean_inc_ref(v_code_2185_);
v___y_2162_ = v_code_2185_;
goto v___jp_2161_;
}
default: 
{
lean_object* v_code_2186_; 
v_code_2186_ = lean_ctor_get(v_a_2160_, 0);
lean_inc_ref(v_code_2186_);
v___y_2162_ = v_code_2186_;
goto v___jp_2161_;
}
}
v___jp_2161_:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v___y_2162_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2165_; size_t v___x_2166_; size_t v___x_2167_; uint8_t v___x_2168_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
lean_inc(v_a_2160_);
v___x_2165_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2160_, v_a_2164_);
v___x_2166_ = lean_ptr_addr(v_a_2160_);
v___x_2167_ = lean_ptr_addr(v___x_2165_);
v___x_2168_ = lean_usize_dec_eq(v___x_2166_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = lean_unsigned_to_nat(1u);
v___x_2170_ = lean_nat_add(v_i_2148_, v___x_2169_);
v___x_2171_ = lean_array_fset(v_as_2149_, v_i_2148_, v___x_2165_);
lean_dec(v_i_2148_);
v_i_2148_ = v___x_2170_;
v_as_2149_ = v___x_2171_;
goto _start;
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_dec_ref(v___x_2165_);
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = lean_nat_add(v_i_2148_, v___x_2173_);
lean_dec(v_i_2148_);
v_i_2148_ = v___x_2174_;
goto _start;
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v_as_2149_);
lean_dec(v_i_2148_);
v_a_2176_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2163_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2163_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object* v_i_2187_, lean_object* v_as_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_2187_, v_as_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object* v_code_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_code_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(lean_object* v_f_2206_, lean_object* v_v_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
if (lean_obj_tag(v_v_2207_) == 0)
{
lean_object* v_code_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2239_; 
v_code_2215_ = lean_ctor_get(v_v_2207_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_v_2207_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2217_ = v_v_2207_;
v_isShared_2218_ = v_isSharedCheck_2239_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_code_2215_);
lean_dec(v_v_2207_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2239_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; 
lean_inc(v___y_2213_);
lean_inc_ref(v___y_2212_);
lean_inc(v___y_2211_);
lean_inc_ref(v___y_2210_);
lean_inc(v___y_2209_);
lean_inc_ref(v___y_2208_);
v___x_2219_ = lean_apply_8(v_f_2206_, v_code_2215_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, lean_box(0));
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2230_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2230_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2230_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v_a_2220_);
v___x_2225_ = v___x_2217_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2225_);
v___x_2227_ = v___x_2222_;
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
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_del_object(v___x_2217_);
v_a_2231_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2219_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2219_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
else
{
lean_object* v___x_2240_; 
lean_dec_ref(v_f_2206_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v_v_2207_);
return v___x_2240_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(lean_object* v_f_2241_, lean_object* v_v_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2241_, v_v_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(uint8_t v_pu_2251_, lean_object* v_f_2252_, lean_object* v_v_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2252_, v_v_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(lean_object* v_pu_2262_, lean_object* v_f_2263_, lean_object* v_v_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
uint8_t v_pu_boxed_2272_; lean_object* v_res_2273_; 
v_pu_boxed_2272_ = lean_unbox(v_pu_2262_);
v_res_2273_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_boxed_2272_, v_f_2263_, v_v_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object* v_decl_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v_toSignature_2283_; lean_object* v_value_2284_; uint8_t v_recursive_2285_; lean_object* v_inlineAttr_x3f_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2311_; 
v_toSignature_2283_ = lean_ctor_get(v_decl_2275_, 0);
v_value_2284_ = lean_ctor_get(v_decl_2275_, 1);
v_recursive_2285_ = lean_ctor_get_uint8(v_decl_2275_, sizeof(void*)*3);
v_inlineAttr_x3f_2286_ = lean_ctor_get(v_decl_2275_, 2);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_decl_2275_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2288_ = v_decl_2275_;
v_isShared_2289_ = v_isSharedCheck_2311_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_inlineAttr_x3f_2286_);
lean_inc(v_value_2284_);
lean_inc(v_toSignature_2283_);
lean_dec(v_decl_2275_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2311_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0));
v___x_2291_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v___x_2290_, v_value_2284_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2302_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2302_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2302_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 1, v_a_2292_);
v___x_2297_ = v___x_2288_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_toSignature_2283_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_a_2292_);
lean_ctor_set(v_reuseFailAlloc_2301_, 2, v_inlineAttr_x3f_2286_);
lean_ctor_set_uint8(v_reuseFailAlloc_2301_, sizeof(void*)*3, v_recursive_2285_);
v___x_2297_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2299_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2297_);
v___x_2299_ = v___x_2294_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_del_object(v___x_2288_);
lean_dec(v_inlineAttr_x3f_2286_);
lean_dec_ref(v_toSignature_2283_);
v_a_2303_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2291_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2291_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(lean_object* v_decl_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
return v_res_2320_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2323_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_2324_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0));
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_ctor_set(v___x_2325_, 1, v___x_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* v_decl_2326_, lean_object* v_sccDecls_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_toSignature_2333_; lean_object* v_name_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v_toSignature_2333_ = lean_ctor_get(v_decl_2326_, 0);
v_name_2334_ = lean_ctor_get(v_toSignature_2333_, 0);
lean_inc(v_name_2334_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v_name_2334_);
lean_ctor_set(v___x_2335_, 1, v_sccDecls_2327_);
v___x_2336_ = lean_unsigned_to_nat(0u);
v___x_2337_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1);
v___x_2338_ = lean_st_mk_ref(v___x_2337_);
v___x_2339_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2326_, v___x_2335_, v___x_2338_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
lean_dec_ref_known(v___x_2335_, 2);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2365_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2365_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2365_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; lean_object* v_decls_2345_; lean_object* v_decl_2347_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2344_ = lean_st_ref_get(v___x_2338_);
lean_dec(v___x_2338_);
v_decls_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc_ref(v_decls_2345_);
lean_dec(v___x_2344_);
v___x_2352_ = lean_array_get_size(v_decls_2345_);
v___x_2353_ = lean_nat_dec_eq(v___x_2352_, v___x_2336_);
if (v___x_2353_ == 0)
{
uint8_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = 0;
v___x_2355_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2354_, v_a_2340_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v___x_2355_, 1);
v_decl_2347_ = v_a_2356_;
goto v___jp_2346_;
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v_decls_2345_);
lean_del_object(v___x_2342_);
v_a_2357_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2355_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2355_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
v_decl_2347_ = v_a_2340_;
goto v___jp_2346_;
}
v___jp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2348_ = lean_array_push(v_decls_2345_, v_decl_2347_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2348_);
v___x_2350_ = v___x_2342_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
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
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v___x_2338_);
v_a_2366_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2339_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2339_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(lean_object* v_decl_2374_, lean_object* v_sccDecls_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v_decl_2374_, v_sccDecls_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(lean_object* v_decls_2382_, lean_object* v_as_2383_, size_t v_i_2384_, size_t v_stop_2385_, lean_object* v_b_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_a_2393_; uint8_t v___x_2397_; 
v___x_2397_ = lean_usize_dec_eq(v_i_2384_, v_stop_2385_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_array_uget_borrowed(v_as_2383_, v_i_2384_);
lean_inc_ref(v_decls_2382_);
lean_inc(v___x_2398_);
v___x_2399_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v___x_2398_, v_decls_2382_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2401_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v___x_2401_ = l_Array_append___redArg(v_b_2386_, v_a_2400_);
lean_dec(v_a_2400_);
v_a_2393_ = v___x_2401_;
goto v___jp_2392_;
}
else
{
lean_dec_ref(v_b_2386_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2402_; 
v_a_2402_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2399_, 1);
v_a_2393_ = v_a_2402_;
goto v___jp_2392_;
}
else
{
lean_dec_ref(v_decls_2382_);
return v___x_2399_;
}
}
}
else
{
lean_object* v___x_2403_; 
lean_dec_ref(v_decls_2382_);
v___x_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2403_, 0, v_b_2386_);
return v___x_2403_;
}
v___jp_2392_:
{
size_t v___x_2394_; size_t v___x_2395_; 
v___x_2394_ = ((size_t)1ULL);
v___x_2395_ = lean_usize_add(v_i_2384_, v___x_2394_);
v_i_2384_ = v___x_2395_;
v_b_2386_ = v_a_2393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object* v_decls_2404_, lean_object* v_as_2405_, lean_object* v_i_2406_, lean_object* v_stop_2407_, lean_object* v_b_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
size_t v_i_boxed_2414_; size_t v_stop_boxed_2415_; lean_object* v_res_2416_; 
v_i_boxed_2414_ = lean_unbox_usize(v_i_2406_);
lean_dec(v_i_2406_);
v_stop_boxed_2415_ = lean_unbox_usize(v_stop_2407_);
lean_dec(v_stop_2407_);
v_res_2416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2404_, v_as_2405_, v_i_boxed_2414_, v_stop_boxed_2415_, v_b_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec_ref(v_as_2405_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* v___x_2417_, lean_object* v_decls_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_2419_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2449_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2449_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2449_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
uint8_t v_extractClosed_2429_; 
v_extractClosed_2429_ = lean_ctor_get_uint8(v_a_2425_, sizeof(void*)*4 + 1);
lean_dec(v_a_2425_);
if (v_extractClosed_2429_ == 0)
{
lean_object* v___x_2431_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_decls_2418_);
v___x_2431_ = v___x_2427_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_decls_2418_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2433_ = lean_mk_empty_array_with_capacity(v___x_2417_);
v___x_2434_ = lean_array_get_size(v_decls_2418_);
v___x_2435_ = lean_nat_dec_lt(v___x_2417_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2437_; 
lean_dec_ref(v_decls_2418_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2433_);
v___x_2437_ = v___x_2427_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2433_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
else
{
uint8_t v___x_2439_; 
v___x_2439_ = lean_nat_dec_le(v___x_2434_, v___x_2434_);
if (v___x_2439_ == 0)
{
if (v___x_2435_ == 0)
{
lean_object* v___x_2441_; 
lean_dec_ref(v_decls_2418_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2433_);
v___x_2441_ = v___x_2427_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2433_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
else
{
size_t v___x_2443_; size_t v___x_2444_; lean_object* v___x_2445_; 
lean_del_object(v___x_2427_);
v___x_2443_ = ((size_t)0ULL);
v___x_2444_ = lean_usize_of_nat(v___x_2434_);
lean_inc_ref(v_decls_2418_);
v___x_2445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2418_, v_decls_2418_, v___x_2443_, v___x_2444_, v___x_2433_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec_ref(v_decls_2418_);
return v___x_2445_;
}
}
else
{
size_t v___x_2446_; size_t v___x_2447_; lean_object* v___x_2448_; 
lean_del_object(v___x_2427_);
v___x_2446_ = ((size_t)0ULL);
v___x_2447_ = lean_usize_of_nat(v___x_2434_);
lean_inc_ref(v_decls_2418_);
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2418_, v_decls_2418_, v___x_2446_, v___x_2447_, v___x_2433_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec_ref(v_decls_2418_);
return v___x_2448_;
}
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v_decls_2418_);
v_a_2450_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2424_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2424_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object* v___x_2458_, lean_object* v_decls_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(v___x_2458_, v_decls_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___x_2458_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2548_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2549_ = 1;
v___x_2550_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2551_ = l_Lean_registerTraceClass(v___x_2548_, v___x_2549_, v___x_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
return v_res_2553_;
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
