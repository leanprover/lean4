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
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_dec_ref(v___x_13_);
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
lean_dec_ref(v_v_19_);
v___x_38_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(v_struct_37_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
lean_dec(v_struct_37_);
return v___x_38_;
}
case 3:
{
lean_object* v_args_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_args_39_ = lean_ctor_get(v_v_19_, 2);
lean_inc_ref(v_args_39_);
lean_dec_ref(v_v_19_);
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
lean_dec_ref(v_v_19_);
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
v___x_99_ = lean_st_ref_set(v_a_79_, v___x_98_);
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
uint8_t v_____do__lift_18060__boxed_193_; lean_object* v_res_194_; 
v_____do__lift_18060__boxed_193_ = lean_unbox(v_____do__lift_185_);
v_res_194_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v_____do__lift_18060__boxed_193_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
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
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_nbuckets_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_269_ = lean_array_get_size(v_data_268_);
v___x_270_ = lean_unsigned_to_nat(2u);
v_nbuckets_271_ = lean_nat_mul(v___x_269_, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_box(0);
v___x_274_ = lean_mk_array(v_nbuckets_271_, v___x_273_);
v___x_275_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v___x_272_, v_data_268_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(lean_object* v_a_276_, lean_object* v_b_277_, lean_object* v_x_278_){
_start:
{
if (lean_obj_tag(v_x_278_) == 0)
{
lean_dec(v_b_277_);
lean_dec(v_a_276_);
return v_x_278_;
}
else
{
lean_object* v_key_279_; lean_object* v_value_280_; lean_object* v_tail_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_293_; 
v_key_279_ = lean_ctor_get(v_x_278_, 0);
v_value_280_ = lean_ctor_get(v_x_278_, 1);
v_tail_281_ = lean_ctor_get(v_x_278_, 2);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_278_);
if (v_isSharedCheck_293_ == 0)
{
v___x_283_ = v_x_278_;
v_isShared_284_ = v_isSharedCheck_293_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_tail_281_);
lean_inc(v_value_280_);
lean_inc(v_key_279_);
lean_dec(v_x_278_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_293_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
uint8_t v___x_285_; 
v___x_285_ = l_Lean_instBEqFVarId_beq(v_key_279_, v_a_276_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_276_, v_b_277_, v_tail_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 2, v___x_286_);
v___x_288_ = v___x_283_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_key_279_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_value_280_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
else
{
lean_object* v___x_291_; 
lean_dec(v_value_280_);
lean_dec(v_key_279_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_b_277_);
lean_ctor_set(v___x_283_, 0, v_a_276_);
v___x_291_ = v___x_283_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_276_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_b_277_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_tail_281_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(lean_object* v_a_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
uint8_t v___x_296_; 
v___x_296_ = 0;
return v___x_296_;
}
else
{
lean_object* v_key_297_; lean_object* v_tail_298_; uint8_t v___x_299_; 
v_key_297_ = lean_ctor_get(v_x_295_, 0);
v_tail_298_ = lean_ctor_get(v_x_295_, 2);
v___x_299_ = l_Lean_instBEqFVarId_beq(v_key_297_, v_a_294_);
if (v___x_299_ == 0)
{
v_x_295_ = v_tail_298_;
goto _start;
}
else
{
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg___boxed(lean_object* v_a_301_, lean_object* v_x_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_301_, v_x_302_);
lean_dec(v_x_302_);
lean_dec(v_a_301_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(lean_object* v_m_305_, lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
lean_object* v_size_308_; lean_object* v_buckets_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_352_; 
v_size_308_ = lean_ctor_get(v_m_305_, 0);
v_buckets_309_ = lean_ctor_get(v_m_305_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v_m_305_);
if (v_isSharedCheck_352_ == 0)
{
v___x_311_ = v_m_305_;
v_isShared_312_ = v_isSharedCheck_352_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_buckets_309_);
lean_inc(v_size_308_);
lean_dec(v_m_305_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_352_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v_fold_317_; uint64_t v___x_318_; uint64_t v___x_319_; uint64_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v_bkt_326_; uint8_t v___x_327_; 
v___x_313_ = lean_array_get_size(v_buckets_309_);
v___x_314_ = l_Lean_instHashableFVarId_hash(v_a_306_);
v___x_315_ = 32ULL;
v___x_316_ = lean_uint64_shift_right(v___x_314_, v___x_315_);
v_fold_317_ = lean_uint64_xor(v___x_314_, v___x_316_);
v___x_318_ = 16ULL;
v___x_319_ = lean_uint64_shift_right(v_fold_317_, v___x_318_);
v___x_320_ = lean_uint64_xor(v_fold_317_, v___x_319_);
v___x_321_ = lean_uint64_to_usize(v___x_320_);
v___x_322_ = lean_usize_of_nat(v___x_313_);
v___x_323_ = ((size_t)1ULL);
v___x_324_ = lean_usize_sub(v___x_322_, v___x_323_);
v___x_325_ = lean_usize_land(v___x_321_, v___x_324_);
v_bkt_326_ = lean_array_uget_borrowed(v_buckets_309_, v___x_325_);
v___x_327_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_306_, v_bkt_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v_size_x27_329_; lean_object* v___x_330_; lean_object* v_buckets_x27_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v_size_x27_329_ = lean_nat_add(v_size_308_, v___x_328_);
lean_dec(v_size_308_);
lean_inc(v_bkt_326_);
v___x_330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_330_, 0, v_a_306_);
lean_ctor_set(v___x_330_, 1, v_b_307_);
lean_ctor_set(v___x_330_, 2, v_bkt_326_);
v_buckets_x27_331_ = lean_array_uset(v_buckets_309_, v___x_325_, v___x_330_);
v___x_332_ = lean_unsigned_to_nat(4u);
v___x_333_ = lean_nat_mul(v_size_x27_329_, v___x_332_);
v___x_334_ = lean_unsigned_to_nat(3u);
v___x_335_ = lean_nat_div(v___x_333_, v___x_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_array_get_size(v_buckets_x27_331_);
v___x_337_ = lean_nat_dec_le(v___x_335_, v___x_336_);
lean_dec(v___x_335_);
if (v___x_337_ == 0)
{
lean_object* v_val_338_; lean_object* v___x_340_; 
v_val_338_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_buckets_x27_331_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v_val_338_);
lean_ctor_set(v___x_311_, 0, v_size_x27_329_);
v___x_340_ = v___x_311_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_size_x27_329_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_val_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
else
{
lean_object* v___x_343_; 
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v_buckets_x27_331_);
lean_ctor_set(v___x_311_, 0, v_size_x27_329_);
v___x_343_ = v___x_311_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_size_x27_329_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_buckets_x27_331_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v___x_345_; lean_object* v_buckets_x27_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
lean_inc(v_bkt_326_);
v___x_345_ = lean_box(0);
v_buckets_x27_346_ = lean_array_uset(v_buckets_309_, v___x_325_, v___x_345_);
v___x_347_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_306_, v_b_307_, v_bkt_326_);
v___x_348_ = lean_array_uset(v_buckets_x27_346_, v___x_325_, v___x_347_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_348_);
v___x_350_ = v___x_311_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_size_308_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(lean_object* v_declName_353_, lean_object* v_as_354_, size_t v_i_355_, size_t v_stop_356_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_usize_dec_eq(v_i_355_, v_stop_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v_toSignature_359_; lean_object* v_name_360_; uint8_t v___x_361_; 
v___x_358_ = lean_array_uget_borrowed(v_as_354_, v_i_355_);
v_toSignature_359_ = lean_ctor_get(v___x_358_, 0);
v_name_360_ = lean_ctor_get(v_toSignature_359_, 0);
v___x_361_ = lean_name_eq(v_name_360_, v_declName_353_);
if (v___x_361_ == 0)
{
size_t v___x_362_; size_t v___x_363_; 
v___x_362_ = ((size_t)1ULL);
v___x_363_ = lean_usize_add(v_i_355_, v___x_362_);
v_i_355_ = v___x_363_;
goto _start;
}
else
{
return v___x_361_;
}
}
else
{
uint8_t v___x_365_; 
v___x_365_ = 0;
return v___x_365_;
}
}
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(uint8_t v_isRoot_374_, uint8_t v___x_375_, lean_object* v_as_376_, size_t v_i_377_, size_t v_stop_378_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object* v_isRoot_389_, lean_object* v___x_390_, lean_object* v_as_391_, lean_object* v_i_392_, lean_object* v_stop_393_){
_start:
{
uint8_t v_isRoot_boxed_394_; uint8_t v___x_18365__boxed_395_; size_t v_i_boxed_396_; size_t v_stop_boxed_397_; uint8_t v_res_398_; lean_object* v_r_399_; 
v_isRoot_boxed_394_ = lean_unbox(v_isRoot_389_);
v___x_18365__boxed_395_ = lean_unbox(v___x_390_);
v_i_boxed_396_ = lean_unbox_usize(v_i_392_);
lean_dec(v_i_392_);
v_stop_boxed_397_ = lean_unbox_usize(v_stop_393_);
lean_dec(v_stop_393_);
v_res_398_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_boxed_394_, v___x_18365__boxed_395_, v_as_391_, v_i_boxed_396_, v_stop_boxed_397_);
lean_dec_ref(v_as_391_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0(void){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_cstr_to_nat("9223372036854775808");
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(uint8_t v___x_401_, lean_object* v_as_402_, size_t v_i_403_, size_t v_stop_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = lean_usize_dec_eq(v_i_403_, v_stop_404_);
if (v___x_412_ == 0)
{
uint8_t v___x_413_; uint8_t v_a_415_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_413_ = 1;
v___x_421_ = lean_array_uget_borrowed(v_as_402_, v_i_403_);
lean_inc(v___x_421_);
v___x_422_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_421_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_432_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_432_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
uint8_t v___x_427_; 
v___x_427_ = lean_unbox(v_a_423_);
lean_dec(v_a_423_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = lean_box(v___x_413_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_428_);
v___x_430_ = v___x_425_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
lean_del_object(v___x_425_);
v_a_415_ = v___x_401_;
goto v___jp_414_;
}
}
}
else
{
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_433_; uint8_t v___x_434_; 
v_a_433_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_433_);
lean_dec_ref(v___x_422_);
v___x_434_ = lean_unbox(v_a_433_);
lean_dec(v_a_433_);
v_a_415_ = v___x_434_;
goto v___jp_414_;
}
else
{
return v___x_422_;
}
}
v___jp_414_:
{
if (v_a_415_ == 0)
{
size_t v___x_416_; size_t v___x_417_; 
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_add(v_i_403_, v___x_416_);
v_i_403_ = v___x_417_;
goto _start;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_box(v___x_413_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
}
else
{
uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = 0;
v___x_436_ = lean_box(v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(lean_object* v_as_438_, size_t v_i_439_, size_t v_stop_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
uint8_t v___x_448_; 
v___x_448_ = lean_usize_dec_eq(v_i_439_, v_stop_440_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; uint8_t v_a_451_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_449_ = 1;
v___x_457_ = lean_array_uget_borrowed(v_as_438_, v_i_439_);
lean_inc(v___x_457_);
v___x_458_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_457_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_468_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_468_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; 
v___x_463_ = lean_unbox(v_a_459_);
lean_dec(v_a_459_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_464_ = lean_box(v___x_449_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_464_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_del_object(v___x_461_);
v_a_451_ = v___x_448_;
goto v___jp_450_;
}
}
}
else
{
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_469_; uint8_t v___x_470_; 
v_a_469_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_469_);
lean_dec_ref(v___x_458_);
v___x_470_ = lean_unbox(v_a_469_);
lean_dec(v_a_469_);
v_a_451_ = v___x_470_;
goto v___jp_450_;
}
else
{
return v___x_458_;
}
}
v___jp_450_:
{
if (v_a_451_ == 0)
{
size_t v___x_452_; size_t v___x_453_; 
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_add(v_i_439_, v___x_452_);
v_i_439_ = v___x_453_;
goto _start;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_box(v___x_449_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
}
else
{
uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = 0;
v___x_472_ = lean_box(v___x_471_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t v_isRoot_474_, lean_object* v_v_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
uint8_t v___y_484_; uint8_t v_____do__lift_485_; 
switch(lean_obj_tag(v_v_475_))
{
case 0:
{
lean_object* v_value_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_536_; 
v_value_491_ = lean_ctor_get(v_v_475_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_v_475_);
if (v_isSharedCheck_536_ == 0)
{
v___x_493_ = v_v_475_;
v_isShared_494_ = v_isSharedCheck_536_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_value_491_);
lean_dec(v_v_475_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_536_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
switch(lean_obj_tag(v_value_491_))
{
case 1:
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_503_; 
lean_del_object(v___x_493_);
v_isSharedCheck_503_ = !lean_is_exclusive(v_value_491_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v_value_491_, 0);
lean_dec(v_unused_504_);
v___x_496_ = v_value_491_;
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_value_491_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_498_ = 1;
v___x_499_ = lean_box(v___x_498_);
if (v_isShared_497_ == 0)
{
lean_ctor_set_tag(v___x_496_, 0);
lean_ctor_set(v___x_496_, 0, v___x_499_);
v___x_501_ = v___x_496_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
case 0:
{
lean_del_object(v___x_493_);
if (v_isRoot_474_ == 0)
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_513_; 
v_isSharedCheck_513_ = !lean_is_exclusive(v_value_491_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v_value_491_, 0);
lean_dec(v_unused_514_);
v___x_506_ = v_value_491_;
v_isShared_507_ = v_isSharedCheck_513_;
goto v_resetjp_505_;
}
else
{
lean_dec(v_value_491_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_513_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = 1;
v___x_509_ = lean_box(v___x_508_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_509_);
v___x_511_ = v___x_506_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v_val_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_525_; 
v_val_515_ = lean_ctor_get(v_value_491_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v_value_491_);
if (v_isSharedCheck_525_ == 0)
{
v___x_517_ = v_value_491_;
v_isShared_518_ = v_isSharedCheck_525_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_val_515_);
lean_dec(v_value_491_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_525_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_519_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0, &l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0);
v___x_520_ = lean_nat_dec_le(v___x_519_, v_val_515_);
lean_dec(v_val_515_);
v___x_521_ = lean_box(v___x_520_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_521_);
v___x_523_ = v___x_517_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
default: 
{
lean_dec_ref(v_value_491_);
if (v_isRoot_474_ == 0)
{
uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_526_ = 1;
v___x_527_ = lean_box(v___x_526_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_527_);
v___x_529_ = v___x_493_;
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
else
{
uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_531_ = 0;
v___x_532_ = lean_box(v___x_531_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_532_);
v___x_534_ = v___x_493_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
case 1:
{
if (v_isRoot_474_ == 0)
{
uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = 1;
v___x_538_ = lean_box(v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
else
{
uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = 0;
v___x_541_ = lean_box(v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
case 2:
{
lean_object* v_struct_543_; lean_object* v___x_544_; 
v_struct_543_ = lean_ctor_get(v_v_475_, 2);
lean_inc(v_struct_543_);
lean_dec_ref(v_v_475_);
v___x_544_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_struct_543_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
return v___x_544_;
}
case 3:
{
lean_object* v_declName_545_; lean_object* v_args_546_; lean_object* v_sccDecls_547_; lean_object* v___x_548_; uint8_t v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; uint8_t v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; uint8_t v___y_594_; uint8_t v___y_598_; uint8_t v___y_599_; uint8_t v___y_603_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_declName_545_ = lean_ctor_get(v_v_475_, 0);
lean_inc(v_declName_545_);
v_args_546_ = lean_ctor_get(v_v_475_, 2);
lean_inc_ref(v_args_546_);
lean_dec_ref(v_v_475_);
v_sccDecls_547_ = lean_ctor_get(v_a_476_, 1);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_array_get_size(v_sccDecls_547_);
v___x_623_ = lean_nat_dec_lt(v___x_548_, v___x_622_);
if (v___x_623_ == 0)
{
v___y_603_ = v___x_623_;
goto v___jp_602_;
}
else
{
if (v___x_623_ == 0)
{
v___y_603_ = v___x_623_;
goto v___jp_602_;
}
else
{
size_t v___x_624_; size_t v___x_625_; uint8_t v___x_626_; 
v___x_624_ = ((size_t)0ULL);
v___x_625_ = lean_usize_of_nat(v___x_622_);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_545_, v_sccDecls_547_, v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
v___y_603_ = v___x_626_;
goto v___jp_602_;
}
else
{
uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec_ref(v_args_546_);
lean_dec(v_declName_545_);
v___x_627_ = 0;
v___x_628_ = lean_box(v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
}
v___jp_549_:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_array_get_size(v_args_546_);
v___x_558_ = lean_nat_dec_lt(v___x_548_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec_ref(v_args_546_);
v___y_484_ = v___y_550_;
v_____do__lift_485_ = v___y_550_;
goto v___jp_483_;
}
else
{
if (v___x_558_ == 0)
{
lean_dec_ref(v_args_546_);
v___y_484_ = v___y_550_;
v_____do__lift_485_ = v___y_550_;
goto v___jp_483_;
}
else
{
size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; 
v___x_559_ = ((size_t)0ULL);
v___x_560_ = lean_usize_of_nat(v___x_557_);
v___x_561_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___y_550_, v_args_546_, v___x_559_, v___x_560_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec_ref(v_args_546_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v_a_562_; uint8_t v___x_563_; 
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref(v___x_561_);
v___x_563_ = lean_unbox(v_a_562_);
lean_dec(v_a_562_);
v___y_484_ = v___y_550_;
v_____do__lift_485_ = v___x_563_;
goto v___jp_483_;
}
else
{
return v___x_561_;
}
}
}
}
v___jp_564_:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_545_, v___y_571_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_584_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_584_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
if (lean_obj_tag(v_a_573_) == 1)
{
lean_object* v_val_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v_val_577_ = lean_ctor_get(v_a_573_, 0);
lean_inc(v_val_577_);
lean_dec_ref(v_a_573_);
v___x_578_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_577_);
lean_dec(v_val_577_);
v___x_579_ = lean_nat_dec_eq(v___x_578_, v___x_548_);
lean_dec(v___x_578_);
if (v___x_579_ == 0)
{
lean_del_object(v___x_575_);
v___y_550_ = v___y_565_;
v___y_551_ = v___y_566_;
v___y_552_ = v___y_567_;
v___y_553_ = v___y_568_;
v___y_554_ = v___y_569_;
v___y_555_ = v___y_570_;
v___y_556_ = v___y_571_;
goto v___jp_549_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec_ref(v_args_546_);
v___x_580_ = lean_box(v___y_565_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_580_);
v___x_582_ = v___x_575_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
lean_del_object(v___x_575_);
lean_dec(v_a_573_);
v___y_550_ = v___y_565_;
v___y_551_ = v___y_566_;
v___y_552_ = v___y_567_;
v___y_553_ = v___y_568_;
v___y_554_ = v___y_569_;
v___y_555_ = v___y_570_;
v___y_556_ = v___y_571_;
goto v___jp_549_;
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v_args_546_);
v_a_585_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_572_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_572_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
v___jp_593_:
{
if (v___y_594_ == 0)
{
v___y_565_ = v___y_594_;
v___y_566_ = v_a_476_;
v___y_567_ = v_a_477_;
v___y_568_ = v_a_478_;
v___y_569_ = v_a_479_;
v___y_570_ = v_a_480_;
v___y_571_ = v_a_481_;
goto v___jp_564_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec_ref(v_args_546_);
lean_dec(v_declName_545_);
v___x_595_ = lean_box(v___y_594_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
v___jp_597_:
{
if (v___y_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec_ref(v_args_546_);
lean_dec(v_declName_545_);
v___x_600_ = lean_box(v___y_598_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
else
{
v___y_594_ = v___y_598_;
goto v___jp_593_;
}
}
v___jp_602_:
{
lean_object* v___x_604_; lean_object* v_env_605_; uint8_t v___x_606_; 
v___x_604_ = lean_st_ref_get(v_a_481_);
v_env_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_604_);
lean_inc(v_declName_545_);
v___x_606_ = l_Lean_hasNeverExtractAttribute(v_env_605_, v_declName_545_);
if (v___x_606_ == 0)
{
if (v_isRoot_474_ == 0)
{
lean_dec(v_declName_545_);
v___y_550_ = v___x_606_;
v___y_551_ = v_a_476_;
v___y_552_ = v_a_477_;
v___y_553_ = v_a_478_;
v___y_554_ = v_a_479_;
v___y_555_ = v_a_480_;
v___y_556_ = v_a_481_;
goto v___jp_549_;
}
else
{
lean_object* v___x_607_; lean_object* v_env_608_; lean_object* v___x_609_; 
v___x_607_ = lean_st_ref_get(v_a_481_);
v_env_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc_ref(v_env_608_);
lean_dec(v___x_607_);
lean_inc(v_declName_545_);
v___x_609_ = l_Lean_Environment_find_x3f(v_env_608_, v_declName_545_, v___x_606_);
if (lean_obj_tag(v___x_609_) == 1)
{
lean_object* v_val_610_; 
v_val_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_val_610_);
lean_dec_ref(v___x_609_);
switch(lean_obj_tag(v_val_610_))
{
case 1:
{
lean_object* v_val_611_; lean_object* v_toConstantVal_612_; lean_object* v_type_613_; uint8_t v___x_614_; 
v_val_611_ = lean_ctor_get(v_val_610_, 0);
lean_inc_ref(v_val_611_);
lean_dec_ref(v_val_610_);
v_toConstantVal_612_ = lean_ctor_get(v_val_611_, 0);
lean_inc_ref(v_toConstantVal_612_);
lean_dec_ref(v_val_611_);
v_type_613_ = lean_ctor_get(v_toConstantVal_612_, 2);
lean_inc_ref(v_type_613_);
lean_dec_ref(v_toConstantVal_612_);
v___x_614_ = l_Lean_Expr_isForall(v_type_613_);
lean_dec_ref(v_type_613_);
v___y_598_ = v___x_606_;
v___y_599_ = v___x_614_;
goto v___jp_597_;
}
case 6:
{
lean_object* v___x_615_; uint8_t v___x_616_; 
lean_dec_ref(v_val_610_);
v___x_615_ = lean_array_get_size(v_args_546_);
v___x_616_ = lean_nat_dec_lt(v___x_548_, v___x_615_);
if (v___x_616_ == 0)
{
v___y_598_ = v___x_606_;
v___y_599_ = v___x_606_;
goto v___jp_597_;
}
else
{
if (v___x_616_ == 0)
{
v___y_598_ = v___x_606_;
v___y_599_ = v___x_606_;
goto v___jp_597_;
}
else
{
size_t v___x_617_; size_t v___x_618_; uint8_t v___x_619_; 
v___x_617_ = ((size_t)0ULL);
v___x_618_ = lean_usize_of_nat(v___x_615_);
v___x_619_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_474_, v___x_606_, v_args_546_, v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
v___y_598_ = v___x_606_;
v___y_599_ = v___x_606_;
goto v___jp_597_;
}
else
{
v___y_598_ = v___x_606_;
v___y_599_ = v___x_619_;
goto v___jp_597_;
}
}
}
}
default: 
{
lean_dec(v_val_610_);
v___y_594_ = v___x_606_;
goto v___jp_593_;
}
}
}
else
{
lean_dec(v___x_609_);
v___y_565_ = v___x_606_;
v___y_566_ = v_a_476_;
v___y_567_ = v_a_477_;
v___y_568_ = v_a_478_;
v___y_569_ = v_a_479_;
v___y_570_ = v_a_480_;
v___y_571_ = v_a_481_;
goto v___jp_564_;
}
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec_ref(v_args_546_);
lean_dec(v_declName_545_);
v___x_620_ = lean_box(v___y_603_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
default: 
{
lean_object* v_fvarId_630_; lean_object* v_args_631_; lean_object* v___x_632_; 
v_fvarId_630_ = lean_ctor_get(v_v_475_, 0);
lean_inc(v_fvarId_630_);
v_args_631_ = lean_ctor_get(v_v_475_, 1);
lean_inc_ref(v_args_631_);
lean_dec_ref(v_v_475_);
v___x_632_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_630_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___y_635_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_array_get_size(v_args_631_);
v___x_647_ = lean_nat_dec_lt(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
lean_dec_ref(v_args_631_);
v___x_648_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_647_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
v___y_635_ = v___x_648_;
goto v___jp_634_;
}
else
{
if (v___x_647_ == 0)
{
lean_object* v___x_649_; 
lean_dec_ref(v_args_631_);
v___x_649_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_647_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
v___y_635_ = v___x_649_;
goto v___jp_634_;
}
else
{
size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
v___x_650_ = ((size_t)0ULL);
v___x_651_ = lean_usize_of_nat(v___x_646_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_args_631_, v___x_650_, v___x_651_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec_ref(v_args_631_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; uint8_t v___x_654_; lean_object* v___x_655_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref(v___x_652_);
v___x_654_ = lean_unbox(v_a_653_);
lean_dec(v_a_653_);
v___x_655_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_654_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
v___y_635_ = v___x_655_;
goto v___jp_634_;
}
else
{
v___y_635_ = v___x_652_;
goto v___jp_634_;
}
}
}
v___jp_634_:
{
if (lean_obj_tag(v___y_635_) == 0)
{
uint8_t v___x_636_; 
v___x_636_ = lean_unbox(v_a_633_);
if (v___x_636_ == 0)
{
lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
v_isSharedCheck_643_ = !lean_is_exclusive(v___y_635_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v___y_635_, 0);
lean_dec(v_unused_644_);
v___x_638_ = v___y_635_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_dec(v___y_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v_a_633_);
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_633_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_dec(v_a_633_);
return v___y_635_;
}
}
else
{
lean_dec(v_a_633_);
return v___y_635_;
}
}
}
else
{
lean_dec_ref(v_args_631_);
return v___x_632_;
}
}
}
v___jp_483_:
{
if (v_____do__lift_485_ == 0)
{
uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = 1;
v___x_487_ = lean_box(v___x_486_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_box(v___y_484_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(lean_object* v_fvarId_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
uint8_t v___x_664_; lean_object* v___x_665_; 
v___x_664_ = 0;
v___x_665_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_664_, v_fvarId_656_, v_a_660_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_679_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_679_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_679_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_679_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
if (lean_obj_tag(v_a_666_) == 1)
{
lean_object* v_val_670_; lean_object* v_value_671_; uint8_t v___x_672_; lean_object* v___x_673_; 
lean_del_object(v___x_668_);
v_val_670_ = lean_ctor_get(v_a_666_, 0);
lean_inc(v_val_670_);
lean_dec_ref(v_a_666_);
v_value_671_ = lean_ctor_get(v_val_670_, 3);
lean_inc(v_value_671_);
lean_dec(v_val_670_);
v___x_672_ = 0;
v___x_673_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_672_, v_value_671_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
return v___x_673_;
}
else
{
uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
lean_dec(v_a_666_);
v___x_674_ = 0;
v___x_675_ = lean_box(v___x_674_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_675_);
v___x_677_ = v___x_668_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
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
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
v_a_680_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_665_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_665_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object* v_fvarId_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v___x_696_; lean_object* v_fvarDecisionCache_697_; lean_object* v___x_698_; 
v___x_696_ = lean_st_ref_get(v_a_690_);
v_fvarDecisionCache_697_ = lean_ctor_get(v___x_696_, 1);
lean_inc_ref(v_fvarDecisionCache_697_);
lean_dec(v___x_696_);
v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_fvarDecisionCache_697_, v_fvarId_688_);
lean_dec_ref(v_fvarDecisionCache_697_);
if (lean_obj_tag(v___x_698_) == 1)
{
lean_object* v_val_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_fvarId_688_);
v_val_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_val_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 0);
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_val_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_object* v___x_707_; 
lean_dec(v___x_698_);
v___x_707_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_727_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_727_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_727_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_727_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v_decls_713_; lean_object* v_fvarDecisionCache_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_726_; 
v___x_712_ = lean_st_ref_take(v_a_690_);
v_decls_713_ = lean_ctor_get(v___x_712_, 0);
v_fvarDecisionCache_714_ = lean_ctor_get(v___x_712_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_726_ == 0)
{
v___x_716_ = v___x_712_;
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_fvarDecisionCache_714_);
lean_inc(v_decls_713_);
lean_dec(v___x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
lean_inc(v_a_708_);
v___x_718_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_fvarDecisionCache_714_, v_fvarId_688_, v_a_708_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_decls_713_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_725_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_721_ = lean_st_ref_set(v_a_690_, v___x_720_);
if (v_isShared_711_ == 0)
{
v___x_723_ = v___x_710_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_708_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_688_);
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object* v_arg_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
if (lean_obj_tag(v_arg_728_) == 1)
{
lean_object* v_fvarId_736_; lean_object* v___x_737_; 
v_fvarId_736_ = lean_ctor_get(v_arg_728_, 0);
lean_inc(v_fvarId_736_);
lean_dec_ref(v_arg_728_);
v___x_737_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_736_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
return v___x_737_;
}
else
{
uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v_arg_728_);
v___x_738_ = 1;
v___x_739_ = lean_box(v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object* v_arg_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v_arg_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(lean_object* v_fvarId_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_fvarId_750_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object* v_fvarId_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object* v___x_768_, lean_object* v_as_769_, lean_object* v_i_770_, lean_object* v_stop_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
uint8_t v___x_18418__boxed_779_; size_t v_i_boxed_780_; size_t v_stop_boxed_781_; lean_object* v_res_782_; 
v___x_18418__boxed_779_ = lean_unbox(v___x_768_);
v_i_boxed_780_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_stop_boxed_781_ = lean_unbox_usize(v_stop_771_);
lean_dec(v_stop_771_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___x_18418__boxed_779_, v_as_769_, v_i_boxed_780_, v_stop_boxed_781_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v_as_769_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(lean_object* v_as_783_, lean_object* v_i_784_, lean_object* v_stop_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
size_t v_i_boxed_793_; size_t v_stop_boxed_794_; lean_object* v_res_795_; 
v_i_boxed_793_ = lean_unbox_usize(v_i_784_);
lean_dec(v_i_784_);
v_stop_boxed_794_ = lean_unbox_usize(v_stop_785_);
lean_dec(v_stop_785_);
v_res_795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_as_783_, v_i_boxed_793_, v_stop_boxed_794_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec_ref(v_as_783_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object* v_isRoot_796_, lean_object* v_v_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
uint8_t v_isRoot_boxed_805_; lean_object* v_res_806_; 
v_isRoot_boxed_805_ = lean_unbox(v_isRoot_796_);
v_res_806_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v_isRoot_boxed_805_, v_v_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object* v_00_u03b2_807_, lean_object* v_m_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_808_, v_a_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___boxed(lean_object* v_00_u03b2_811_, lean_object* v_m_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(v_00_u03b2_811_, v_m_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_m_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(lean_object* v_00_u03b2_815_, lean_object* v_m_816_, lean_object* v_a_817_, lean_object* v_b_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_m_816_, v_a_817_, v_b_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(lean_object* v_00_u03b2_820_, lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_821_, v_x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___boxed(lean_object* v_00_u03b2_824_, lean_object* v_a_825_, lean_object* v_x_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(v_00_u03b2_824_, v_a_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec(v_a_825_);
return v_res_827_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(lean_object* v_00_u03b2_828_, lean_object* v_a_829_, lean_object* v_x_830_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___boxed(lean_object* v_00_u03b2_832_, lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
uint8_t v_res_835_; lean_object* v_r_836_; 
v_res_835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(v_00_u03b2_832_, v_a_833_, v_x_834_);
lean_dec(v_x_834_);
lean_dec(v_a_833_);
v_r_836_ = lean_box(v_res_835_);
return v_r_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10(lean_object* v_00_u03b2_837_, lean_object* v_data_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_data_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11(lean_object* v_00_u03b2_840_, lean_object* v_a_841_, lean_object* v_b_842_, lean_object* v_x_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_841_, v_b_842_, v_x_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_845_, lean_object* v_i_846_, lean_object* v_source_847_, lean_object* v_target_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v_i_846_, v_source_847_, v_target_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_850_, lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_x_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(lean_object* v_prevArrayId_859_, lean_object* v_decl_860_, lean_object* v_k_861_, lean_object* v_illegalSet_862_, lean_object* v_size_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_decl_875_; lean_object* v_k_876_; lean_object* v_illegalSet_877_; lean_object* v_zero_885_; uint8_t v_isZero_886_; 
v_zero_885_ = lean_unsigned_to_nat(0u);
v_isZero_886_ = lean_nat_dec_eq(v_size_863_, v_zero_885_);
if (v_isZero_886_ == 1)
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
lean_dec(v_prevArrayId_859_);
v___x_887_ = lean_box(0);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
else
{
lean_object* v_value_889_; 
v_value_889_ = lean_ctor_get(v_decl_860_, 3);
if (lean_obj_tag(v_value_889_) == 3)
{
lean_object* v_declName_890_; 
v_declName_890_ = lean_ctor_get(v_value_889_, 0);
if (lean_obj_tag(v_declName_890_) == 1)
{
lean_object* v_pre_891_; 
v_pre_891_ = lean_ctor_get(v_declName_890_, 0);
if (lean_obj_tag(v_pre_891_) == 1)
{
lean_object* v_pre_892_; 
v_pre_892_ = lean_ctor_get(v_pre_891_, 0);
if (lean_obj_tag(v_pre_892_) == 0)
{
lean_object* v_fvarId_893_; lean_object* v_args_894_; lean_object* v_str_895_; lean_object* v_str_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v_fvarId_893_ = lean_ctor_get(v_decl_860_, 0);
v_args_894_ = lean_ctor_get(v_value_889_, 2);
v_str_895_ = lean_ctor_get(v_declName_890_, 1);
v_str_896_ = lean_ctor_get(v_pre_891_, 1);
v___x_897_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_898_ = lean_string_dec_eq(v_str_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
lean_dec(v_prevArrayId_859_);
goto v___jp_871_;
}
else
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_900_ = lean_string_dec_eq(v_str_895_, v___x_899_);
if (v___x_900_ == 0)
{
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
lean_dec(v_prevArrayId_859_);
goto v___jp_871_;
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_901_ = lean_array_get_size(v_args_894_);
v___x_902_ = lean_unsigned_to_nat(3u);
v___x_903_ = lean_nat_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
lean_dec(v_prevArrayId_859_);
goto v___jp_871_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_array_fget(v_args_894_, v___x_904_);
if (lean_obj_tag(v___x_905_) == 1)
{
lean_object* v_fvarId_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_1023_; 
v_fvarId_906_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_1023_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_fvarId_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_1023_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
uint8_t v___x_910_; 
v___x_910_ = l_Lean_instBEqFVarId_beq(v_fvarId_906_, v_prevArrayId_859_);
lean_dec(v_prevArrayId_859_);
lean_dec(v_fvarId_906_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_913_; 
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
v___x_911_ = lean_box(0);
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 0);
lean_ctor_set(v___x_908_, 0, v___x_911_);
v___x_913_ = v___x_908_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_del_object(v___x_908_);
v___x_915_ = lean_unsigned_to_nat(2u);
v___x_916_ = lean_array_fget_borrowed(v_args_894_, v___x_915_);
lean_inc(v___x_916_);
v___x_917_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_916_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_1014_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_1014_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_1014_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
uint8_t v___x_922_; 
v___x_922_ = lean_unbox(v_a_918_);
lean_dec(v_a_918_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_925_; 
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
v___x_923_ = lean_box(0);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_923_);
v___x_925_ = v___x_920_;
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
else
{
lean_object* v_n_927_; uint8_t v___x_928_; 
v_n_927_ = lean_nat_sub(v_size_863_, v___x_904_);
lean_dec(v_size_863_);
v___x_928_ = lean_nat_dec_eq(v_n_927_, v_zero_885_);
if (v___x_928_ == 0)
{
lean_inc(v_fvarId_893_);
lean_dec_ref(v_decl_860_);
if (lean_obj_tag(v_k_861_) == 0)
{
lean_object* v_decl_929_; lean_object* v_k_930_; lean_object* v___x_931_; 
lean_del_object(v___x_920_);
v_decl_929_ = lean_ctor_get(v_k_861_, 0);
lean_inc_ref(v_decl_929_);
v_k_930_ = lean_ctor_get(v_k_861_, 1);
lean_inc_ref(v_k_930_);
lean_dec_ref(v_k_861_);
lean_inc(v_fvarId_893_);
v___x_931_ = l_Lean_FVarIdSet_insert(v_illegalSet_862_, v_fvarId_893_);
v_prevArrayId_859_ = v_fvarId_893_;
v_decl_860_ = v_decl_929_;
v_k_861_ = v_k_930_;
v_illegalSet_862_ = v___x_931_;
v_size_863_ = v_n_927_;
goto _start;
}
else
{
lean_object* v___x_933_; lean_object* v___x_935_; 
lean_dec(v_n_927_);
lean_dec(v_fvarId_893_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
v___x_933_ = lean_box(0);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_933_);
v___x_935_ = v___x_920_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
else
{
lean_dec(v_n_927_);
lean_del_object(v___x_920_);
if (lean_obj_tag(v_k_861_) == 0)
{
lean_object* v_decl_937_; lean_object* v_value_938_; 
v_decl_937_ = lean_ctor_get(v_k_861_, 0);
lean_inc_ref(v_decl_937_);
v_value_938_ = lean_ctor_get(v_decl_937_, 3);
lean_inc(v_value_938_);
if (lean_obj_tag(v_value_938_) == 3)
{
lean_object* v_declName_939_; 
v_declName_939_ = lean_ctor_get(v_value_938_, 0);
lean_inc(v_declName_939_);
if (lean_obj_tag(v_declName_939_) == 1)
{
lean_object* v_pre_940_; 
v_pre_940_ = lean_ctor_get(v_declName_939_, 0);
lean_inc(v_pre_940_);
if (lean_obj_tag(v_pre_940_) == 1)
{
lean_object* v_pre_941_; 
v_pre_941_ = lean_ctor_get(v_pre_940_, 0);
lean_inc(v_pre_941_);
if (lean_obj_tag(v_pre_941_) == 0)
{
lean_object* v_k_942_; lean_object* v_fvarId_943_; lean_object* v_binderName_944_; lean_object* v_type_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1012_; 
v_k_942_ = lean_ctor_get(v_k_861_, 1);
v_fvarId_943_ = lean_ctor_get(v_decl_937_, 0);
v_binderName_944_ = lean_ctor_get(v_decl_937_, 1);
v_type_945_ = lean_ctor_get(v_decl_937_, 2);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_decl_937_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_decl_937_, 3);
lean_dec(v_unused_1013_);
v___x_947_ = v_decl_937_;
v_isShared_948_ = v_isSharedCheck_1012_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_type_945_);
lean_inc(v_binderName_944_);
lean_inc(v_fvarId_943_);
lean_dec(v_decl_937_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1012_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_us_949_; lean_object* v_args_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1010_; 
v_us_949_ = lean_ctor_get(v_value_938_, 1);
v_args_950_ = lean_ctor_get(v_value_938_, 2);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_value_938_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_value_938_, 0);
lean_dec(v_unused_1011_);
v___x_952_ = v_value_938_;
v_isShared_953_ = v_isSharedCheck_1010_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_args_950_);
lean_inc(v_us_949_);
lean_dec(v_value_938_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1010_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_str_954_; lean_object* v_str_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_str_954_ = lean_ctor_get(v_declName_939_, 1);
lean_inc_ref(v_str_954_);
lean_dec_ref(v_declName_939_);
v_str_955_ = lean_ctor_get(v_pre_940_, 1);
lean_inc_ref(v_str_955_);
lean_dec_ref(v_pre_940_);
v___x_956_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2));
v___x_957_ = lean_string_dec_eq(v_str_955_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; uint8_t v___x_959_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3));
v___x_959_ = lean_string_dec_eq(v_str_955_, v___x_958_);
lean_dec_ref(v_str_955_);
if (v___x_959_ == 0)
{
lean_dec_ref(v_str_954_);
lean_del_object(v___x_952_);
lean_dec_ref(v_args_950_);
lean_dec(v_us_949_);
lean_del_object(v___x_947_);
lean_dec_ref(v_type_945_);
lean_dec(v_binderName_944_);
lean_dec(v_fvarId_943_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
else
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_961_ = lean_string_dec_eq(v_str_954_, v___x_960_);
lean_dec_ref(v_str_954_);
if (v___x_961_ == 0)
{
lean_del_object(v___x_952_);
lean_dec_ref(v_args_950_);
lean_dec(v_us_949_);
lean_del_object(v___x_947_);
lean_dec_ref(v_type_945_);
lean_dec(v_binderName_944_);
lean_dec(v_fvarId_943_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
else
{
lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_962_ = lean_array_get_size(v_args_950_);
v___x_963_ = lean_nat_dec_eq(v___x_962_, v___x_904_);
if (v___x_963_ == 0)
{
lean_del_object(v___x_952_);
lean_dec_ref(v_args_950_);
lean_dec(v_us_949_);
lean_del_object(v___x_947_);
lean_dec_ref(v_type_945_);
lean_dec(v_binderName_944_);
lean_dec(v_fvarId_943_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
else
{
lean_object* v___x_964_; 
v___x_964_ = lean_array_fget(v_args_950_, v_zero_885_);
lean_dec_ref(v_args_950_);
if (lean_obj_tag(v___x_964_) == 1)
{
lean_object* v_fvarId_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_984_; 
v_fvarId_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_984_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_984_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_fvarId_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_984_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
uint8_t v___x_969_; 
v___x_969_ = l_Lean_instBEqFVarId_beq(v_fvarId_965_, v_fvarId_893_);
if (v___x_969_ == 0)
{
lean_del_object(v___x_967_);
lean_dec(v_fvarId_965_);
lean_del_object(v___x_952_);
lean_dec(v_us_949_);
lean_del_object(v___x_947_);
lean_dec_ref(v_type_945_);
lean_dec(v_binderName_944_);
lean_dec(v_fvarId_943_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
lean_inc_ref(v_k_942_);
lean_inc(v_fvarId_893_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
v___x_970_ = l_Lean_Name_str___override(v_pre_941_, v___x_958_);
v___x_971_ = l_Lean_Name_str___override(v___x_970_, v___x_960_);
if (v_isShared_968_ == 0)
{
v___x_973_ = v___x_967_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_fvarId_965_);
v___x_973_ = v_reuseFailAlloc_983_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_974_ = lean_mk_empty_array_with_capacity(v___x_904_);
v___x_975_ = lean_array_push(v___x_974_, v___x_973_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 2, v___x_975_);
lean_ctor_set(v___x_952_, 0, v___x_971_);
v___x_977_ = v___x_952_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v_us_949_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v___x_975_);
v___x_977_ = v_reuseFailAlloc_982_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_979_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 3, v___x_977_);
v___x_979_ = v___x_947_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_fvarId_943_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_binderName_944_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_type_945_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v___x_977_);
v___x_979_ = v_reuseFailAlloc_981_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_FVarIdSet_insert(v_illegalSet_862_, v_fvarId_893_);
v_decl_875_ = v___x_979_;
v_k_876_ = v_k_942_;
v_illegalSet_877_ = v___x_980_;
goto v___jp_874_;
}
}
}
}
}
}
else
{
lean_dec(v___x_964_);
lean_del_object(v___x_952_);
lean_dec(v_us_949_);
lean_del_object(v___x_947_);
lean_dec_ref(v_type_945_);
lean_dec(v_binderName_944_);
lean_dec(v_fvarId_943_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
}
}
}
}
else
{
lean_object* v___x_985_; uint8_t v___x_986_; 
lean_dec_ref(v_str_955_);
v___x_985_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_986_ = lean_string_dec_eq(v_str_954_, v___x_985_);
lean_dec_ref(v_str_954_);
if (v___x_986_ == 0)
{
lean_del_object(v___x_952_);
lean_dec_ref(v_args_950_);
lean_dec(v_us_949_);
lean_del_object(v___x_947_);
lean_dec_ref(v_type_945_);
lean_dec(v_binderName_944_);
lean_dec(v_fvarId_943_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
else
{
lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = lean_array_get_size(v_args_950_);
v___x_988_ = lean_nat_dec_eq(v___x_987_, v___x_904_);
if (v___x_988_ == 0)
{
lean_del_object(v___x_952_);
lean_dec_ref(v_args_950_);
lean_dec(v_us_949_);
lean_del_object(v___x_947_);
lean_dec_ref(v_type_945_);
lean_dec(v_binderName_944_);
lean_dec(v_fvarId_943_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_array_fget(v_args_950_, v_zero_885_);
lean_dec_ref(v_args_950_);
if (lean_obj_tag(v___x_989_) == 1)
{
lean_object* v_fvarId_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1009_; 
v_fvarId_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1009_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_fvarId_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1009_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___x_994_; 
v___x_994_ = l_Lean_instBEqFVarId_beq(v_fvarId_990_, v_fvarId_893_);
if (v___x_994_ == 0)
{
lean_del_object(v___x_992_);
lean_dec(v_fvarId_990_);
lean_del_object(v___x_952_);
lean_dec(v_us_949_);
lean_del_object(v___x_947_);
lean_dec_ref(v_type_945_);
lean_dec(v_binderName_944_);
lean_dec(v_fvarId_943_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
lean_inc_ref(v_k_942_);
lean_inc(v_fvarId_893_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
v___x_995_ = l_Lean_Name_str___override(v_pre_941_, v___x_956_);
v___x_996_ = l_Lean_Name_str___override(v___x_995_, v___x_985_);
if (v_isShared_993_ == 0)
{
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_fvarId_990_);
v___x_998_ = v_reuseFailAlloc_1008_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_999_ = lean_mk_empty_array_with_capacity(v___x_904_);
v___x_1000_ = lean_array_push(v___x_999_, v___x_998_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 2, v___x_1000_);
lean_ctor_set(v___x_952_, 0, v___x_996_);
v___x_1002_ = v___x_952_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_us_949_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 3, v___x_1002_);
v___x_1004_ = v___x_947_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_fvarId_943_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_binderName_944_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_type_945_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_FVarIdSet_insert(v_illegalSet_862_, v_fvarId_893_);
v_decl_875_ = v___x_1004_;
v_k_876_ = v_k_942_;
v_illegalSet_877_ = v___x_1005_;
goto v___jp_874_;
}
}
}
}
}
}
else
{
lean_dec(v___x_989_);
lean_del_object(v___x_952_);
lean_dec(v_us_949_);
lean_del_object(v___x_947_);
lean_dec_ref(v_type_945_);
lean_dec(v_binderName_944_);
lean_dec(v_fvarId_943_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
}
}
}
}
}
}
else
{
lean_dec(v_pre_941_);
lean_dec_ref(v_pre_940_);
lean_dec_ref(v_declName_939_);
lean_dec_ref(v_value_938_);
lean_dec_ref(v_decl_937_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
}
else
{
lean_dec_ref(v_declName_939_);
lean_dec(v_pre_940_);
lean_dec_ref(v_value_938_);
lean_dec_ref(v_decl_937_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
}
else
{
lean_dec(v_declName_939_);
lean_dec_ref(v_value_938_);
lean_dec_ref(v_decl_937_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
}
else
{
lean_dec(v_value_938_);
lean_dec_ref(v_decl_937_);
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
}
else
{
v_decl_875_ = v_decl_860_;
v_k_876_ = v_k_861_;
v_illegalSet_877_ = v_illegalSet_862_;
goto v___jp_874_;
}
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
v_a_1015_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_917_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_917_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
}
else
{
lean_dec(v___x_905_);
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
lean_dec(v_prevArrayId_859_);
goto v___jp_871_;
}
}
}
}
}
else
{
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
lean_dec(v_prevArrayId_859_);
goto v___jp_871_;
}
}
else
{
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
lean_dec(v_prevArrayId_859_);
goto v___jp_871_;
}
}
else
{
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
lean_dec(v_prevArrayId_859_);
goto v___jp_871_;
}
}
else
{
lean_dec(v_size_863_);
lean_dec(v_illegalSet_862_);
lean_dec_ref(v_k_861_);
lean_dec_ref(v_decl_860_);
lean_dec(v_prevArrayId_859_);
goto v___jp_871_;
}
}
v___jp_871_:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_box(0);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
v___jp_874_:
{
uint8_t v___x_878_; uint8_t v___x_879_; 
v___x_878_ = 0;
v___x_879_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_878_, v_k_876_, v_illegalSet_877_);
lean_dec(v_illegalSet_877_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_decl_875_);
lean_ctor_set(v___x_880_, 1, v_k_876_);
v___x_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec_ref(v_k_876_);
lean_dec_ref(v_decl_875_);
v___x_883_ = lean_box(0);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___boxed(lean_object* v_prevArrayId_1024_, lean_object* v_decl_1025_, lean_object* v_k_1026_, lean_object* v_illegalSet_1027_, lean_object* v_size_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_prevArrayId_1024_, v_decl_1025_, v_k_1026_, v_illegalSet_1027_, v_size_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(lean_object* v_decl_1039_, lean_object* v_k_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_value_1057_; 
v_value_1057_ = lean_ctor_get(v_decl_1039_, 3);
if (lean_obj_tag(v_value_1057_) == 3)
{
lean_object* v_declName_1058_; 
v_declName_1058_ = lean_ctor_get(v_value_1057_, 0);
if (lean_obj_tag(v_declName_1058_) == 1)
{
lean_object* v_pre_1059_; 
v_pre_1059_ = lean_ctor_get(v_declName_1058_, 0);
if (lean_obj_tag(v_pre_1059_) == 1)
{
lean_object* v_pre_1060_; 
v_pre_1060_ = lean_ctor_get(v_pre_1059_, 0);
if (lean_obj_tag(v_pre_1060_) == 0)
{
lean_object* v_args_1061_; lean_object* v_str_1062_; lean_object* v_str_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_args_1061_ = lean_ctor_get(v_value_1057_, 2);
v_str_1062_ = lean_ctor_get(v_declName_1058_, 1);
v_str_1063_ = lean_ctor_get(v_pre_1059_, 1);
v___x_1064_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1065_ = lean_string_dec_eq(v_str_1063_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1054_;
}
else
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_1067_ = lean_string_dec_eq(v_str_1062_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1054_;
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1068_ = lean_array_get_size(v_args_1061_);
v___x_1069_ = lean_unsigned_to_nat(3u);
v___x_1070_ = lean_nat_dec_eq(v___x_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1054_;
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_unsigned_to_nat(1u);
v___x_1072_ = lean_array_fget_borrowed(v_args_1061_, v___x_1071_);
if (lean_obj_tag(v___x_1072_) == 1)
{
lean_object* v_fvarId_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; 
v_fvarId_1073_ = lean_ctor_get(v___x_1072_, 0);
v___x_1074_ = 0;
v___x_1075_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_1074_, v_fvarId_1073_, v_a_1044_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1131_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1131_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1131_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
if (lean_obj_tag(v_a_1076_) == 1)
{
lean_object* v_val_1080_; lean_object* v_value_1081_; 
lean_del_object(v___x_1078_);
v_val_1080_ = lean_ctor_get(v_a_1076_, 0);
lean_inc(v_val_1080_);
lean_dec_ref(v_a_1076_);
v_value_1081_ = lean_ctor_get(v_val_1080_, 3);
lean_inc(v_value_1081_);
if (lean_obj_tag(v_value_1081_) == 3)
{
lean_object* v_declName_1082_; 
v_declName_1082_ = lean_ctor_get(v_value_1081_, 0);
lean_inc(v_declName_1082_);
if (lean_obj_tag(v_declName_1082_) == 1)
{
lean_object* v_pre_1083_; 
v_pre_1083_ = lean_ctor_get(v_declName_1082_, 0);
lean_inc(v_pre_1083_);
if (lean_obj_tag(v_pre_1083_) == 1)
{
lean_object* v_pre_1084_; 
v_pre_1084_ = lean_ctor_get(v_pre_1083_, 0);
if (lean_obj_tag(v_pre_1084_) == 0)
{
lean_object* v_fvarId_1085_; lean_object* v_args_1086_; lean_object* v_str_1087_; lean_object* v_str_1088_; uint8_t v___x_1089_; 
v_fvarId_1085_ = lean_ctor_get(v_val_1080_, 0);
lean_inc(v_fvarId_1085_);
lean_dec(v_val_1080_);
v_args_1086_ = lean_ctor_get(v_value_1081_, 2);
lean_inc_ref(v_args_1086_);
lean_dec_ref(v_value_1081_);
v_str_1087_ = lean_ctor_get(v_declName_1082_, 1);
lean_inc_ref(v_str_1087_);
lean_dec_ref(v_declName_1082_);
v_str_1088_ = lean_ctor_get(v_pre_1083_, 1);
lean_inc_ref(v_str_1088_);
lean_dec_ref(v_pre_1083_);
v___x_1089_ = lean_string_dec_eq(v_str_1088_, v___x_1064_);
lean_dec_ref(v_str_1088_);
if (v___x_1089_ == 0)
{
lean_dec_ref(v_str_1087_);
lean_dec_ref(v_args_1086_);
lean_dec(v_fvarId_1085_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1051_;
}
else
{
lean_object* v___x_1090_; lean_object* v_sizeFVar_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1090_ = lean_box(1);
v___x_1113_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1114_ = lean_string_dec_eq(v_str_1087_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1116_ = lean_string_dec_eq(v_str_1087_, v___x_1115_);
lean_dec_ref(v_str_1087_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v_args_1086_);
lean_dec(v_fvarId_1085_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1051_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1117_ = lean_array_get_size(v_args_1086_);
v___x_1118_ = lean_unsigned_to_nat(2u);
v___x_1119_ = lean_nat_dec_eq(v___x_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec_ref(v_args_1086_);
lean_dec(v_fvarId_1085_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1051_;
}
else
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_array_fget(v_args_1086_, v___x_1071_);
lean_dec_ref(v_args_1086_);
if (lean_obj_tag(v___x_1120_) == 1)
{
lean_object* v_fvarId_1121_; 
v_fvarId_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_fvarId_1121_);
lean_dec_ref(v___x_1120_);
v_sizeFVar_1092_ = v_fvarId_1121_;
v___y_1093_ = v_a_1041_;
v___y_1094_ = v_a_1042_;
v___y_1095_ = v_a_1043_;
v___y_1096_ = v_a_1044_;
v___y_1097_ = v_a_1045_;
v___y_1098_ = v_a_1046_;
goto v___jp_1091_;
}
else
{
lean_dec(v___x_1120_);
lean_dec(v_fvarId_1085_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1051_;
}
}
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
lean_dec_ref(v_str_1087_);
v___x_1122_ = lean_array_get_size(v_args_1086_);
v___x_1123_ = lean_unsigned_to_nat(2u);
v___x_1124_ = lean_nat_dec_eq(v___x_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_dec_ref(v_args_1086_);
lean_dec(v_fvarId_1085_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1051_;
}
else
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_array_fget(v_args_1086_, v___x_1071_);
lean_dec_ref(v_args_1086_);
if (lean_obj_tag(v___x_1125_) == 1)
{
lean_object* v_fvarId_1126_; 
v_fvarId_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_fvarId_1126_);
lean_dec_ref(v___x_1125_);
v_sizeFVar_1092_ = v_fvarId_1126_;
v___y_1093_ = v_a_1041_;
v___y_1094_ = v_a_1042_;
v___y_1095_ = v_a_1043_;
v___y_1096_ = v_a_1044_;
v___y_1097_ = v_a_1045_;
v___y_1098_ = v_a_1046_;
goto v___jp_1091_;
}
else
{
lean_dec(v___x_1125_);
lean_dec(v_fvarId_1085_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1051_;
}
}
}
v___jp_1091_:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1074_, v_sizeFVar_1092_, v___y_1096_);
lean_dec(v_sizeFVar_1092_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref(v___x_1099_);
if (lean_obj_tag(v_a_1100_) == 1)
{
lean_object* v_val_1101_; 
v_val_1101_ = lean_ctor_get(v_a_1100_, 0);
lean_inc(v_val_1101_);
lean_dec_ref(v_a_1100_);
if (lean_obj_tag(v_val_1101_) == 0)
{
lean_object* v_value_1102_; 
v_value_1102_ = lean_ctor_get(v_val_1101_, 0);
lean_inc_ref(v_value_1102_);
lean_dec_ref(v_val_1101_);
if (lean_obj_tag(v_value_1102_) == 0)
{
lean_object* v_val_1103_; lean_object* v___x_1104_; 
v_val_1103_ = lean_ctor_get(v_value_1102_, 0);
lean_inc(v_val_1103_);
lean_dec_ref(v_value_1102_);
v___x_1104_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_fvarId_1085_, v_decl_1039_, v_k_1040_, v___x_1090_, v_val_1103_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
return v___x_1104_;
}
else
{
lean_dec_ref(v_value_1102_);
lean_dec(v_fvarId_1085_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1048_;
}
}
else
{
lean_dec(v_val_1101_);
lean_dec(v_fvarId_1085_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1048_;
}
}
else
{
lean_dec(v_a_1100_);
lean_dec(v_fvarId_1085_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1048_;
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v_fvarId_1085_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
v_a_1105_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1099_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1099_);
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
}
}
else
{
lean_dec_ref(v_pre_1083_);
lean_dec_ref(v_declName_1082_);
lean_dec_ref(v_value_1081_);
lean_dec(v_val_1080_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1051_;
}
}
else
{
lean_dec(v_pre_1083_);
lean_dec_ref(v_declName_1082_);
lean_dec_ref(v_value_1081_);
lean_dec(v_val_1080_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1051_;
}
}
else
{
lean_dec(v_declName_1082_);
lean_dec_ref(v_value_1081_);
lean_dec(v_val_1080_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1051_;
}
}
else
{
lean_dec(v_value_1081_);
lean_dec(v_val_1080_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1051_;
}
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
lean_dec(v_a_1076_);
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
v___x_1127_ = lean_box(0);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1127_);
v___x_1129_ = v___x_1078_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
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
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
v_a_1132_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1075_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1075_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
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
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1054_;
}
}
}
}
}
else
{
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1054_;
}
}
else
{
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1054_;
}
}
else
{
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1054_;
}
}
else
{
lean_dec_ref(v_k_1040_);
lean_dec_ref(v_decl_1039_);
goto v___jp_1054_;
}
v___jp_1048_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
return v___x_1050_;
}
v___jp_1051_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
v___jp_1054_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_box(0);
v___x_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
return v___x_1056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___boxed(lean_object* v_decl_1140_, lean_object* v_k_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1140_, v_k_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
return v_res_1149_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0);
v___x_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(lean_object* v_env_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; lean_object* v_nextMacroScope_1159_; lean_object* v_ngen_1160_; lean_object* v_auxDeclNGen_1161_; lean_object* v_traceState_1162_; lean_object* v_messages_1163_; lean_object* v_infoState_1164_; lean_object* v_snapshotTasks_1165_; lean_object* v_newDecls_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1177_; 
v___x_1158_ = lean_st_ref_take(v___y_1156_);
v_nextMacroScope_1159_ = lean_ctor_get(v___x_1158_, 1);
v_ngen_1160_ = lean_ctor_get(v___x_1158_, 2);
v_auxDeclNGen_1161_ = lean_ctor_get(v___x_1158_, 3);
v_traceState_1162_ = lean_ctor_get(v___x_1158_, 4);
v_messages_1163_ = lean_ctor_get(v___x_1158_, 6);
v_infoState_1164_ = lean_ctor_get(v___x_1158_, 7);
v_snapshotTasks_1165_ = lean_ctor_get(v___x_1158_, 8);
v_newDecls_1166_ = lean_ctor_get(v___x_1158_, 9);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1177_ == 0)
{
lean_object* v_unused_1178_; lean_object* v_unused_1179_; 
v_unused_1178_ = lean_ctor_get(v___x_1158_, 5);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v___x_1158_, 0);
lean_dec(v_unused_1179_);
v___x_1168_ = v___x_1158_;
v_isShared_1169_ = v_isSharedCheck_1177_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_newDecls_1166_);
lean_inc(v_snapshotTasks_1165_);
lean_inc(v_infoState_1164_);
lean_inc(v_messages_1163_);
lean_inc(v_traceState_1162_);
lean_inc(v_auxDeclNGen_1161_);
lean_inc(v_ngen_1160_);
lean_inc(v_nextMacroScope_1159_);
lean_dec(v___x_1158_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1177_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 5, v___x_1170_);
lean_ctor_set(v___x_1168_, 0, v_env_1155_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_env_1155_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_nextMacroScope_1159_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_ngen_1160_);
lean_ctor_set(v_reuseFailAlloc_1176_, 3, v_auxDeclNGen_1161_);
lean_ctor_set(v_reuseFailAlloc_1176_, 4, v_traceState_1162_);
lean_ctor_set(v_reuseFailAlloc_1176_, 5, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1176_, 6, v_messages_1163_);
lean_ctor_set(v_reuseFailAlloc_1176_, 7, v_infoState_1164_);
lean_ctor_set(v_reuseFailAlloc_1176_, 8, v_snapshotTasks_1165_);
lean_ctor_set(v_reuseFailAlloc_1176_, 9, v_newDecls_1166_);
v___x_1172_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_st_ref_set(v___y_1156_, v___x_1172_);
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___boxed(lean_object* v_env_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1180_, v___y_1181_);
lean_dec(v___y_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(lean_object* v_env_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1184_, v___y_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(lean_object* v_env_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_env_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(size_t v_sz_1202_, size_t v_i_1203_, lean_object* v_bs_1204_, uint8_t v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_usize_dec_lt(v_i_1203_, v_sz_1202_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_bs_1204_);
return v___x_1213_;
}
else
{
uint8_t v___x_1214_; lean_object* v_v_1215_; lean_object* v___x_1216_; 
v___x_1214_ = 0;
v_v_1215_ = lean_array_uget_borrowed(v_bs_1204_, v_i_1203_);
lean_inc(v_v_1215_);
v___x_1216_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_1214_, v_v_1215_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1218_; lean_object* v_bs_x27_1219_; size_t v___x_1220_; size_t v___x_1221_; lean_object* v___x_1222_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref(v___x_1216_);
v___x_1218_ = lean_unsigned_to_nat(0u);
v_bs_x27_1219_ = lean_array_uset(v_bs_1204_, v_i_1203_, v___x_1218_);
v___x_1220_ = ((size_t)1ULL);
v___x_1221_ = lean_usize_add(v_i_1203_, v___x_1220_);
v___x_1222_ = lean_array_uset(v_bs_x27_1219_, v_i_1203_, v_a_1217_);
v_i_1203_ = v___x_1221_;
v_bs_1204_ = v___x_1222_;
goto _start;
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref(v_bs_1204_);
v_a_1224_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1216_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1216_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(lean_object* v_sz_1232_, lean_object* v_i_1233_, lean_object* v_bs_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
size_t v_sz_boxed_1242_; size_t v_i_boxed_1243_; uint8_t v___y_8215__boxed_1244_; lean_object* v_res_1245_; 
v_sz_boxed_1242_ = lean_unbox_usize(v_sz_1232_);
lean_dec(v_sz_1232_);
v_i_boxed_1243_ = lean_unbox_usize(v_i_1233_);
lean_dec(v_i_1233_);
v___y_8215__boxed_1244_ = lean_unbox(v___y_1235_);
v_res_1245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_boxed_1242_, v_i_boxed_1243_, v_bs_1234_, v___y_8215__boxed_1244_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
return v_res_1245_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_box(0);
v___x_1249_ = lean_unsigned_to_nat(16u);
v___x_1250_ = lean_mk_array(v___x_1249_, v___x_1248_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1);
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___x_1251_);
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3(void){
_start:
{
uint8_t v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = 0;
v___x_1255_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(lean_object* v_decl_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_type_1274_; lean_object* v_value_1275_; lean_object* v___x_1276_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0));
v___x_1273_ = lean_st_mk_ref(v___x_1272_);
v_type_1274_ = lean_ctor_get(v_decl_1264_, 2);
lean_inc_ref(v_type_1274_);
v_value_1275_ = lean_ctor_get(v_decl_1264_, 3);
lean_inc(v_value_1275_);
v___x_1276_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_1275_, v___x_1273_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; lean_object* v_a_1287_; size_t v_sz_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
lean_dec_ref(v___x_1276_);
v___x_1277_ = lean_st_ref_get(v___x_1273_);
lean_dec(v___x_1273_);
v___x_1278_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_1279_ = lean_st_mk_ref(v___x_1278_);
v___x_1280_ = 0;
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_decl_1264_);
v___x_1282_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3);
v___x_1283_ = l_Array_reverse___redArg(v___x_1277_);
v___x_1284_ = lean_array_push(v___x_1283_, v___x_1281_);
v___x_1285_ = 0;
v_sz_1369_ = lean_array_size(v___x_1284_);
v___x_1370_ = ((size_t)0ULL);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_1369_, v___x_1370_, v___x_1284_, v___x_1285_, v___x_1279_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1373_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = lean_st_ref_get(v___x_1279_);
lean_dec(v___x_1279_);
lean_dec(v___x_1373_);
v_a_1287_ = v_a_1372_;
goto v___jp_1286_;
}
else
{
lean_dec(v___x_1279_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1374_; 
v_a_1374_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1371_);
v_a_1287_ = v_a_1374_;
goto v___jp_1286_;
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec_ref(v_type_1274_);
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
v___jp_1286_:
{
lean_object* v___x_1288_; lean_object* v_env_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1288_ = lean_st_ref_get(v_a_1270_);
v_env_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc_ref_n(v_env_1289_, 2);
lean_dec(v___x_1288_);
v___x_1290_ = lean_array_get_size(v_a_1287_);
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_nat_sub(v___x_1290_, v___x_1291_);
v___x_1293_ = lean_array_get_borrowed(v___x_1282_, v_a_1287_, v___x_1292_);
lean_dec(v___x_1292_);
v___x_1294_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1293_);
v___x_1295_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
v___x_1296_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1280_, v_a_1287_, v___x_1295_);
lean_dec_ref(v_a_1287_);
v___x_1297_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4));
lean_inc_ref(v___x_1296_);
v___x_1298_ = l_Lean_Compiler_LCNF_Code_toExpr(v___x_1280_, v___x_1296_, v___x_1297_);
v___x_1299_ = l_Lean_getClosedTermName_x3f(v_env_1289_, v___x_1298_);
if (lean_obj_tag(v___x_1299_) == 1)
{
lean_object* v_val_1300_; lean_object* v___x_1301_; 
lean_dec_ref(v___x_1298_);
lean_dec_ref(v_env_1289_);
lean_dec_ref(v_type_1274_);
v_val_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_val_1300_);
lean_dec_ref(v___x_1299_);
v___x_1301_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1280_, v___x_1296_, v_a_1268_);
lean_dec_ref(v___x_1296_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; 
v_unused_1309_ = lean_ctor_get(v___x_1301_, 0);
lean_dec(v_unused_1309_);
v___x_1303_ = v___x_1301_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_dec(v___x_1301_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v_val_1300_);
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_val_1300_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec(v_val_1300_);
v_a_1310_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1301_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1301_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
else
{
lean_object* v___x_1318_; lean_object* v_baseName_1319_; lean_object* v_decls_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v___x_1299_);
v___x_1318_ = lean_st_ref_get(v_a_1266_);
v_baseName_1319_ = lean_ctor_get(v_a_1265_, 0);
v_decls_1320_ = lean_ctor_get(v___x_1318_, 0);
lean_inc_ref(v_decls_1320_);
lean_dec(v___x_1318_);
v___x_1321_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6));
v___x_1322_ = lean_array_get_size(v_decls_1320_);
lean_dec_ref(v_decls_1320_);
v___x_1323_ = lean_name_append_index_after(v___x_1321_, v___x_1322_);
lean_inc(v_baseName_1319_);
v___x_1324_ = l_Lean_Name_append(v_baseName_1319_, v___x_1323_);
lean_inc(v___x_1324_);
v___x_1325_ = l_Lean_cacheClosedTermName(v_env_1289_, v___x_1298_, v___x_1324_);
v___x_1326_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v___x_1325_, v_a_1270_);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v___x_1326_, 0);
lean_dec(v_unused_1368_);
v___x_1328_ = v___x_1326_;
v_isShared_1329_ = v_isSharedCheck_1367_;
goto v_resetjp_1327_;
}
else
{
lean_dec(v___x_1326_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1367_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = 1;
lean_inc(v___x_1324_);
v___x_1332_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1332_, 0, v___x_1324_);
lean_ctor_set(v___x_1332_, 1, v___x_1330_);
lean_ctor_set(v___x_1332_, 2, v_type_1274_);
lean_ctor_set(v___x_1332_, 3, v___x_1297_);
lean_ctor_set_uint8(v___x_1332_, sizeof(void*)*4, v___x_1331_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1296_);
v___x_1334_ = v___x_1328_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1296_);
v___x_1334_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7));
v___x_1336_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1336_, 0, v___x_1332_);
lean_ctor_set(v___x_1336_, 1, v___x_1334_);
lean_ctor_set(v___x_1336_, 2, v___x_1335_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*3, v___x_1285_);
lean_inc_ref(v___x_1336_);
v___x_1337_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1336_, v_a_1270_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1356_; 
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; 
v_unused_1357_ = lean_ctor_get(v___x_1337_, 0);
lean_dec(v_unused_1357_);
v___x_1339_ = v___x_1337_;
v_isShared_1340_ = v_isSharedCheck_1356_;
goto v_resetjp_1338_;
}
else
{
lean_dec(v___x_1337_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1356_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v_decls_1342_; lean_object* v_fvarDecisionCache_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1355_; 
v___x_1341_ = lean_st_ref_take(v_a_1266_);
v_decls_1342_ = lean_ctor_get(v___x_1341_, 0);
v_fvarDecisionCache_1343_ = lean_ctor_get(v___x_1341_, 1);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1345_ = v___x_1341_;
v_isShared_1346_ = v_isSharedCheck_1355_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_fvarDecisionCache_1343_);
lean_inc(v_decls_1342_);
lean_dec(v___x_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1355_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_array_push(v_decls_1342_, v___x_1336_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_fvarDecisionCache_1343_);
v___x_1349_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = lean_st_ref_set(v_a_1266_, v___x_1349_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1324_);
v___x_1352_ = v___x_1339_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1324_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v___x_1336_);
lean_dec(v___x_1324_);
v_a_1358_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1337_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1337_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
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
lean_dec_ref(v_type_1274_);
lean_dec(v___x_1273_);
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
uint8_t v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = 0;
v___x_1401_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(lean_object* v_msg_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0);
v___x_1404_ = lean_panic_fn_borrowed(v___x_1403_, v_msg_1402_);
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1408_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2));
v___x_1409_ = lean_unsigned_to_nat(9u);
v___x_1410_ = lean_unsigned_to_nat(640u);
v___x_1411_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1));
v___x_1412_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0));
v___x_1413_ = l_mkPanicMessageWithDecl(v___x_1412_, v___x_1411_, v___x_1410_, v___x_1409_, v___x_1408_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* v_code_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___y_1425_; lean_object* v___y_1426_; uint8_t v___y_1427_; lean_object* v___y_1432_; lean_object* v___y_1433_; uint8_t v___y_1434_; lean_object* v_decl_1439_; lean_object* v_k_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1493_; lean_object* v___y_1494_; uint8_t v___y_1495_; lean_object* v___y_1500_; lean_object* v___y_1501_; uint8_t v___y_1502_; lean_object* v___y_1507_; lean_object* v___y_1508_; uint8_t v___y_1509_; lean_object* v___y_1514_; lean_object* v___y_1515_; uint8_t v___y_1516_; lean_object* v___y_1521_; lean_object* v___y_1522_; uint8_t v___y_1523_; 
switch(lean_obj_tag(v_code_1416_))
{
case 0:
{
lean_object* v_decl_1527_; lean_object* v_k_1528_; lean_object* v___y_1530_; uint8_t v___y_1531_; lean_object* v___y_1544_; uint8_t v___y_1545_; lean_object* v___y_1558_; uint8_t v___y_1559_; lean_object* v_value_1571_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; 
v_decl_1527_ = lean_ctor_get(v_code_1416_, 0);
v_k_1528_ = lean_ctor_get(v_code_1416_, 1);
v_value_1571_ = lean_ctor_get(v_decl_1527_, 3);
lean_inc(v_value_1571_);
if (lean_obj_tag(v_value_1571_) == 3)
{
lean_object* v_declName_1675_; 
v_declName_1675_ = lean_ctor_get(v_value_1571_, 0);
if (lean_obj_tag(v_declName_1675_) == 1)
{
lean_object* v_pre_1676_; 
v_pre_1676_ = lean_ctor_get(v_declName_1675_, 0);
if (lean_obj_tag(v_pre_1676_) == 1)
{
lean_object* v_pre_1677_; 
v_pre_1677_ = lean_ctor_get(v_pre_1676_, 0);
if (lean_obj_tag(v_pre_1677_) == 0)
{
lean_object* v_args_1678_; lean_object* v_str_1679_; lean_object* v_str_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v_sizeId_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; 
v_args_1678_ = lean_ctor_get(v_value_1571_, 2);
v_str_1679_ = lean_ctor_get(v_declName_1675_, 1);
v_str_1680_ = lean_ctor_get(v_pre_1676_, 1);
v___x_1681_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1682_ = lean_string_dec_eq(v_str_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
v___y_1573_ = v_a_1417_;
v___y_1574_ = v_a_1418_;
v___y_1575_ = v_a_1419_;
v___y_1576_ = v_a_1420_;
v___y_1577_ = v_a_1421_;
v___y_1578_ = v_a_1422_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1866_ = lean_string_dec_eq(v_str_1679_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1868_ = lean_string_dec_eq(v_str_1679_, v___x_1867_);
if (v___x_1868_ == 0)
{
v___y_1573_ = v_a_1417_;
v___y_1574_ = v_a_1418_;
v___y_1575_ = v_a_1419_;
v___y_1576_ = v_a_1420_;
v___y_1577_ = v_a_1421_;
v___y_1578_ = v_a_1422_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1869_ = lean_array_get_size(v_args_1678_);
v___x_1870_ = lean_unsigned_to_nat(2u);
v___x_1871_ = lean_nat_dec_eq(v___x_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
v___y_1573_ = v_a_1417_;
v___y_1574_ = v_a_1418_;
v___y_1575_ = v_a_1419_;
v___y_1576_ = v_a_1420_;
v___y_1577_ = v_a_1421_;
v___y_1578_ = v_a_1422_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = lean_array_fget_borrowed(v_args_1678_, v___x_1872_);
if (lean_obj_tag(v___x_1873_) == 1)
{
lean_object* v_fvarId_1874_; 
v_fvarId_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_fvarId_1874_);
v_sizeId_1795_ = v_fvarId_1874_;
v___y_1796_ = v_a_1417_;
v___y_1797_ = v_a_1418_;
v___y_1798_ = v_a_1419_;
v___y_1799_ = v_a_1420_;
v___y_1800_ = v_a_1421_;
v___y_1801_ = v_a_1422_;
goto v___jp_1794_;
}
else
{
v___y_1573_ = v_a_1417_;
v___y_1574_ = v_a_1418_;
v___y_1575_ = v_a_1419_;
v___y_1576_ = v_a_1420_;
v___y_1577_ = v_a_1421_;
v___y_1578_ = v_a_1422_;
goto v___jp_1572_;
}
}
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1875_ = lean_array_get_size(v_args_1678_);
v___x_1876_ = lean_unsigned_to_nat(2u);
v___x_1877_ = lean_nat_dec_eq(v___x_1875_, v___x_1876_);
if (v___x_1877_ == 0)
{
v___y_1573_ = v_a_1417_;
v___y_1574_ = v_a_1418_;
v___y_1575_ = v_a_1419_;
v___y_1576_ = v_a_1420_;
v___y_1577_ = v_a_1421_;
v___y_1578_ = v_a_1422_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = lean_array_fget_borrowed(v_args_1678_, v___x_1878_);
if (lean_obj_tag(v___x_1879_) == 1)
{
lean_object* v_fvarId_1880_; 
v_fvarId_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_fvarId_1880_);
v_sizeId_1795_ = v_fvarId_1880_;
v___y_1796_ = v_a_1417_;
v___y_1797_ = v_a_1418_;
v___y_1798_ = v_a_1419_;
v___y_1799_ = v_a_1420_;
v___y_1800_ = v_a_1421_;
v___y_1801_ = v_a_1422_;
goto v___jp_1794_;
}
else
{
v___y_1573_ = v_a_1417_;
v___y_1574_ = v_a_1418_;
v___y_1575_ = v_a_1419_;
v___y_1576_ = v_a_1420_;
v___y_1577_ = v_a_1421_;
v___y_1578_ = v_a_1422_;
goto v___jp_1572_;
}
}
}
}
v___jp_1683_:
{
lean_object* v___x_1690_; 
lean_inc_ref(v_k_1528_);
lean_inc_ref(v_decl_1527_);
v___x_1690_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1527_, v_k_1528_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1690_);
if (lean_obj_tag(v_a_1691_) == 1)
{
lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1732_; 
v_isSharedCheck_1732_ = !lean_is_exclusive(v_value_1571_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; lean_object* v_unused_1734_; lean_object* v_unused_1735_; 
v_unused_1733_ = lean_ctor_get(v_value_1571_, 2);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_value_1571_, 1);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_value_1571_, 0);
lean_dec(v_unused_1735_);
v___x_1693_ = v_value_1571_;
v_isShared_1694_ = v_isSharedCheck_1732_;
goto v_resetjp_1692_;
}
else
{
lean_dec(v_value_1571_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1732_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_val_1695_; lean_object* v_fst_1696_; lean_object* v_snd_1697_; lean_object* v___x_1698_; 
v_val_1695_ = lean_ctor_get(v_a_1691_, 0);
lean_inc(v_val_1695_);
lean_dec_ref(v_a_1691_);
v_fst_1696_ = lean_ctor_get(v_val_1695_, 0);
lean_inc_n(v_fst_1696_, 2);
v_snd_1697_ = lean_ctor_get(v_val_1695_, 1);
lean_inc(v_snd_1697_);
lean_dec(v_val_1695_);
v___x_1698_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1696_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; uint8_t v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref(v___x_1698_);
v___x_1700_ = 0;
v___x_1701_ = lean_box(0);
v___x_1702_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 2, v___x_1702_);
lean_ctor_set(v___x_1693_, 1, v___x_1701_);
lean_ctor_set(v___x_1693_, 0, v_a_1699_);
v___x_1704_ = v___x_1693_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1699_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1700_, v_fst_1696_, v___x_1704_, v___y_1687_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1697_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; size_t v___x_1709_; size_t v___x_1710_; uint8_t v___x_1711_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = lean_ptr_addr(v_k_1528_);
v___x_1710_ = lean_ptr_addr(v_a_1708_);
v___x_1711_ = lean_usize_dec_eq(v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
v___y_1521_ = v_a_1708_;
v___y_1522_ = v_a_1706_;
v___y_1523_ = v___x_1711_;
goto v___jp_1520_;
}
else
{
size_t v___x_1712_; size_t v___x_1713_; uint8_t v___x_1714_; 
v___x_1712_ = lean_ptr_addr(v_decl_1527_);
v___x_1713_ = lean_ptr_addr(v_a_1706_);
v___x_1714_ = lean_usize_dec_eq(v___x_1712_, v___x_1713_);
v___y_1521_ = v_a_1708_;
v___y_1522_ = v_a_1706_;
v___y_1523_ = v___x_1714_;
goto v___jp_1520_;
}
}
else
{
lean_dec(v_a_1706_);
lean_dec_ref(v_code_1416_);
return v___x_1707_;
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_snd_1697_);
lean_dec_ref(v_code_1416_);
v_a_1715_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1705_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1705_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_snd_1697_);
lean_dec(v_fst_1696_);
lean_del_object(v___x_1693_);
lean_dec_ref(v_code_1416_);
v_a_1724_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1698_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1698_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
else
{
lean_object* v___x_1736_; 
lean_dec(v_a_1691_);
v___x_1736_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1682_, v_value_1571_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; uint8_t v___x_1738_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = lean_unbox(v_a_1737_);
lean_dec(v_a_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
lean_inc_ref(v_k_1528_);
v___x_1739_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; size_t v___x_1741_; size_t v___x_1742_; uint8_t v___x_1743_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref(v___x_1739_);
v___x_1741_ = lean_ptr_addr(v_k_1528_);
v___x_1742_ = lean_ptr_addr(v_a_1740_);
v___x_1743_ = lean_usize_dec_eq(v___x_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
v___y_1558_ = v_a_1740_;
v___y_1559_ = v___x_1743_;
goto v___jp_1557_;
}
else
{
size_t v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = lean_ptr_addr(v_decl_1527_);
v___x_1745_ = lean_usize_dec_eq(v___x_1744_, v___x_1744_);
v___y_1558_ = v_a_1740_;
v___y_1559_ = v___x_1745_;
goto v___jp_1557_;
}
}
else
{
lean_dec_ref(v_code_1416_);
return v___x_1739_;
}
}
else
{
lean_object* v___x_1746_; 
lean_inc_ref(v_decl_1527_);
v___x_1746_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1527_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = 0;
v___x_1749_ = lean_box(0);
v___x_1750_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1751_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1751_, 0, v_a_1747_);
lean_ctor_set(v___x_1751_, 1, v___x_1749_);
lean_ctor_set(v___x_1751_, 2, v___x_1750_);
lean_inc_ref(v_decl_1527_);
v___x_1752_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1748_, v_decl_1527_, v___x_1751_, v___y_1687_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref(v___x_1752_);
lean_inc_ref(v_k_1528_);
v___x_1754_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; size_t v___x_1756_; size_t v___x_1757_; uint8_t v___x_1758_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = lean_ptr_addr(v_k_1528_);
v___x_1757_ = lean_ptr_addr(v_a_1755_);
v___x_1758_ = lean_usize_dec_eq(v___x_1756_, v___x_1757_);
if (v___x_1758_ == 0)
{
v___y_1514_ = v_a_1753_;
v___y_1515_ = v_a_1755_;
v___y_1516_ = v___x_1758_;
goto v___jp_1513_;
}
else
{
size_t v___x_1759_; size_t v___x_1760_; uint8_t v___x_1761_; 
v___x_1759_ = lean_ptr_addr(v_decl_1527_);
v___x_1760_ = lean_ptr_addr(v_a_1753_);
v___x_1761_ = lean_usize_dec_eq(v___x_1759_, v___x_1760_);
v___y_1514_ = v_a_1753_;
v___y_1515_ = v_a_1755_;
v___y_1516_ = v___x_1761_;
goto v___jp_1513_;
}
}
else
{
lean_dec(v_a_1753_);
lean_dec_ref(v_code_1416_);
return v___x_1754_;
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref(v_code_1416_);
v_a_1762_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1752_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1752_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v_code_1416_);
v_a_1770_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1746_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1746_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec_ref(v_code_1416_);
v_a_1778_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1736_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1736_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v_value_1571_);
lean_dec_ref(v_code_1416_);
v_a_1786_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1690_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1690_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
v___jp_1794_:
{
uint8_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = 0;
v___x_1803_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1802_, v_sizeId_1795_, v___y_1799_);
lean_dec(v_sizeId_1795_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref(v___x_1803_);
if (lean_obj_tag(v_a_1804_) == 1)
{
lean_object* v_val_1805_; 
v_val_1805_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref(v_a_1804_);
if (lean_obj_tag(v_val_1805_) == 0)
{
lean_object* v_value_1806_; 
v_value_1806_ = lean_ctor_get(v_val_1805_, 0);
lean_inc_ref(v_value_1806_);
lean_dec_ref(v_val_1805_);
if (lean_obj_tag(v_value_1806_) == 0)
{
lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1853_; 
v_isSharedCheck_1853_ = !lean_is_exclusive(v_value_1571_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; 
v_unused_1854_ = lean_ctor_get(v_value_1571_, 2);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_value_1571_, 1);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_value_1571_, 0);
lean_dec(v_unused_1856_);
v___x_1808_ = v_value_1571_;
v_isShared_1809_ = v_isSharedCheck_1853_;
goto v_resetjp_1807_;
}
else
{
lean_dec(v_value_1571_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1853_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v_val_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_val_1810_ = lean_ctor_get(v_value_1806_, 0);
lean_inc(v_val_1810_);
lean_dec_ref(v_value_1806_);
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = lean_nat_dec_eq(v_val_1810_, v___x_1811_);
lean_dec(v_val_1810_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; 
lean_del_object(v___x_1808_);
lean_inc_ref(v_k_1528_);
v___x_1813_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; size_t v___x_1815_; size_t v___x_1816_; uint8_t v___x_1817_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref(v___x_1813_);
v___x_1815_ = lean_ptr_addr(v_k_1528_);
v___x_1816_ = lean_ptr_addr(v_a_1814_);
v___x_1817_ = lean_usize_dec_eq(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
v___y_1544_ = v_a_1814_;
v___y_1545_ = v___x_1817_;
goto v___jp_1543_;
}
else
{
size_t v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = lean_ptr_addr(v_decl_1527_);
v___x_1819_ = lean_usize_dec_eq(v___x_1818_, v___x_1818_);
v___y_1544_ = v_a_1814_;
v___y_1545_ = v___x_1819_;
goto v___jp_1543_;
}
}
else
{
lean_dec_ref(v_code_1416_);
return v___x_1813_;
}
}
else
{
lean_object* v___x_1820_; 
lean_inc_ref(v_decl_1527_);
v___x_1820_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1527_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = lean_box(0);
v___x_1823_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 2, v___x_1823_);
lean_ctor_set(v___x_1808_, 1, v___x_1822_);
lean_ctor_set(v___x_1808_, 0, v_a_1821_);
v___x_1825_ = v___x_1808_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1821_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; 
lean_inc_ref(v_decl_1527_);
v___x_1826_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1802_, v_decl_1527_, v___x_1825_, v___y_1799_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref(v___x_1826_);
lean_inc_ref(v_k_1528_);
v___x_1828_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; size_t v___x_1830_; size_t v___x_1831_; uint8_t v___x_1832_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v___x_1828_);
v___x_1830_ = lean_ptr_addr(v_k_1528_);
v___x_1831_ = lean_ptr_addr(v_a_1829_);
v___x_1832_ = lean_usize_dec_eq(v___x_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
v___y_1507_ = v_a_1827_;
v___y_1508_ = v_a_1829_;
v___y_1509_ = v___x_1832_;
goto v___jp_1506_;
}
else
{
size_t v___x_1833_; size_t v___x_1834_; uint8_t v___x_1835_; 
v___x_1833_ = lean_ptr_addr(v_decl_1527_);
v___x_1834_ = lean_ptr_addr(v_a_1827_);
v___x_1835_ = lean_usize_dec_eq(v___x_1833_, v___x_1834_);
v___y_1507_ = v_a_1827_;
v___y_1508_ = v_a_1829_;
v___y_1509_ = v___x_1835_;
goto v___jp_1506_;
}
}
else
{
lean_dec(v_a_1827_);
lean_dec_ref(v_code_1416_);
return v___x_1828_;
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec_ref(v_code_1416_);
v_a_1836_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1826_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1826_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_del_object(v___x_1808_);
lean_dec_ref(v_code_1416_);
v_a_1845_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1820_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1820_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_1806_);
v___y_1684_ = v___y_1796_;
v___y_1685_ = v___y_1797_;
v___y_1686_ = v___y_1798_;
v___y_1687_ = v___y_1799_;
v___y_1688_ = v___y_1800_;
v___y_1689_ = v___y_1801_;
goto v___jp_1683_;
}
}
else
{
lean_dec(v_val_1805_);
v___y_1684_ = v___y_1796_;
v___y_1685_ = v___y_1797_;
v___y_1686_ = v___y_1798_;
v___y_1687_ = v___y_1799_;
v___y_1688_ = v___y_1800_;
v___y_1689_ = v___y_1801_;
goto v___jp_1683_;
}
}
else
{
lean_dec(v_a_1804_);
v___y_1684_ = v___y_1796_;
v___y_1685_ = v___y_1797_;
v___y_1686_ = v___y_1798_;
v___y_1687_ = v___y_1799_;
v___y_1688_ = v___y_1800_;
v___y_1689_ = v___y_1801_;
goto v___jp_1683_;
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v_value_1571_);
lean_dec_ref(v_code_1416_);
v_a_1857_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1803_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1803_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
else
{
v___y_1573_ = v_a_1417_;
v___y_1574_ = v_a_1418_;
v___y_1575_ = v_a_1419_;
v___y_1576_ = v_a_1420_;
v___y_1577_ = v_a_1421_;
v___y_1578_ = v_a_1422_;
goto v___jp_1572_;
}
}
else
{
v___y_1573_ = v_a_1417_;
v___y_1574_ = v_a_1418_;
v___y_1575_ = v_a_1419_;
v___y_1576_ = v_a_1420_;
v___y_1577_ = v_a_1421_;
v___y_1578_ = v_a_1422_;
goto v___jp_1572_;
}
}
else
{
v___y_1573_ = v_a_1417_;
v___y_1574_ = v_a_1418_;
v___y_1575_ = v_a_1419_;
v___y_1576_ = v_a_1420_;
v___y_1577_ = v_a_1421_;
v___y_1578_ = v_a_1422_;
goto v___jp_1572_;
}
}
else
{
v___y_1573_ = v_a_1417_;
v___y_1574_ = v_a_1418_;
v___y_1575_ = v_a_1419_;
v___y_1576_ = v_a_1420_;
v___y_1577_ = v_a_1421_;
v___y_1578_ = v_a_1422_;
goto v___jp_1572_;
}
v___jp_1529_:
{
if (v___y_1531_ == 0)
{
lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1539_; 
lean_inc_ref(v_decl_1527_);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_code_1416_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; lean_object* v_unused_1541_; 
v_unused_1540_ = lean_ctor_get(v_code_1416_, 1);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_code_1416_, 0);
lean_dec(v_unused_1541_);
v___x_1533_ = v_code_1416_;
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
else
{
lean_dec(v_code_1416_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v___y_1530_);
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_decl_1527_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___y_1530_);
v___x_1536_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
}
}
else
{
lean_object* v___x_1542_; 
lean_dec_ref(v___y_1530_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_code_1416_);
return v___x_1542_;
}
}
v___jp_1543_:
{
if (v___y_1545_ == 0)
{
lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1553_; 
lean_inc_ref(v_decl_1527_);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_code_1416_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; lean_object* v_unused_1555_; 
v_unused_1554_ = lean_ctor_get(v_code_1416_, 1);
lean_dec(v_unused_1554_);
v_unused_1555_ = lean_ctor_get(v_code_1416_, 0);
lean_dec(v_unused_1555_);
v___x_1547_ = v_code_1416_;
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
else
{
lean_dec(v_code_1416_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 1, v___y_1544_);
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_decl_1527_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___y_1544_);
v___x_1550_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
}
}
else
{
lean_object* v___x_1556_; 
lean_dec_ref(v___y_1544_);
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_code_1416_);
return v___x_1556_;
}
}
v___jp_1557_:
{
if (v___y_1559_ == 0)
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
lean_inc_ref(v_decl_1527_);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_code_1416_);
if (v_isSharedCheck_1567_ == 0)
{
lean_object* v_unused_1568_; lean_object* v_unused_1569_; 
v_unused_1568_ = lean_ctor_get(v_code_1416_, 1);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_code_1416_, 0);
lean_dec(v_unused_1569_);
v___x_1561_ = v_code_1416_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v_code_1416_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 1, v___y_1558_);
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_decl_1527_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v___y_1558_);
v___x_1564_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
}
else
{
lean_object* v___x_1570_; 
lean_dec_ref(v___y_1558_);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_code_1416_);
return v___x_1570_;
}
}
v___jp_1572_:
{
lean_object* v___x_1579_; 
lean_inc_ref(v_k_1528_);
lean_inc_ref(v_decl_1527_);
v___x_1579_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1527_, v_k_1528_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref(v___x_1579_);
if (lean_obj_tag(v_a_1580_) == 1)
{
lean_object* v_val_1581_; lean_object* v_fst_1582_; lean_object* v_snd_1583_; lean_object* v___x_1584_; 
lean_dec(v_value_1571_);
v_val_1581_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_val_1581_);
lean_dec_ref(v_a_1580_);
v_fst_1582_ = lean_ctor_get(v_val_1581_, 0);
lean_inc_n(v_fst_1582_, 2);
v_snd_1583_ = lean_ctor_get(v_val_1581_, 1);
lean_inc(v_snd_1583_);
lean_dec(v_val_1581_);
v___x_1584_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1582_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = 0;
v___x_1587_ = lean_box(0);
v___x_1588_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1589_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1589_, 0, v_a_1585_);
lean_ctor_set(v___x_1589_, 1, v___x_1587_);
lean_ctor_set(v___x_1589_, 2, v___x_1588_);
v___x_1590_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1586_, v_fst_1582_, v___x_1589_, v___y_1576_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1592_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
v___x_1592_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1583_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; size_t v___x_1594_; size_t v___x_1595_; uint8_t v___x_1596_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___x_1592_);
v___x_1594_ = lean_ptr_addr(v_k_1528_);
v___x_1595_ = lean_ptr_addr(v_a_1593_);
v___x_1596_ = lean_usize_dec_eq(v___x_1594_, v___x_1595_);
if (v___x_1596_ == 0)
{
v___y_1500_ = v_a_1593_;
v___y_1501_ = v_a_1591_;
v___y_1502_ = v___x_1596_;
goto v___jp_1499_;
}
else
{
size_t v___x_1597_; size_t v___x_1598_; uint8_t v___x_1599_; 
v___x_1597_ = lean_ptr_addr(v_decl_1527_);
v___x_1598_ = lean_ptr_addr(v_a_1591_);
v___x_1599_ = lean_usize_dec_eq(v___x_1597_, v___x_1598_);
v___y_1500_ = v_a_1593_;
v___y_1501_ = v_a_1591_;
v___y_1502_ = v___x_1599_;
goto v___jp_1499_;
}
}
else
{
lean_dec(v_a_1591_);
lean_dec_ref(v_code_1416_);
return v___x_1592_;
}
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_snd_1583_);
lean_dec_ref(v_code_1416_);
v_a_1600_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1590_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1590_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_snd_1583_);
lean_dec(v_fst_1582_);
lean_dec_ref(v_code_1416_);
v_a_1608_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1584_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1584_);
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
uint8_t v___x_1616_; lean_object* v___x_1617_; 
lean_dec(v_a_1580_);
v___x_1616_ = 1;
v___x_1617_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1616_, v_value_1571_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; uint8_t v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = lean_unbox(v_a_1618_);
lean_dec(v_a_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_inc_ref(v_k_1528_);
v___x_1620_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; size_t v___x_1622_; size_t v___x_1623_; uint8_t v___x_1624_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = lean_ptr_addr(v_k_1528_);
v___x_1623_ = lean_ptr_addr(v_a_1621_);
v___x_1624_ = lean_usize_dec_eq(v___x_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
v___y_1530_ = v_a_1621_;
v___y_1531_ = v___x_1624_;
goto v___jp_1529_;
}
else
{
size_t v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = lean_ptr_addr(v_decl_1527_);
v___x_1626_ = lean_usize_dec_eq(v___x_1625_, v___x_1625_);
v___y_1530_ = v_a_1621_;
v___y_1531_ = v___x_1626_;
goto v___jp_1529_;
}
}
else
{
lean_dec_ref(v_code_1416_);
return v___x_1620_;
}
}
else
{
lean_object* v___x_1627_; 
lean_inc_ref(v_decl_1527_);
v___x_1627_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1527_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref(v___x_1627_);
v___x_1629_ = 0;
v___x_1630_ = lean_box(0);
v___x_1631_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1632_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1632_, 0, v_a_1628_);
lean_ctor_set(v___x_1632_, 1, v___x_1630_);
lean_ctor_set(v___x_1632_, 2, v___x_1631_);
lean_inc_ref(v_decl_1527_);
v___x_1633_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1629_, v_decl_1527_, v___x_1632_, v___y_1576_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1635_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref(v___x_1633_);
lean_inc_ref(v_k_1528_);
v___x_1635_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1528_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; size_t v___x_1637_; size_t v___x_1638_; uint8_t v___x_1639_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
lean_dec_ref(v___x_1635_);
v___x_1637_ = lean_ptr_addr(v_k_1528_);
v___x_1638_ = lean_ptr_addr(v_a_1636_);
v___x_1639_ = lean_usize_dec_eq(v___x_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
v___y_1493_ = v_a_1636_;
v___y_1494_ = v_a_1634_;
v___y_1495_ = v___x_1639_;
goto v___jp_1492_;
}
else
{
size_t v___x_1640_; size_t v___x_1641_; uint8_t v___x_1642_; 
v___x_1640_ = lean_ptr_addr(v_decl_1527_);
v___x_1641_ = lean_ptr_addr(v_a_1634_);
v___x_1642_ = lean_usize_dec_eq(v___x_1640_, v___x_1641_);
v___y_1493_ = v_a_1636_;
v___y_1494_ = v_a_1634_;
v___y_1495_ = v___x_1642_;
goto v___jp_1492_;
}
}
else
{
lean_dec(v_a_1634_);
lean_dec_ref(v_code_1416_);
return v___x_1635_;
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v_code_1416_);
v_a_1643_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1633_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1633_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v_code_1416_);
v_a_1651_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1627_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1627_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
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
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_code_1416_);
v_a_1659_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1617_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1617_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
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
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_value_1571_);
lean_dec_ref(v_code_1416_);
v_a_1667_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1579_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1579_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1881_; lean_object* v_k_1882_; 
v_decl_1881_ = lean_ctor_get(v_code_1416_, 0);
v_k_1882_ = lean_ctor_get(v_code_1416_, 1);
lean_inc_ref(v_k_1882_);
lean_inc_ref(v_decl_1881_);
v_decl_1439_ = v_decl_1881_;
v_k_1440_ = v_k_1882_;
v___y_1441_ = v_a_1417_;
v___y_1442_ = v_a_1418_;
v___y_1443_ = v_a_1419_;
v___y_1444_ = v_a_1420_;
v___y_1445_ = v_a_1421_;
v___y_1446_ = v_a_1422_;
goto v___jp_1438_;
}
case 2:
{
lean_object* v_decl_1883_; lean_object* v_k_1884_; 
v_decl_1883_ = lean_ctor_get(v_code_1416_, 0);
v_k_1884_ = lean_ctor_get(v_code_1416_, 1);
lean_inc_ref(v_k_1884_);
lean_inc_ref(v_decl_1883_);
v_decl_1439_ = v_decl_1883_;
v_k_1440_ = v_k_1884_;
v___y_1441_ = v_a_1417_;
v___y_1442_ = v_a_1418_;
v___y_1443_ = v_a_1419_;
v___y_1444_ = v_a_1420_;
v___y_1445_ = v_a_1421_;
v___y_1446_ = v_a_1422_;
goto v___jp_1438_;
}
case 4:
{
lean_object* v_cases_1885_; lean_object* v_typeName_1886_; lean_object* v_resultType_1887_; lean_object* v_discr_1888_; lean_object* v_alts_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1928_; 
v_cases_1885_ = lean_ctor_get(v_code_1416_, 0);
lean_inc_ref(v_cases_1885_);
v_typeName_1886_ = lean_ctor_get(v_cases_1885_, 0);
v_resultType_1887_ = lean_ctor_get(v_cases_1885_, 1);
v_discr_1888_ = lean_ctor_get(v_cases_1885_, 2);
v_alts_1889_ = lean_ctor_get(v_cases_1885_, 3);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_cases_1885_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1891_ = v_cases_1885_;
v_isShared_1892_ = v_isSharedCheck_1928_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_alts_1889_);
lean_inc(v_discr_1888_);
lean_inc(v_resultType_1887_);
lean_inc(v_typeName_1886_);
lean_dec(v_cases_1885_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1928_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1889_);
v___x_1894_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v___x_1893_, v_alts_1889_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1919_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1919_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1919_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
size_t v___x_1899_; size_t v___x_1900_; uint8_t v___x_1901_; 
v___x_1899_ = lean_ptr_addr(v_alts_1889_);
lean_dec_ref(v_alts_1889_);
v___x_1900_ = lean_ptr_addr(v_a_1895_);
v___x_1901_ = lean_usize_dec_eq(v___x_1899_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1914_; 
v_isSharedCheck_1914_ = !lean_is_exclusive(v_code_1416_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v_code_1416_, 0);
lean_dec(v_unused_1915_);
v___x_1903_ = v_code_1416_;
v_isShared_1904_ = v_isSharedCheck_1914_;
goto v_resetjp_1902_;
}
else
{
lean_dec(v_code_1416_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1914_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 3, v_a_1895_);
v___x_1906_ = v___x_1891_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_typeName_1886_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_resultType_1887_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_discr_1888_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_a_1895_);
v___x_1906_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1906_);
v___x_1908_ = v___x_1903_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1910_; 
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1908_);
v___x_1910_ = v___x_1897_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
else
{
lean_object* v___x_1917_; 
lean_dec(v_a_1895_);
lean_del_object(v___x_1891_);
lean_dec(v_discr_1888_);
lean_dec_ref(v_resultType_1887_);
lean_dec(v_typeName_1886_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v_code_1416_);
v___x_1917_ = v___x_1897_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_code_1416_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_del_object(v___x_1891_);
lean_dec_ref(v_alts_1889_);
lean_dec(v_discr_1888_);
lean_dec_ref(v_resultType_1887_);
lean_dec(v_typeName_1886_);
lean_dec_ref(v_code_1416_);
v_a_1920_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1894_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1894_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
default: 
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v_code_1416_);
return v___x_1929_;
}
}
v___jp_1424_:
{
if (v___y_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec_ref(v_code_1416_);
v___x_1428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___y_1425_);
lean_ctor_set(v___x_1428_, 1, v___y_1426_);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
return v___x_1429_;
}
else
{
lean_object* v___x_1430_; 
lean_dec_ref(v___y_1426_);
lean_dec_ref(v___y_1425_);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_code_1416_);
return v___x_1430_;
}
}
v___jp_1431_:
{
if (v___y_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec_ref(v_code_1416_);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___y_1432_);
lean_ctor_set(v___x_1435_, 1, v___y_1433_);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; 
lean_dec_ref(v___y_1433_);
lean_dec_ref(v___y_1432_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_code_1416_);
return v___x_1437_;
}
}
v___jp_1438_:
{
lean_object* v_params_1447_; lean_object* v_type_1448_; lean_object* v_value_1449_; lean_object* v___x_1450_; 
v_params_1447_ = lean_ctor_get(v_decl_1439_, 2);
lean_inc_ref(v_params_1447_);
v_type_1448_ = lean_ctor_get(v_decl_1439_, 3);
lean_inc_ref(v_type_1448_);
v_value_1449_ = lean_ctor_get(v_decl_1439_, 4);
lean_inc_ref(v_value_1449_);
v___x_1450_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_value_1449_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; uint8_t v___x_1452_; lean_object* v___x_1453_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1450_);
v___x_1452_ = 0;
v___x_1453_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1452_, v_decl_1439_, v_type_1448_, v_params_1447_, v_a_1451_, v___y_1444_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1455_) == 0)
{
switch(lean_obj_tag(v_code_1416_))
{
case 1:
{
lean_object* v_a_1456_; lean_object* v_decl_1457_; lean_object* v_k_1458_; size_t v___x_1459_; size_t v___x_1460_; uint8_t v___x_1461_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref(v___x_1455_);
v_decl_1457_ = lean_ctor_get(v_code_1416_, 0);
v_k_1458_ = lean_ctor_get(v_code_1416_, 1);
v___x_1459_ = lean_ptr_addr(v_k_1458_);
v___x_1460_ = lean_ptr_addr(v_a_1456_);
v___x_1461_ = lean_usize_dec_eq(v___x_1459_, v___x_1460_);
if (v___x_1461_ == 0)
{
v___y_1432_ = v_a_1454_;
v___y_1433_ = v_a_1456_;
v___y_1434_ = v___x_1461_;
goto v___jp_1431_;
}
else
{
size_t v___x_1462_; size_t v___x_1463_; uint8_t v___x_1464_; 
v___x_1462_ = lean_ptr_addr(v_decl_1457_);
v___x_1463_ = lean_ptr_addr(v_a_1454_);
v___x_1464_ = lean_usize_dec_eq(v___x_1462_, v___x_1463_);
v___y_1432_ = v_a_1454_;
v___y_1433_ = v_a_1456_;
v___y_1434_ = v___x_1464_;
goto v___jp_1431_;
}
}
case 2:
{
lean_object* v_a_1465_; lean_object* v_decl_1466_; lean_object* v_k_1467_; size_t v___x_1468_; size_t v___x_1469_; uint8_t v___x_1470_; 
v_a_1465_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1465_);
lean_dec_ref(v___x_1455_);
v_decl_1466_ = lean_ctor_get(v_code_1416_, 0);
v_k_1467_ = lean_ctor_get(v_code_1416_, 1);
v___x_1468_ = lean_ptr_addr(v_k_1467_);
v___x_1469_ = lean_ptr_addr(v_a_1465_);
v___x_1470_ = lean_usize_dec_eq(v___x_1468_, v___x_1469_);
if (v___x_1470_ == 0)
{
v___y_1425_ = v_a_1454_;
v___y_1426_ = v_a_1465_;
v___y_1427_ = v___x_1470_;
goto v___jp_1424_;
}
else
{
size_t v___x_1471_; size_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = lean_ptr_addr(v_decl_1466_);
v___x_1472_ = lean_ptr_addr(v_a_1454_);
v___x_1473_ = lean_usize_dec_eq(v___x_1471_, v___x_1472_);
v___y_1425_ = v_a_1454_;
v___y_1426_ = v_a_1465_;
v___y_1427_ = v___x_1473_;
goto v___jp_1424_;
}
}
default: 
{
lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_a_1454_);
lean_dec_ref(v_code_1416_);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v___x_1455_, 0);
lean_dec(v_unused_1483_);
v___x_1475_ = v___x_1455_;
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v___x_1455_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1477_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3, &l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3);
v___x_1478_ = l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(v___x_1477_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1478_);
v___x_1480_ = v___x_1475_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
else
{
lean_dec(v_a_1454_);
lean_dec_ref(v_code_1416_);
return v___x_1455_;
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v_k_1440_);
lean_dec_ref(v_code_1416_);
v_a_1484_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1453_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1453_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_dec_ref(v_type_1448_);
lean_dec_ref(v_params_1447_);
lean_dec_ref(v_k_1440_);
lean_dec_ref(v_decl_1439_);
lean_dec_ref(v_code_1416_);
return v___x_1450_;
}
}
v___jp_1492_:
{
if (v___y_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec_ref(v_code_1416_);
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1494_);
lean_ctor_set(v___x_1496_, 1, v___y_1493_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; 
lean_dec_ref(v___y_1494_);
lean_dec_ref(v___y_1493_);
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_code_1416_);
return v___x_1498_;
}
}
v___jp_1499_:
{
if (v___y_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec_ref(v_code_1416_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___y_1501_);
lean_ctor_set(v___x_1503_, 1, v___y_1500_);
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
else
{
lean_object* v___x_1505_; 
lean_dec_ref(v___y_1501_);
lean_dec_ref(v___y_1500_);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v_code_1416_);
return v___x_1505_;
}
}
v___jp_1506_:
{
if (v___y_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v_code_1416_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___y_1507_);
lean_ctor_set(v___x_1510_, 1, v___y_1508_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; 
lean_dec_ref(v___y_1508_);
lean_dec_ref(v___y_1507_);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_code_1416_);
return v___x_1512_;
}
}
v___jp_1513_:
{
if (v___y_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec_ref(v_code_1416_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
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
lean_ctor_set(v___x_1519_, 0, v_code_1416_);
return v___x_1519_;
}
}
v___jp_1520_:
{
if (v___y_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec_ref(v_code_1416_);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___y_1522_);
lean_ctor_set(v___x_1524_, 1, v___y_1521_);
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
lean_ctor_set(v___x_1526_, 0, v_code_1416_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object* v_i_1930_, lean_object* v_as_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1939_ = lean_array_get_size(v_as_1931_);
v___x_1940_ = lean_nat_dec_lt(v_i_1930_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec(v_i_1930_);
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_as_1931_);
return v___x_1941_;
}
else
{
lean_object* v_a_1942_; lean_object* v___y_1944_; 
v_a_1942_ = lean_array_fget_borrowed(v_as_1931_, v_i_1930_);
switch(lean_obj_tag(v_a_1942_))
{
case 0:
{
lean_object* v_code_1966_; 
v_code_1966_ = lean_ctor_get(v_a_1942_, 2);
lean_inc_ref(v_code_1966_);
v___y_1944_ = v_code_1966_;
goto v___jp_1943_;
}
case 1:
{
lean_object* v_code_1967_; 
v_code_1967_ = lean_ctor_get(v_a_1942_, 1);
lean_inc_ref(v_code_1967_);
v___y_1944_ = v_code_1967_;
goto v___jp_1943_;
}
default: 
{
lean_object* v_code_1968_; 
v_code_1968_ = lean_ctor_get(v_a_1942_, 0);
lean_inc_ref(v_code_1968_);
v___y_1944_ = v_code_1968_;
goto v___jp_1943_;
}
}
v___jp_1943_:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v___y_1944_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; uint8_t v___x_1950_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
lean_inc(v_a_1942_);
v___x_1947_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1942_, v_a_1946_);
v___x_1948_ = lean_ptr_addr(v_a_1942_);
v___x_1949_ = lean_ptr_addr(v___x_1947_);
v___x_1950_ = lean_usize_dec_eq(v___x_1948_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1951_ = lean_unsigned_to_nat(1u);
v___x_1952_ = lean_nat_add(v_i_1930_, v___x_1951_);
v___x_1953_ = lean_array_fset(v_as_1931_, v_i_1930_, v___x_1947_);
lean_dec(v_i_1930_);
v_i_1930_ = v___x_1952_;
v_as_1931_ = v___x_1953_;
goto _start;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
lean_dec_ref(v___x_1947_);
v___x_1955_ = lean_unsigned_to_nat(1u);
v___x_1956_ = lean_nat_add(v_i_1930_, v___x_1955_);
lean_dec(v_i_1930_);
v_i_1930_ = v___x_1956_;
goto _start;
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec_ref(v_as_1931_);
lean_dec(v_i_1930_);
v_a_1958_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1945_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1945_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object* v_i_1969_, lean_object* v_as_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_1969_, v_as_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object* v_code_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_code_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(lean_object* v_f_1988_, lean_object* v_v_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
if (lean_obj_tag(v_v_1989_) == 0)
{
lean_object* v_code_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2021_; 
v_code_1997_ = lean_ctor_get(v_v_1989_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_v_1989_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1999_ = v_v_1989_;
v_isShared_2000_ = v_isSharedCheck_2021_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_code_1997_);
lean_dec(v_v_1989_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2021_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2001_; 
lean_inc(v___y_1995_);
lean_inc_ref(v___y_1994_);
lean_inc(v___y_1993_);
lean_inc_ref(v___y_1992_);
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
v___x_2001_ = lean_apply_8(v_f_1988_, v_code_1997_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, lean_box(0));
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2012_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2012_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2012_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v_a_2002_);
v___x_2007_ = v___x_1999_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2009_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2007_);
v___x_2009_ = v___x_2004_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_del_object(v___x_1999_);
v_a_2013_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2001_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2001_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
else
{
lean_object* v___x_2022_; 
lean_dec_ref(v_f_1988_);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_v_1989_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(lean_object* v_f_2023_, lean_object* v_v_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2023_, v_v_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(uint8_t v_pu_2033_, lean_object* v_f_2034_, lean_object* v_v_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2034_, v_v_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(lean_object* v_pu_2044_, lean_object* v_f_2045_, lean_object* v_v_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
uint8_t v_pu_boxed_2054_; lean_object* v_res_2055_; 
v_pu_boxed_2054_ = lean_unbox(v_pu_2044_);
v_res_2055_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_boxed_2054_, v_f_2045_, v_v_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object* v_decl_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v_toSignature_2065_; lean_object* v_value_2066_; uint8_t v_recursive_2067_; lean_object* v_inlineAttr_x3f_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2093_; 
v_toSignature_2065_ = lean_ctor_get(v_decl_2057_, 0);
v_value_2066_ = lean_ctor_get(v_decl_2057_, 1);
v_recursive_2067_ = lean_ctor_get_uint8(v_decl_2057_, sizeof(void*)*3);
v_inlineAttr_x3f_2068_ = lean_ctor_get(v_decl_2057_, 2);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_decl_2057_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2070_ = v_decl_2057_;
v_isShared_2071_ = v_isSharedCheck_2093_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_inlineAttr_x3f_2068_);
lean_inc(v_value_2066_);
lean_inc(v_toSignature_2065_);
lean_dec(v_decl_2057_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2093_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0));
v___x_2073_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v___x_2072_, v_value_2066_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2084_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2084_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2084_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v_a_2074_);
v___x_2079_ = v___x_2070_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_toSignature_2065_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_a_2074_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_inlineAttr_x3f_2068_);
lean_ctor_set_uint8(v_reuseFailAlloc_2083_, sizeof(void*)*3, v_recursive_2067_);
v___x_2079_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2081_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2079_);
v___x_2081_ = v___x_2076_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
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
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_del_object(v___x_2070_);
lean_dec(v_inlineAttr_x3f_2068_);
lean_dec_ref(v_toSignature_2065_);
v_a_2085_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2073_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2073_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(lean_object* v_decl_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
return v_res_2102_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_2106_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0));
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* v_decl_2108_, lean_object* v_sccDecls_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v_toSignature_2118_; lean_object* v_name_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1);
v___x_2117_ = lean_st_mk_ref(v___x_2116_);
v_toSignature_2118_ = lean_ctor_get(v_decl_2108_, 0);
v_name_2119_ = lean_ctor_get(v_toSignature_2118_, 0);
lean_inc(v_name_2119_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v_name_2119_);
lean_ctor_set(v___x_2120_, 1, v_sccDecls_2109_);
v___x_2121_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2108_, v___x_2120_, v___x_2117_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
lean_dec_ref(v___x_2120_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2147_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2147_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2147_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v_decls_2127_; lean_object* v_decl_2129_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2126_ = lean_st_ref_get(v___x_2117_);
lean_dec(v___x_2117_);
v_decls_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc_ref(v_decls_2127_);
lean_dec(v___x_2126_);
v___x_2134_ = lean_array_get_size(v_decls_2127_);
v___x_2135_ = lean_nat_dec_eq(v___x_2134_, v___x_2115_);
if (v___x_2135_ == 0)
{
uint8_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = 0;
v___x_2137_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2136_, v_a_2122_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref(v___x_2137_);
v_decl_2129_ = v_a_2138_;
goto v___jp_2128_;
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec_ref(v_decls_2127_);
lean_del_object(v___x_2124_);
v_a_2139_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2137_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2137_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
v_decl_2129_ = v_a_2122_;
goto v___jp_2128_;
}
v___jp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_array_push(v_decls_2127_, v_decl_2129_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2130_);
v___x_2132_ = v___x_2124_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v___x_2117_);
v_a_2148_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2121_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2121_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(lean_object* v_decl_2156_, lean_object* v_sccDecls_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v_decl_2156_, v_sccDecls_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(lean_object* v_decls_2164_, lean_object* v_as_2165_, size_t v_i_2166_, size_t v_stop_2167_, lean_object* v_b_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_a_2175_; uint8_t v___x_2179_; 
v___x_2179_ = lean_usize_dec_eq(v_i_2166_, v_stop_2167_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_array_uget_borrowed(v_as_2165_, v_i_2166_);
lean_inc_ref(v_decls_2164_);
lean_inc(v___x_2180_);
v___x_2181_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v___x_2180_, v_decls_2164_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2183_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = l_Array_append___redArg(v_b_2168_, v_a_2182_);
lean_dec(v_a_2182_);
v_a_2175_ = v___x_2183_;
goto v___jp_2174_;
}
else
{
lean_dec_ref(v_b_2168_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2184_; 
v_a_2184_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2184_);
lean_dec_ref(v___x_2181_);
v_a_2175_ = v_a_2184_;
goto v___jp_2174_;
}
else
{
lean_dec_ref(v_decls_2164_);
return v___x_2181_;
}
}
}
else
{
lean_object* v___x_2185_; 
lean_dec_ref(v_decls_2164_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_b_2168_);
return v___x_2185_;
}
v___jp_2174_:
{
size_t v___x_2176_; size_t v___x_2177_; 
v___x_2176_ = ((size_t)1ULL);
v___x_2177_ = lean_usize_add(v_i_2166_, v___x_2176_);
v_i_2166_ = v___x_2177_;
v_b_2168_ = v_a_2175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object* v_decls_2186_, lean_object* v_as_2187_, lean_object* v_i_2188_, lean_object* v_stop_2189_, lean_object* v_b_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
size_t v_i_boxed_2196_; size_t v_stop_boxed_2197_; lean_object* v_res_2198_; 
v_i_boxed_2196_ = lean_unbox_usize(v_i_2188_);
lean_dec(v_i_2188_);
v_stop_boxed_2197_ = lean_unbox_usize(v_stop_2189_);
lean_dec(v_stop_2189_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2186_, v_as_2187_, v_i_boxed_2196_, v_stop_boxed_2197_, v_b_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec_ref(v_as_2187_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* v___x_2199_, lean_object* v_decls_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_2201_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2231_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2231_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2231_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
uint8_t v_extractClosed_2211_; 
v_extractClosed_2211_ = lean_ctor_get_uint8(v_a_2207_, sizeof(void*)*4 + 1);
lean_dec(v_a_2207_);
if (v_extractClosed_2211_ == 0)
{
lean_object* v___x_2213_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v_decls_2200_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_decls_2200_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
else
{
lean_object* v___x_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2215_ = lean_mk_empty_array_with_capacity(v___x_2199_);
v___x_2216_ = lean_array_get_size(v_decls_2200_);
v___x_2217_ = lean_nat_dec_lt(v___x_2199_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2219_; 
lean_dec_ref(v_decls_2200_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2215_);
v___x_2219_ = v___x_2209_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2215_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
else
{
uint8_t v___x_2221_; 
v___x_2221_ = lean_nat_dec_le(v___x_2216_, v___x_2216_);
if (v___x_2221_ == 0)
{
if (v___x_2217_ == 0)
{
lean_object* v___x_2223_; 
lean_dec_ref(v_decls_2200_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2215_);
v___x_2223_ = v___x_2209_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2215_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
else
{
size_t v___x_2225_; size_t v___x_2226_; lean_object* v___x_2227_; 
lean_del_object(v___x_2209_);
v___x_2225_ = ((size_t)0ULL);
v___x_2226_ = lean_usize_of_nat(v___x_2216_);
lean_inc_ref(v_decls_2200_);
v___x_2227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2200_, v_decls_2200_, v___x_2225_, v___x_2226_, v___x_2215_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec_ref(v_decls_2200_);
return v___x_2227_;
}
}
else
{
size_t v___x_2228_; size_t v___x_2229_; lean_object* v___x_2230_; 
lean_del_object(v___x_2209_);
v___x_2228_ = ((size_t)0ULL);
v___x_2229_ = lean_usize_of_nat(v___x_2216_);
lean_inc_ref(v_decls_2200_);
v___x_2230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2200_, v_decls_2200_, v___x_2228_, v___x_2229_, v___x_2215_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec_ref(v_decls_2200_);
return v___x_2230_;
}
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec_ref(v_decls_2200_);
v_a_2232_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2206_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2206_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object* v___x_2240_, lean_object* v_decls_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(v___x_2240_, v_decls_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___x_2240_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2330_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2331_ = 1;
v___x_2332_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2333_ = l_Lean_registerTraceClass(v___x_2330_, v___x_2331_, v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
return v_res_2335_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ExtractClosed(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
