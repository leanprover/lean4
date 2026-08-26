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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint8_t v_____do__lift_15156__boxed_193_; lean_object* v_res_194_; 
v_____do__lift_15156__boxed_193_ = lean_unbox(v_____do__lift_185_);
v_res_194_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v_____do__lift_15156__boxed_193_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
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
uint8_t v_isRoot_boxed_394_; uint8_t v___x_15461__boxed_395_; size_t v_i_boxed_396_; size_t v_stop_boxed_397_; uint8_t v_res_398_; lean_object* v_r_399_; 
v_isRoot_boxed_394_ = lean_unbox(v_isRoot_389_);
v___x_15461__boxed_395_ = lean_unbox(v___x_390_);
v_i_boxed_396_ = lean_unbox_usize(v_i_392_);
lean_dec(v_i_392_);
v_stop_boxed_397_ = lean_unbox_usize(v_stop_393_);
lean_dec(v_stop_393_);
v_res_398_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_boxed_394_, v___x_15461__boxed_395_, v_as_391_, v_i_boxed_396_, v_stop_boxed_397_);
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
lean_dec_ref_known(v___x_422_, 1);
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
uint8_t v___x_452_; 
v___x_452_ = lean_usize_dec_eq(v_i_439_, v_stop_440_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = 1;
v___x_454_ = lean_array_uget_borrowed(v_as_438_, v_i_439_);
lean_inc(v___x_454_);
v___x_455_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_454_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_465_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_465_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_465_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_465_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
uint8_t v___x_460_; 
v___x_460_ = lean_unbox(v_a_456_);
lean_dec(v_a_456_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_box(v___x_453_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_461_);
v___x_463_ = v___x_458_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
else
{
lean_del_object(v___x_458_);
goto v___jp_448_;
}
}
}
else
{
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_475_; 
v_a_466_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_475_ == 0)
{
v___x_468_ = v___x_455_;
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_455_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
uint8_t v___x_470_; 
v___x_470_ = lean_unbox(v_a_466_);
lean_dec(v_a_466_);
if (v___x_470_ == 0)
{
lean_del_object(v___x_468_);
goto v___jp_448_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_box(v___x_453_);
if (v_isShared_469_ == 0)
{
lean_ctor_set_tag(v___x_468_, 0);
lean_ctor_set(v___x_468_, 0, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
return v___x_455_;
}
}
}
else
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = 0;
v___x_477_ = lean_box(v___x_476_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
v___jp_448_:
{
size_t v___x_449_; size_t v___x_450_; 
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_439_, v___x_449_);
v_i_439_ = v___x_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t v_isRoot_479_, lean_object* v_v_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
switch(lean_obj_tag(v_v_480_))
{
case 0:
{
lean_object* v_value_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_537_; 
v_value_492_ = lean_ctor_get(v_v_480_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v_v_480_);
if (v_isSharedCheck_537_ == 0)
{
v___x_494_ = v_v_480_;
v_isShared_495_ = v_isSharedCheck_537_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_value_492_);
lean_dec(v_v_480_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_537_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
switch(lean_obj_tag(v_value_492_))
{
case 1:
{
lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_504_; 
lean_del_object(v___x_494_);
v_isSharedCheck_504_ = !lean_is_exclusive(v_value_492_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v_value_492_, 0);
lean_dec(v_unused_505_);
v___x_497_ = v_value_492_;
v_isShared_498_ = v_isSharedCheck_504_;
goto v_resetjp_496_;
}
else
{
lean_dec(v_value_492_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_504_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_499_ = 1;
v___x_500_ = lean_box(v___x_499_);
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 0);
lean_ctor_set(v___x_497_, 0, v___x_500_);
v___x_502_ = v___x_497_;
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
case 0:
{
lean_del_object(v___x_494_);
if (v_isRoot_479_ == 0)
{
lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_514_; 
v_isSharedCheck_514_ = !lean_is_exclusive(v_value_492_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v_value_492_, 0);
lean_dec(v_unused_515_);
v___x_507_ = v_value_492_;
v_isShared_508_ = v_isSharedCheck_514_;
goto v_resetjp_506_;
}
else
{
lean_dec(v_value_492_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_514_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_509_ = 1;
v___x_510_ = lean_box(v___x_509_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_510_);
v___x_512_ = v___x_507_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v_val_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_526_; 
v_val_516_ = lean_ctor_get(v_value_492_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v_value_492_);
if (v_isSharedCheck_526_ == 0)
{
v___x_518_ = v_value_492_;
v_isShared_519_ = v_isSharedCheck_526_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_val_516_);
lean_dec(v_value_492_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_526_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_520_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0, &l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0);
v___x_521_ = lean_nat_dec_le(v___x_520_, v_val_516_);
lean_dec(v_val_516_);
v___x_522_ = lean_box(v___x_521_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_522_);
v___x_524_ = v___x_518_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
default: 
{
lean_dec_ref(v_value_492_);
if (v_isRoot_479_ == 0)
{
uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_527_ = 1;
v___x_528_ = lean_box(v___x_527_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_528_);
v___x_530_ = v___x_494_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
else
{
uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = 0;
v___x_533_ = lean_box(v___x_532_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_533_);
v___x_535_ = v___x_494_;
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
}
}
}
}
case 1:
{
if (v_isRoot_479_ == 0)
{
uint8_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = 1;
v___x_539_ = lean_box(v___x_538_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
else
{
uint8_t v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = 0;
v___x_542_ = lean_box(v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
case 2:
{
lean_object* v_struct_544_; lean_object* v___x_545_; 
v_struct_544_ = lean_ctor_get(v_v_480_, 2);
lean_inc(v_struct_544_);
lean_dec_ref_known(v_v_480_, 3);
v___x_545_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_struct_544_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_545_;
}
case 3:
{
lean_object* v_declName_546_; lean_object* v_args_547_; lean_object* v_sccDecls_548_; lean_object* v___x_549_; uint8_t v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; uint8_t v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; uint8_t v___y_603_; uint8_t v___y_607_; uint8_t v___y_608_; uint8_t v___y_612_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_declName_546_ = lean_ctor_get(v_v_480_, 0);
lean_inc(v_declName_546_);
v_args_547_ = lean_ctor_get(v_v_480_, 2);
lean_inc_ref(v_args_547_);
lean_dec_ref_known(v_v_480_, 3);
v_sccDecls_548_ = lean_ctor_get(v_a_481_, 1);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_array_get_size(v_sccDecls_548_);
v___x_632_ = lean_nat_dec_lt(v___x_549_, v___x_631_);
if (v___x_632_ == 0)
{
v___y_612_ = v___x_632_;
goto v___jp_611_;
}
else
{
if (v___x_632_ == 0)
{
v___y_612_ = v___x_632_;
goto v___jp_611_;
}
else
{
size_t v___x_633_; size_t v___x_634_; uint8_t v___x_635_; 
v___x_633_ = ((size_t)0ULL);
v___x_634_ = lean_usize_of_nat(v___x_631_);
v___x_635_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_546_, v_sccDecls_548_, v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
v___y_612_ = v___x_635_;
goto v___jp_611_;
}
else
{
uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec_ref(v_args_547_);
lean_dec(v_declName_546_);
v___x_636_ = 0;
v___x_637_ = lean_box(v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
v___jp_550_:
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_array_get_size(v_args_547_);
v___x_559_ = lean_nat_dec_lt(v___x_549_, v___x_558_);
if (v___x_559_ == 0)
{
lean_dec_ref(v_args_547_);
goto v___jp_488_;
}
else
{
if (v___x_559_ == 0)
{
lean_dec_ref(v_args_547_);
goto v___jp_488_;
}
else
{
size_t v___x_560_; size_t v___x_561_; lean_object* v___x_562_; 
v___x_560_ = ((size_t)0ULL);
v___x_561_ = lean_usize_of_nat(v___x_558_);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___y_551_, v_args_547_, v___x_560_, v___x_561_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec_ref(v_args_547_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_572_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_572_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_572_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
uint8_t v___x_567_; 
v___x_567_ = lean_unbox(v_a_563_);
lean_dec(v_a_563_);
if (v___x_567_ == 0)
{
lean_del_object(v___x_565_);
goto v___jp_488_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_box(v___y_551_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_568_);
v___x_570_ = v___x_565_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
else
{
return v___x_562_;
}
}
}
}
v___jp_573_:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_546_, v___y_580_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_593_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_593_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_593_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_593_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
if (lean_obj_tag(v_a_582_) == 1)
{
lean_object* v_val_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v_val_586_ = lean_ctor_get(v_a_582_, 0);
lean_inc(v_val_586_);
lean_dec_ref_known(v_a_582_, 1);
v___x_587_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_586_);
lean_dec(v_val_586_);
v___x_588_ = lean_nat_dec_eq(v___x_587_, v___x_549_);
lean_dec(v___x_587_);
if (v___x_588_ == 0)
{
lean_del_object(v___x_584_);
v___y_551_ = v___y_574_;
v___y_552_ = v___y_575_;
v___y_553_ = v___y_576_;
v___y_554_ = v___y_577_;
v___y_555_ = v___y_578_;
v___y_556_ = v___y_579_;
v___y_557_ = v___y_580_;
goto v___jp_550_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_591_; 
lean_dec_ref(v_args_547_);
v___x_589_ = lean_box(v___y_574_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_589_);
v___x_591_ = v___x_584_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
else
{
lean_del_object(v___x_584_);
lean_dec(v_a_582_);
v___y_551_ = v___y_574_;
v___y_552_ = v___y_575_;
v___y_553_ = v___y_576_;
v___y_554_ = v___y_577_;
v___y_555_ = v___y_578_;
v___y_556_ = v___y_579_;
v___y_557_ = v___y_580_;
goto v___jp_550_;
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref(v_args_547_);
v_a_594_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_581_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_581_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
v___jp_602_:
{
if (v___y_603_ == 0)
{
v___y_574_ = v___y_603_;
v___y_575_ = v_a_481_;
v___y_576_ = v_a_482_;
v___y_577_ = v_a_483_;
v___y_578_ = v_a_484_;
v___y_579_ = v_a_485_;
v___y_580_ = v_a_486_;
goto v___jp_573_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec_ref(v_args_547_);
lean_dec(v_declName_546_);
v___x_604_ = lean_box(v___y_603_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
v___jp_606_:
{
if (v___y_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec_ref(v_args_547_);
lean_dec(v_declName_546_);
v___x_609_ = lean_box(v___y_607_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
else
{
v___y_603_ = v___y_607_;
goto v___jp_602_;
}
}
v___jp_611_:
{
lean_object* v___x_613_; lean_object* v_env_614_; uint8_t v___x_615_; 
v___x_613_ = lean_st_ref_get(v_a_486_);
v_env_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_613_);
lean_inc(v_declName_546_);
v___x_615_ = l_Lean_hasNeverExtractAttribute(v_env_614_, v_declName_546_);
if (v___x_615_ == 0)
{
if (v_isRoot_479_ == 0)
{
lean_dec(v_declName_546_);
v___y_551_ = v___x_615_;
v___y_552_ = v_a_481_;
v___y_553_ = v_a_482_;
v___y_554_ = v_a_483_;
v___y_555_ = v_a_484_;
v___y_556_ = v_a_485_;
v___y_557_ = v_a_486_;
goto v___jp_550_;
}
else
{
lean_object* v___x_616_; lean_object* v_env_617_; lean_object* v___x_618_; 
v___x_616_ = lean_st_ref_get(v_a_486_);
v_env_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref(v_env_617_);
lean_dec(v___x_616_);
lean_inc(v_declName_546_);
v___x_618_ = l_Lean_Environment_find_x3f(v_env_617_, v_declName_546_, v___x_615_);
if (lean_obj_tag(v___x_618_) == 1)
{
lean_object* v_val_619_; 
v_val_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_val_619_);
lean_dec_ref_known(v___x_618_, 1);
switch(lean_obj_tag(v_val_619_))
{
case 1:
{
lean_object* v_val_620_; lean_object* v_toConstantVal_621_; lean_object* v_type_622_; uint8_t v___x_623_; 
v_val_620_ = lean_ctor_get(v_val_619_, 0);
lean_inc_ref(v_val_620_);
lean_dec_ref_known(v_val_619_, 1);
v_toConstantVal_621_ = lean_ctor_get(v_val_620_, 0);
lean_inc_ref(v_toConstantVal_621_);
lean_dec_ref(v_val_620_);
v_type_622_ = lean_ctor_get(v_toConstantVal_621_, 2);
lean_inc_ref(v_type_622_);
lean_dec_ref(v_toConstantVal_621_);
v___x_623_ = l_Lean_Expr_isForall(v_type_622_);
lean_dec_ref(v_type_622_);
v___y_607_ = v___x_615_;
v___y_608_ = v___x_623_;
goto v___jp_606_;
}
case 6:
{
lean_object* v___x_624_; uint8_t v___x_625_; 
lean_dec_ref_known(v_val_619_, 1);
v___x_624_ = lean_array_get_size(v_args_547_);
v___x_625_ = lean_nat_dec_lt(v___x_549_, v___x_624_);
if (v___x_625_ == 0)
{
v___y_607_ = v___x_615_;
v___y_608_ = v___x_615_;
goto v___jp_606_;
}
else
{
if (v___x_625_ == 0)
{
v___y_607_ = v___x_615_;
v___y_608_ = v___x_615_;
goto v___jp_606_;
}
else
{
size_t v___x_626_; size_t v___x_627_; uint8_t v___x_628_; 
v___x_626_ = ((size_t)0ULL);
v___x_627_ = lean_usize_of_nat(v___x_624_);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_479_, v___x_615_, v_args_547_, v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
v___y_607_ = v___x_615_;
v___y_608_ = v___x_615_;
goto v___jp_606_;
}
else
{
if (v___x_615_ == 0)
{
v___y_603_ = v___x_615_;
goto v___jp_602_;
}
else
{
v___y_607_ = v___x_615_;
v___y_608_ = v___x_615_;
goto v___jp_606_;
}
}
}
}
}
default: 
{
lean_dec(v_val_619_);
v___y_603_ = v___x_615_;
goto v___jp_602_;
}
}
}
else
{
lean_dec(v___x_618_);
v___y_574_ = v___x_615_;
v___y_575_ = v_a_481_;
v___y_576_ = v_a_482_;
v___y_577_ = v_a_483_;
v___y_578_ = v_a_484_;
v___y_579_ = v_a_485_;
v___y_580_ = v_a_486_;
goto v___jp_573_;
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec_ref(v_args_547_);
lean_dec(v_declName_546_);
v___x_629_ = lean_box(v___y_612_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
default: 
{
lean_object* v_fvarId_639_; lean_object* v_args_640_; lean_object* v___x_641_; 
v_fvarId_639_ = lean_ctor_get(v_v_480_, 0);
lean_inc(v_fvarId_639_);
v_args_640_ = lean_ctor_get(v_v_480_, 1);
lean_inc_ref(v_args_640_);
lean_dec_ref_known(v_v_480_, 2);
v___x_641_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_639_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___y_644_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_array_get_size(v_args_640_);
v___x_656_ = lean_nat_dec_lt(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec_ref(v_args_640_);
v___x_657_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_656_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
v___y_644_ = v___x_657_;
goto v___jp_643_;
}
else
{
if (v___x_656_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v_args_640_);
v___x_658_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_656_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
v___y_644_ = v___x_658_;
goto v___jp_643_;
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_655_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_args_640_, v___x_659_, v___x_660_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
lean_dec_ref(v_args_640_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; uint8_t v___x_663_; lean_object* v___x_664_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = lean_unbox(v_a_662_);
lean_dec(v_a_662_);
v___x_664_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_663_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
v___y_644_ = v___x_664_;
goto v___jp_643_;
}
else
{
v___y_644_ = v___x_661_;
goto v___jp_643_;
}
}
}
v___jp_643_:
{
if (lean_obj_tag(v___y_644_) == 0)
{
uint8_t v___x_645_; 
v___x_645_ = lean_unbox(v_a_642_);
if (v___x_645_ == 0)
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_isSharedCheck_652_ = !lean_is_exclusive(v___y_644_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v___y_644_, 0);
lean_dec(v_unused_653_);
v___x_647_ = v___y_644_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_dec(v___y_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v_a_642_);
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_642_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
lean_dec(v_a_642_);
return v___y_644_;
}
}
else
{
lean_dec(v_a_642_);
return v___y_644_;
}
}
}
else
{
lean_dec_ref(v_args_640_);
return v___x_641_;
}
}
}
v___jp_488_:
{
uint8_t v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = 1;
v___x_490_ = lean_box(v___x_489_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(lean_object* v_fvarId_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
uint8_t v___x_673_; lean_object* v___x_674_; 
v___x_673_ = 0;
v___x_674_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_673_, v_fvarId_665_, v_a_669_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_688_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_688_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_688_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_688_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
if (lean_obj_tag(v_a_675_) == 1)
{
lean_object* v_val_679_; lean_object* v_value_680_; uint8_t v___x_681_; lean_object* v___x_682_; 
lean_del_object(v___x_677_);
v_val_679_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_a_675_, 1);
v_value_680_ = lean_ctor_get(v_val_679_, 3);
lean_inc(v_value_680_);
lean_dec(v_val_679_);
v___x_681_ = 0;
v___x_682_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_681_, v_value_680_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_682_;
}
else
{
uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
lean_dec(v_a_675_);
v___x_683_ = 0;
v___x_684_ = lean_box(v___x_683_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_684_);
v___x_686_ = v___x_677_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
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
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_a_689_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_674_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_674_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object* v_fvarId_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_705_; lean_object* v_fvarDecisionCache_706_; lean_object* v___x_707_; 
v___x_705_ = lean_st_ref_get(v_a_699_);
v_fvarDecisionCache_706_ = lean_ctor_get(v___x_705_, 1);
lean_inc_ref(v_fvarDecisionCache_706_);
lean_dec(v___x_705_);
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_fvarDecisionCache_706_, v_fvarId_697_);
lean_dec_ref(v_fvarDecisionCache_706_);
if (lean_obj_tag(v___x_707_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_fvarId_697_);
v_val_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_val_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 0);
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_val_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
else
{
lean_object* v___x_716_; 
lean_dec(v___x_707_);
v___x_716_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_736_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_736_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_736_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_736_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v_decls_722_; lean_object* v_fvarDecisionCache_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_735_; 
v___x_721_ = lean_st_ref_take(v_a_699_);
v_decls_722_ = lean_ctor_get(v___x_721_, 0);
v_fvarDecisionCache_723_ = lean_ctor_get(v___x_721_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_735_ == 0)
{
v___x_725_ = v___x_721_;
v_isShared_726_ = v_isSharedCheck_735_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_fvarDecisionCache_723_);
lean_inc(v_decls_722_);
lean_dec(v___x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_735_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
lean_inc(v_a_717_);
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_fvarDecisionCache_723_, v_fvarId_697_, v_a_717_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 1, v___x_727_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_decls_722_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_734_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_st_ref_put(v_a_699_, v___x_729_);
if (v_isShared_720_ == 0)
{
v___x_732_ = v___x_719_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_717_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_697_);
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object* v_arg_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
if (lean_obj_tag(v_arg_737_) == 1)
{
lean_object* v_fvarId_745_; lean_object* v___x_746_; 
v_fvarId_745_ = lean_ctor_get(v_arg_737_, 0);
lean_inc(v_fvarId_745_);
lean_dec_ref_known(v_arg_737_, 1);
v___x_746_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_745_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
return v___x_746_;
}
else
{
uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec(v_arg_737_);
v___x_747_ = 1;
v___x_748_ = lean_box(v___x_747_);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object* v_arg_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v_arg_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(lean_object* v_fvarId_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_fvarId_759_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object* v_fvarId_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object* v___x_777_, lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
uint8_t v___x_15514__boxed_788_; size_t v_i_boxed_789_; size_t v_stop_boxed_790_; lean_object* v_res_791_; 
v___x_15514__boxed_788_ = lean_unbox(v___x_777_);
v_i_boxed_789_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_790_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_791_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___x_15514__boxed_788_, v_as_778_, v_i_boxed_789_, v_stop_boxed_790_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v_as_778_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(lean_object* v_as_792_, lean_object* v_i_793_, lean_object* v_stop_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
size_t v_i_boxed_802_; size_t v_stop_boxed_803_; lean_object* v_res_804_; 
v_i_boxed_802_ = lean_unbox_usize(v_i_793_);
lean_dec(v_i_793_);
v_stop_boxed_803_ = lean_unbox_usize(v_stop_794_);
lean_dec(v_stop_794_);
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_as_792_, v_i_boxed_802_, v_stop_boxed_803_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec_ref(v_as_792_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object* v_isRoot_805_, lean_object* v_v_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
uint8_t v_isRoot_boxed_814_; lean_object* v_res_815_; 
v_isRoot_boxed_814_ = lean_unbox(v_isRoot_805_);
v_res_815_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v_isRoot_boxed_814_, v_v_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object* v_00_u03b2_816_, lean_object* v_m_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_817_, v_a_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___boxed(lean_object* v_00_u03b2_820_, lean_object* v_m_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(v_00_u03b2_820_, v_m_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_m_821_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(lean_object* v_00_u03b2_824_, lean_object* v_m_825_, lean_object* v_a_826_, lean_object* v_b_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_m_825_, v_a_826_, v_b_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(lean_object* v_00_u03b2_829_, lean_object* v_a_830_, lean_object* v_x_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_830_, v_x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___boxed(lean_object* v_00_u03b2_833_, lean_object* v_a_834_, lean_object* v_x_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(v_00_u03b2_833_, v_a_834_, v_x_835_);
lean_dec(v_x_835_);
lean_dec(v_a_834_);
return v_res_836_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(lean_object* v_00_u03b2_837_, lean_object* v_a_838_, lean_object* v_x_839_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_838_, v_x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___boxed(lean_object* v_00_u03b2_841_, lean_object* v_a_842_, lean_object* v_x_843_){
_start:
{
uint8_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(v_00_u03b2_841_, v_a_842_, v_x_843_);
lean_dec(v_x_843_);
lean_dec(v_a_842_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10(lean_object* v_00_u03b2_846_, lean_object* v_data_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_data_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11(lean_object* v_00_u03b2_849_, lean_object* v_a_850_, lean_object* v_b_851_, lean_object* v_x_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_850_, v_b_851_, v_x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_854_, lean_object* v_i_855_, lean_object* v_source_856_, lean_object* v_target_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v_i_855_, v_source_856_, v_target_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_x_860_, v_x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(lean_object* v_prevArrayId_868_, lean_object* v_decl_869_, lean_object* v_k_870_, lean_object* v_illegalSet_871_, lean_object* v_size_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_decl_884_; lean_object* v_k_885_; lean_object* v_illegalSet_886_; lean_object* v_zero_894_; uint8_t v_isZero_895_; 
v_zero_894_ = lean_unsigned_to_nat(0u);
v_isZero_895_ = lean_nat_dec_eq(v_size_872_, v_zero_894_);
if (v_isZero_895_ == 1)
{
lean_object* v___x_896_; lean_object* v___x_897_; 
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
lean_dec(v_prevArrayId_868_);
v___x_896_ = lean_box(0);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
else
{
lean_object* v_value_898_; 
v_value_898_ = lean_ctor_get(v_decl_869_, 3);
if (lean_obj_tag(v_value_898_) == 3)
{
lean_object* v_declName_899_; 
v_declName_899_ = lean_ctor_get(v_value_898_, 0);
if (lean_obj_tag(v_declName_899_) == 1)
{
lean_object* v_pre_900_; 
v_pre_900_ = lean_ctor_get(v_declName_899_, 0);
if (lean_obj_tag(v_pre_900_) == 1)
{
lean_object* v_pre_901_; 
v_pre_901_ = lean_ctor_get(v_pre_900_, 0);
if (lean_obj_tag(v_pre_901_) == 0)
{
lean_object* v_fvarId_902_; lean_object* v_args_903_; lean_object* v_str_904_; lean_object* v_str_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_fvarId_902_ = lean_ctor_get(v_decl_869_, 0);
v_args_903_ = lean_ctor_get(v_value_898_, 2);
v_str_904_ = lean_ctor_get(v_declName_899_, 1);
v_str_905_ = lean_ctor_get(v_pre_900_, 1);
v___x_906_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_907_ = lean_string_dec_eq(v_str_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
lean_dec(v_prevArrayId_868_);
goto v___jp_880_;
}
else
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_909_ = lean_string_dec_eq(v_str_904_, v___x_908_);
if (v___x_909_ == 0)
{
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
lean_dec(v_prevArrayId_868_);
goto v___jp_880_;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_910_ = lean_array_get_size(v_args_903_);
v___x_911_ = lean_unsigned_to_nat(3u);
v___x_912_ = lean_nat_dec_eq(v___x_910_, v___x_911_);
if (v___x_912_ == 0)
{
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
lean_dec(v_prevArrayId_868_);
goto v___jp_880_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_array_fget(v_args_903_, v___x_913_);
if (lean_obj_tag(v___x_914_) == 1)
{
lean_object* v_fvarId_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_1032_; 
v_fvarId_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_1032_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_fvarId_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_1032_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
uint8_t v___x_919_; 
v___x_919_ = l_Lean_instBEqFVarId_beq(v_fvarId_915_, v_prevArrayId_868_);
lean_dec(v_prevArrayId_868_);
lean_dec(v_fvarId_915_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
v___x_920_ = lean_box(0);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 0);
lean_ctor_set(v___x_917_, 0, v___x_920_);
v___x_922_ = v___x_917_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_del_object(v___x_917_);
v___x_924_ = lean_unsigned_to_nat(2u);
v___x_925_ = lean_array_fget_borrowed(v_args_903_, v___x_924_);
lean_inc(v___x_925_);
v___x_926_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_925_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_1023_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_1023_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_1023_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
uint8_t v___x_931_; 
v___x_931_ = lean_unbox(v_a_927_);
lean_dec(v_a_927_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_934_; 
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
v___x_932_ = lean_box(0);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
else
{
lean_object* v_n_936_; uint8_t v___x_937_; 
v_n_936_ = lean_nat_sub(v_size_872_, v___x_913_);
lean_dec(v_size_872_);
v___x_937_ = lean_nat_dec_eq(v_n_936_, v_zero_894_);
if (v___x_937_ == 0)
{
lean_inc(v_fvarId_902_);
lean_dec_ref(v_decl_869_);
if (lean_obj_tag(v_k_870_) == 0)
{
lean_object* v_decl_938_; lean_object* v_k_939_; lean_object* v___x_940_; 
lean_del_object(v___x_929_);
v_decl_938_ = lean_ctor_get(v_k_870_, 0);
lean_inc_ref(v_decl_938_);
v_k_939_ = lean_ctor_get(v_k_870_, 1);
lean_inc_ref(v_k_939_);
lean_dec_ref_known(v_k_870_, 2);
lean_inc(v_fvarId_902_);
v___x_940_ = l_Lean_FVarIdSet_insert(v_illegalSet_871_, v_fvarId_902_);
v_prevArrayId_868_ = v_fvarId_902_;
v_decl_869_ = v_decl_938_;
v_k_870_ = v_k_939_;
v_illegalSet_871_ = v___x_940_;
v_size_872_ = v_n_936_;
goto _start;
}
else
{
lean_object* v___x_942_; lean_object* v___x_944_; 
lean_dec(v_n_936_);
lean_dec(v_fvarId_902_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
v___x_942_ = lean_box(0);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_942_);
v___x_944_ = v___x_929_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
else
{
lean_dec(v_n_936_);
lean_del_object(v___x_929_);
if (lean_obj_tag(v_k_870_) == 0)
{
lean_object* v_decl_946_; lean_object* v_value_947_; 
v_decl_946_ = lean_ctor_get(v_k_870_, 0);
lean_inc_ref(v_decl_946_);
v_value_947_ = lean_ctor_get(v_decl_946_, 3);
lean_inc(v_value_947_);
if (lean_obj_tag(v_value_947_) == 3)
{
lean_object* v_declName_948_; 
v_declName_948_ = lean_ctor_get(v_value_947_, 0);
lean_inc(v_declName_948_);
if (lean_obj_tag(v_declName_948_) == 1)
{
lean_object* v_pre_949_; 
v_pre_949_ = lean_ctor_get(v_declName_948_, 0);
lean_inc(v_pre_949_);
if (lean_obj_tag(v_pre_949_) == 1)
{
lean_object* v_pre_950_; 
v_pre_950_ = lean_ctor_get(v_pre_949_, 0);
lean_inc(v_pre_950_);
if (lean_obj_tag(v_pre_950_) == 0)
{
lean_object* v_k_951_; lean_object* v_fvarId_952_; lean_object* v_binderName_953_; lean_object* v_type_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1021_; 
v_k_951_ = lean_ctor_get(v_k_870_, 1);
v_fvarId_952_ = lean_ctor_get(v_decl_946_, 0);
v_binderName_953_ = lean_ctor_get(v_decl_946_, 1);
v_type_954_ = lean_ctor_get(v_decl_946_, 2);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_decl_946_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_decl_946_, 3);
lean_dec(v_unused_1022_);
v___x_956_ = v_decl_946_;
v_isShared_957_ = v_isSharedCheck_1021_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_type_954_);
lean_inc(v_binderName_953_);
lean_inc(v_fvarId_952_);
lean_dec(v_decl_946_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1021_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_us_958_; lean_object* v_args_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1019_; 
v_us_958_ = lean_ctor_get(v_value_947_, 1);
v_args_959_ = lean_ctor_get(v_value_947_, 2);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_value_947_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; 
v_unused_1020_ = lean_ctor_get(v_value_947_, 0);
lean_dec(v_unused_1020_);
v___x_961_ = v_value_947_;
v_isShared_962_ = v_isSharedCheck_1019_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_args_959_);
lean_inc(v_us_958_);
lean_dec(v_value_947_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1019_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_str_963_; lean_object* v_str_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_str_963_ = lean_ctor_get(v_declName_948_, 1);
lean_inc_ref(v_str_963_);
lean_dec_ref_known(v_declName_948_, 2);
v_str_964_ = lean_ctor_get(v_pre_949_, 1);
lean_inc_ref(v_str_964_);
lean_dec_ref_known(v_pre_949_, 2);
v___x_965_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2));
v___x_966_ = lean_string_dec_eq(v_str_964_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_967_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3));
v___x_968_ = lean_string_dec_eq(v_str_964_, v___x_967_);
lean_dec_ref(v_str_964_);
if (v___x_968_ == 0)
{
lean_dec_ref(v_str_963_);
lean_del_object(v___x_961_);
lean_dec_ref(v_args_959_);
lean_dec(v_us_958_);
lean_del_object(v___x_956_);
lean_dec_ref(v_type_954_);
lean_dec(v_binderName_953_);
lean_dec(v_fvarId_952_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
else
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_970_ = lean_string_dec_eq(v_str_963_, v___x_969_);
lean_dec_ref(v_str_963_);
if (v___x_970_ == 0)
{
lean_del_object(v___x_961_);
lean_dec_ref(v_args_959_);
lean_dec(v_us_958_);
lean_del_object(v___x_956_);
lean_dec_ref(v_type_954_);
lean_dec(v_binderName_953_);
lean_dec(v_fvarId_952_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
else
{
lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_971_ = lean_array_get_size(v_args_959_);
v___x_972_ = lean_nat_dec_eq(v___x_971_, v___x_913_);
if (v___x_972_ == 0)
{
lean_del_object(v___x_961_);
lean_dec_ref(v_args_959_);
lean_dec(v_us_958_);
lean_del_object(v___x_956_);
lean_dec_ref(v_type_954_);
lean_dec(v_binderName_953_);
lean_dec(v_fvarId_952_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = lean_array_fget(v_args_959_, v_zero_894_);
lean_dec_ref(v_args_959_);
if (lean_obj_tag(v___x_973_) == 1)
{
lean_object* v_fvarId_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_993_; 
v_fvarId_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_993_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_993_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_fvarId_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_993_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_instBEqFVarId_beq(v_fvarId_974_, v_fvarId_902_);
if (v___x_978_ == 0)
{
lean_del_object(v___x_976_);
lean_dec(v_fvarId_974_);
lean_del_object(v___x_961_);
lean_dec(v_us_958_);
lean_del_object(v___x_956_);
lean_dec_ref(v_type_954_);
lean_dec(v_binderName_953_);
lean_dec(v_fvarId_952_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
lean_inc_ref(v_k_951_);
lean_inc(v_fvarId_902_);
lean_dec_ref_known(v_k_870_, 2);
lean_dec_ref(v_decl_869_);
v___x_979_ = l_Lean_Name_str___override(v_pre_950_, v___x_967_);
v___x_980_ = l_Lean_Name_str___override(v___x_979_, v___x_969_);
if (v_isShared_977_ == 0)
{
v___x_982_ = v___x_976_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_fvarId_974_);
v___x_982_ = v_reuseFailAlloc_992_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_983_ = lean_mk_empty_array_with_capacity(v___x_913_);
v___x_984_ = lean_array_push(v___x_983_, v___x_982_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 2, v___x_984_);
lean_ctor_set(v___x_961_, 0, v___x_980_);
v___x_986_ = v___x_961_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_us_958_);
lean_ctor_set(v_reuseFailAlloc_991_, 2, v___x_984_);
v___x_986_ = v_reuseFailAlloc_991_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_988_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 3, v___x_986_);
v___x_988_ = v___x_956_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_fvarId_952_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_binderName_953_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_type_954_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v___x_986_);
v___x_988_ = v_reuseFailAlloc_990_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_FVarIdSet_insert(v_illegalSet_871_, v_fvarId_902_);
v_decl_884_ = v___x_988_;
v_k_885_ = v_k_951_;
v_illegalSet_886_ = v___x_989_;
goto v___jp_883_;
}
}
}
}
}
}
else
{
lean_dec(v___x_973_);
lean_del_object(v___x_961_);
lean_dec(v_us_958_);
lean_del_object(v___x_956_);
lean_dec_ref(v_type_954_);
lean_dec(v_binderName_953_);
lean_dec(v_fvarId_952_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
}
}
}
}
else
{
lean_object* v___x_994_; uint8_t v___x_995_; 
lean_dec_ref(v_str_964_);
v___x_994_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_995_ = lean_string_dec_eq(v_str_963_, v___x_994_);
lean_dec_ref(v_str_963_);
if (v___x_995_ == 0)
{
lean_del_object(v___x_961_);
lean_dec_ref(v_args_959_);
lean_dec(v_us_958_);
lean_del_object(v___x_956_);
lean_dec_ref(v_type_954_);
lean_dec(v_binderName_953_);
lean_dec(v_fvarId_952_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
else
{
lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_996_ = lean_array_get_size(v_args_959_);
v___x_997_ = lean_nat_dec_eq(v___x_996_, v___x_913_);
if (v___x_997_ == 0)
{
lean_del_object(v___x_961_);
lean_dec_ref(v_args_959_);
lean_dec(v_us_958_);
lean_del_object(v___x_956_);
lean_dec_ref(v_type_954_);
lean_dec(v_binderName_953_);
lean_dec(v_fvarId_952_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
else
{
lean_object* v___x_998_; 
v___x_998_ = lean_array_fget(v_args_959_, v_zero_894_);
lean_dec_ref(v_args_959_);
if (lean_obj_tag(v___x_998_) == 1)
{
lean_object* v_fvarId_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1018_; 
v_fvarId_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1018_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_fvarId_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1018_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
uint8_t v___x_1003_; 
v___x_1003_ = l_Lean_instBEqFVarId_beq(v_fvarId_999_, v_fvarId_902_);
if (v___x_1003_ == 0)
{
lean_del_object(v___x_1001_);
lean_dec(v_fvarId_999_);
lean_del_object(v___x_961_);
lean_dec(v_us_958_);
lean_del_object(v___x_956_);
lean_dec_ref(v_type_954_);
lean_dec(v_binderName_953_);
lean_dec(v_fvarId_952_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_inc_ref(v_k_951_);
lean_inc(v_fvarId_902_);
lean_dec_ref_known(v_k_870_, 2);
lean_dec_ref(v_decl_869_);
v___x_1004_ = l_Lean_Name_str___override(v_pre_950_, v___x_965_);
v___x_1005_ = l_Lean_Name_str___override(v___x_1004_, v___x_994_);
if (v_isShared_1002_ == 0)
{
v___x_1007_ = v___x_1001_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_fvarId_999_);
v___x_1007_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1008_ = lean_mk_empty_array_with_capacity(v___x_913_);
v___x_1009_ = lean_array_push(v___x_1008_, v___x_1007_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 2, v___x_1009_);
lean_ctor_set(v___x_961_, 0, v___x_1005_);
v___x_1011_ = v___x_961_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_us_958_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 3, v___x_1011_);
v___x_1013_ = v___x_956_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_fvarId_952_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_binderName_953_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_type_954_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_FVarIdSet_insert(v_illegalSet_871_, v_fvarId_902_);
v_decl_884_ = v___x_1013_;
v_k_885_ = v_k_951_;
v_illegalSet_886_ = v___x_1014_;
goto v___jp_883_;
}
}
}
}
}
}
else
{
lean_dec(v___x_998_);
lean_del_object(v___x_961_);
lean_dec(v_us_958_);
lean_del_object(v___x_956_);
lean_dec_ref(v_type_954_);
lean_dec(v_binderName_953_);
lean_dec(v_fvarId_952_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
}
}
}
}
}
}
else
{
lean_dec(v_pre_950_);
lean_dec_ref_known(v_pre_949_, 2);
lean_dec_ref_known(v_declName_948_, 2);
lean_dec_ref_known(v_value_947_, 3);
lean_dec_ref(v_decl_946_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
}
else
{
lean_dec_ref_known(v_declName_948_, 2);
lean_dec(v_pre_949_);
lean_dec_ref_known(v_value_947_, 3);
lean_dec_ref(v_decl_946_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
}
else
{
lean_dec(v_declName_948_);
lean_dec_ref_known(v_value_947_, 3);
lean_dec_ref(v_decl_946_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
}
else
{
lean_dec(v_value_947_);
lean_dec_ref(v_decl_946_);
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
}
else
{
v_decl_884_ = v_decl_869_;
v_k_885_ = v_k_870_;
v_illegalSet_886_ = v_illegalSet_871_;
goto v___jp_883_;
}
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
v_a_1024_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_926_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_926_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
else
{
lean_dec(v___x_914_);
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
lean_dec(v_prevArrayId_868_);
goto v___jp_880_;
}
}
}
}
}
else
{
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
lean_dec(v_prevArrayId_868_);
goto v___jp_880_;
}
}
else
{
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
lean_dec(v_prevArrayId_868_);
goto v___jp_880_;
}
}
else
{
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
lean_dec(v_prevArrayId_868_);
goto v___jp_880_;
}
}
else
{
lean_dec(v_size_872_);
lean_dec(v_illegalSet_871_);
lean_dec_ref(v_k_870_);
lean_dec_ref(v_decl_869_);
lean_dec(v_prevArrayId_868_);
goto v___jp_880_;
}
}
v___jp_880_:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_box(0);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
v___jp_883_:
{
uint8_t v___x_887_; uint8_t v___x_888_; 
v___x_887_ = 0;
v___x_888_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_887_, v_k_885_, v_illegalSet_886_);
lean_dec(v_illegalSet_886_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v_decl_884_);
lean_ctor_set(v___x_889_, 1, v_k_885_);
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec_ref(v_k_885_);
lean_dec_ref(v_decl_884_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___boxed(lean_object* v_prevArrayId_1033_, lean_object* v_decl_1034_, lean_object* v_k_1035_, lean_object* v_illegalSet_1036_, lean_object* v_size_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_prevArrayId_1033_, v_decl_1034_, v_k_1035_, v_illegalSet_1036_, v_size_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(lean_object* v_decl_1048_, lean_object* v_k_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_value_1066_; 
v_value_1066_ = lean_ctor_get(v_decl_1048_, 3);
if (lean_obj_tag(v_value_1066_) == 3)
{
lean_object* v_declName_1067_; 
v_declName_1067_ = lean_ctor_get(v_value_1066_, 0);
if (lean_obj_tag(v_declName_1067_) == 1)
{
lean_object* v_pre_1068_; 
v_pre_1068_ = lean_ctor_get(v_declName_1067_, 0);
if (lean_obj_tag(v_pre_1068_) == 1)
{
lean_object* v_pre_1069_; 
v_pre_1069_ = lean_ctor_get(v_pre_1068_, 0);
if (lean_obj_tag(v_pre_1069_) == 0)
{
lean_object* v_args_1070_; lean_object* v_str_1071_; lean_object* v_str_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_args_1070_ = lean_ctor_get(v_value_1066_, 2);
v_str_1071_ = lean_ctor_get(v_declName_1067_, 1);
v_str_1072_ = lean_ctor_get(v_pre_1068_, 1);
v___x_1073_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1074_ = lean_string_dec_eq(v_str_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1063_;
}
else
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_1076_ = lean_string_dec_eq(v_str_1071_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1063_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = lean_array_get_size(v_args_1070_);
v___x_1078_ = lean_unsigned_to_nat(3u);
v___x_1079_ = lean_nat_dec_eq(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1063_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_array_fget_borrowed(v_args_1070_, v___x_1080_);
if (lean_obj_tag(v___x_1081_) == 1)
{
lean_object* v_fvarId_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; 
v_fvarId_1082_ = lean_ctor_get(v___x_1081_, 0);
v___x_1083_ = 0;
v___x_1084_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_1083_, v_fvarId_1082_, v_a_1053_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1140_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1140_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1140_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
if (lean_obj_tag(v_a_1085_) == 1)
{
lean_object* v_val_1089_; lean_object* v_value_1090_; 
lean_del_object(v___x_1087_);
v_val_1089_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_val_1089_);
lean_dec_ref_known(v_a_1085_, 1);
v_value_1090_ = lean_ctor_get(v_val_1089_, 3);
lean_inc(v_value_1090_);
if (lean_obj_tag(v_value_1090_) == 3)
{
lean_object* v_declName_1091_; 
v_declName_1091_ = lean_ctor_get(v_value_1090_, 0);
lean_inc(v_declName_1091_);
if (lean_obj_tag(v_declName_1091_) == 1)
{
lean_object* v_pre_1092_; 
v_pre_1092_ = lean_ctor_get(v_declName_1091_, 0);
lean_inc(v_pre_1092_);
if (lean_obj_tag(v_pre_1092_) == 1)
{
lean_object* v_pre_1093_; 
v_pre_1093_ = lean_ctor_get(v_pre_1092_, 0);
if (lean_obj_tag(v_pre_1093_) == 0)
{
lean_object* v_fvarId_1094_; lean_object* v_args_1095_; lean_object* v_str_1096_; lean_object* v_str_1097_; uint8_t v___x_1098_; 
v_fvarId_1094_ = lean_ctor_get(v_val_1089_, 0);
lean_inc(v_fvarId_1094_);
lean_dec(v_val_1089_);
v_args_1095_ = lean_ctor_get(v_value_1090_, 2);
lean_inc_ref(v_args_1095_);
lean_dec_ref_known(v_value_1090_, 3);
v_str_1096_ = lean_ctor_get(v_declName_1091_, 1);
lean_inc_ref(v_str_1096_);
lean_dec_ref_known(v_declName_1091_, 2);
v_str_1097_ = lean_ctor_get(v_pre_1092_, 1);
lean_inc_ref(v_str_1097_);
lean_dec_ref_known(v_pre_1092_, 2);
v___x_1098_ = lean_string_dec_eq(v_str_1097_, v___x_1073_);
lean_dec_ref(v_str_1097_);
if (v___x_1098_ == 0)
{
lean_dec_ref(v_str_1096_);
lean_dec_ref(v_args_1095_);
lean_dec(v_fvarId_1094_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1060_;
}
else
{
lean_object* v___x_1099_; lean_object* v_sizeFVar_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1099_ = lean_box(1);
v___x_1122_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1123_ = lean_string_dec_eq(v_str_1096_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1125_ = lean_string_dec_eq(v_str_1096_, v___x_1124_);
lean_dec_ref(v_str_1096_);
if (v___x_1125_ == 0)
{
lean_dec_ref(v_args_1095_);
lean_dec(v_fvarId_1094_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1060_;
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1126_ = lean_array_get_size(v_args_1095_);
v___x_1127_ = lean_unsigned_to_nat(2u);
v___x_1128_ = lean_nat_dec_eq(v___x_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_dec_ref(v_args_1095_);
lean_dec(v_fvarId_1094_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1060_;
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_array_fget(v_args_1095_, v___x_1080_);
lean_dec_ref(v_args_1095_);
if (lean_obj_tag(v___x_1129_) == 1)
{
lean_object* v_fvarId_1130_; 
v_fvarId_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_fvarId_1130_);
lean_dec_ref_known(v___x_1129_, 1);
v_sizeFVar_1101_ = v_fvarId_1130_;
v___y_1102_ = v_a_1050_;
v___y_1103_ = v_a_1051_;
v___y_1104_ = v_a_1052_;
v___y_1105_ = v_a_1053_;
v___y_1106_ = v_a_1054_;
v___y_1107_ = v_a_1055_;
goto v___jp_1100_;
}
else
{
lean_dec(v___x_1129_);
lean_dec(v_fvarId_1094_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1060_;
}
}
}
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
lean_dec_ref(v_str_1096_);
v___x_1131_ = lean_array_get_size(v_args_1095_);
v___x_1132_ = lean_unsigned_to_nat(2u);
v___x_1133_ = lean_nat_dec_eq(v___x_1131_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_dec_ref(v_args_1095_);
lean_dec(v_fvarId_1094_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1060_;
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_array_fget(v_args_1095_, v___x_1080_);
lean_dec_ref(v_args_1095_);
if (lean_obj_tag(v___x_1134_) == 1)
{
lean_object* v_fvarId_1135_; 
v_fvarId_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_fvarId_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v_sizeFVar_1101_ = v_fvarId_1135_;
v___y_1102_ = v_a_1050_;
v___y_1103_ = v_a_1051_;
v___y_1104_ = v_a_1052_;
v___y_1105_ = v_a_1053_;
v___y_1106_ = v_a_1054_;
v___y_1107_ = v_a_1055_;
goto v___jp_1100_;
}
else
{
lean_dec(v___x_1134_);
lean_dec(v_fvarId_1094_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1060_;
}
}
}
v___jp_1100_:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1083_, v_sizeFVar_1101_, v___y_1105_);
lean_dec(v_sizeFVar_1101_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
if (lean_obj_tag(v_a_1109_) == 1)
{
lean_object* v_val_1110_; 
v_val_1110_ = lean_ctor_get(v_a_1109_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v_a_1109_, 1);
if (lean_obj_tag(v_val_1110_) == 0)
{
lean_object* v_value_1111_; 
v_value_1111_ = lean_ctor_get(v_val_1110_, 0);
lean_inc_ref(v_value_1111_);
lean_dec_ref_known(v_val_1110_, 1);
if (lean_obj_tag(v_value_1111_) == 0)
{
lean_object* v_val_1112_; lean_object* v___x_1113_; 
v_val_1112_ = lean_ctor_get(v_value_1111_, 0);
lean_inc(v_val_1112_);
lean_dec_ref_known(v_value_1111_, 1);
v___x_1113_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_fvarId_1094_, v_decl_1048_, v_k_1049_, v___x_1099_, v_val_1112_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
return v___x_1113_;
}
else
{
lean_dec_ref(v_value_1111_);
lean_dec(v_fvarId_1094_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1057_;
}
}
else
{
lean_dec(v_val_1110_);
lean_dec(v_fvarId_1094_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1057_;
}
}
else
{
lean_dec(v_a_1109_);
lean_dec(v_fvarId_1094_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1057_;
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_fvarId_1094_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
v_a_1114_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1108_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1108_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1092_, 2);
lean_dec_ref_known(v_declName_1091_, 2);
lean_dec_ref_known(v_value_1090_, 3);
lean_dec(v_val_1089_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1060_;
}
}
else
{
lean_dec_ref_known(v_declName_1091_, 2);
lean_dec(v_pre_1092_);
lean_dec_ref_known(v_value_1090_, 3);
lean_dec(v_val_1089_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1060_;
}
}
else
{
lean_dec_ref_known(v_value_1090_, 3);
lean_dec(v_declName_1091_);
lean_dec(v_val_1089_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1060_;
}
}
else
{
lean_dec(v_value_1090_);
lean_dec(v_val_1089_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1060_;
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
lean_dec(v_a_1085_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
v___x_1136_ = lean_box(0);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1136_);
v___x_1138_ = v___x_1087_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
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
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
v_a_1141_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1084_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1084_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
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
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1063_;
}
}
}
}
}
else
{
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1063_;
}
}
else
{
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1063_;
}
}
else
{
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1063_;
}
}
else
{
lean_dec_ref(v_k_1049_);
lean_dec_ref(v_decl_1048_);
goto v___jp_1063_;
}
v___jp_1057_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
v___jp_1060_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
v___jp_1063_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___boxed(lean_object* v_decl_1149_, lean_object* v_k_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1149_, v_k_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
return v_res_1158_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1159_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0);
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(lean_object* v_env_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; lean_object* v_nextMacroScope_1168_; lean_object* v_ngen_1169_; lean_object* v_auxDeclNGen_1170_; lean_object* v_traceState_1171_; lean_object* v_messages_1172_; lean_object* v_infoState_1173_; lean_object* v_snapshotTasks_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1185_; 
v___x_1167_ = lean_st_ref_take(v___y_1165_);
v_nextMacroScope_1168_ = lean_ctor_get(v___x_1167_, 1);
v_ngen_1169_ = lean_ctor_get(v___x_1167_, 2);
v_auxDeclNGen_1170_ = lean_ctor_get(v___x_1167_, 3);
v_traceState_1171_ = lean_ctor_get(v___x_1167_, 4);
v_messages_1172_ = lean_ctor_get(v___x_1167_, 6);
v_infoState_1173_ = lean_ctor_get(v___x_1167_, 7);
v_snapshotTasks_1174_ = lean_ctor_get(v___x_1167_, 8);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; lean_object* v_unused_1187_; 
v_unused_1186_ = lean_ctor_get(v___x_1167_, 5);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v___x_1167_, 0);
lean_dec(v_unused_1187_);
v___x_1176_ = v___x_1167_;
v_isShared_1177_ = v_isSharedCheck_1185_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_snapshotTasks_1174_);
lean_inc(v_infoState_1173_);
lean_inc(v_messages_1172_);
lean_inc(v_traceState_1171_);
lean_inc(v_auxDeclNGen_1170_);
lean_inc(v_ngen_1169_);
lean_inc(v_nextMacroScope_1168_);
lean_dec(v___x_1167_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1185_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 5, v___x_1178_);
lean_ctor_set(v___x_1176_, 0, v_env_1164_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_env_1164_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_nextMacroScope_1168_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_ngen_1169_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_auxDeclNGen_1170_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_traceState_1171_);
lean_ctor_set(v_reuseFailAlloc_1184_, 5, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1184_, 6, v_messages_1172_);
lean_ctor_set(v_reuseFailAlloc_1184_, 7, v_infoState_1173_);
lean_ctor_set(v_reuseFailAlloc_1184_, 8, v_snapshotTasks_1174_);
v___x_1180_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_st_ref_put(v___y_1165_, v___x_1180_);
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___boxed(lean_object* v_env_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1188_, v___y_1189_);
lean_dec(v___y_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(lean_object* v_env_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1192_, v___y_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(lean_object* v_env_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_env_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(size_t v_sz_1210_, size_t v_i_1211_, lean_object* v_bs_1212_, uint8_t v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v___x_1220_; 
v___x_1220_ = lean_usize_dec_lt(v_i_1211_, v_sz_1210_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_bs_1212_);
return v___x_1221_;
}
else
{
uint8_t v___x_1222_; lean_object* v_v_1223_; lean_object* v___x_1224_; 
v___x_1222_ = 0;
v_v_1223_ = lean_array_uget_borrowed(v_bs_1212_, v_i_1211_);
lean_inc(v_v_1223_);
v___x_1224_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_1222_, v_v_1223_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1226_; lean_object* v_bs_x27_1227_; size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1226_ = lean_unsigned_to_nat(0u);
v_bs_x27_1227_ = lean_array_uset(v_bs_1212_, v_i_1211_, v___x_1226_);
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1211_, v___x_1228_);
v___x_1230_ = lean_array_uset(v_bs_x27_1227_, v_i_1211_, v_a_1225_);
v_i_1211_ = v___x_1229_;
v_bs_1212_ = v___x_1230_;
goto _start;
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec_ref(v_bs_1212_);
v_a_1232_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1224_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1224_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(lean_object* v_sz_1240_, lean_object* v_i_1241_, lean_object* v_bs_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
size_t v_sz_boxed_1250_; size_t v_i_boxed_1251_; uint8_t v___y_8180__boxed_1252_; lean_object* v_res_1253_; 
v_sz_boxed_1250_ = lean_unbox_usize(v_sz_1240_);
lean_dec(v_sz_1240_);
v_i_boxed_1251_ = lean_unbox_usize(v_i_1241_);
lean_dec(v_i_1241_);
v___y_8180__boxed_1252_ = lean_unbox(v___y_1243_);
v_res_1253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_boxed_1250_, v_i_boxed_1251_, v_bs_1242_, v___y_8180__boxed_1252_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
return v_res_1253_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_box(0);
v___x_1257_ = lean_unsigned_to_nat(16u);
v___x_1258_ = lean_mk_array(v___x_1257_, v___x_1256_);
return v___x_1258_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1);
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
lean_ctor_set(v___x_1261_, 1, v___x_1259_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3(void){
_start:
{
uint8_t v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = 0;
v___x_1263_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(lean_object* v_decl_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v_type_1282_; lean_object* v_value_1283_; lean_object* v___x_1284_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0));
v___x_1281_ = lean_st_mk_ref(v___x_1280_);
v_type_1282_ = lean_ctor_get(v_decl_1272_, 2);
lean_inc_ref(v_type_1282_);
v_value_1283_ = lean_ctor_get(v_decl_1272_, 3);
lean_inc(v_value_1283_);
v___x_1284_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_1283_, v___x_1281_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; lean_object* v_a_1295_; size_t v_sz_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
lean_dec_ref_known(v___x_1284_, 1);
v___x_1285_ = lean_st_ref_get(v___x_1281_);
lean_dec(v___x_1281_);
v___x_1286_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_1287_ = lean_st_mk_ref(v___x_1286_);
v___x_1288_ = 0;
v___x_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1289_, 0, v_decl_1272_);
v___x_1290_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3);
v___x_1291_ = l_Array_reverse___redArg(v___x_1285_);
v___x_1292_ = lean_array_push(v___x_1291_, v___x_1289_);
v___x_1293_ = 0;
v_sz_1377_ = lean_array_size(v___x_1292_);
v___x_1378_ = ((size_t)0ULL);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_1377_, v___x_1378_, v___x_1292_, v___x_1293_, v___x_1287_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
v___x_1381_ = lean_st_ref_get(v___x_1287_);
lean_dec(v___x_1287_);
lean_dec(v___x_1381_);
v_a_1295_ = v_a_1380_;
goto v___jp_1294_;
}
else
{
lean_dec(v___x_1287_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1382_; 
v_a_1382_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1379_, 1);
v_a_1295_ = v_a_1382_;
goto v___jp_1294_;
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v_type_1282_);
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
v___jp_1294_:
{
lean_object* v___x_1296_; lean_object* v_env_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1296_ = lean_st_ref_get(v_a_1278_);
v_env_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc_ref_n(v_env_1297_, 2);
lean_dec(v___x_1296_);
v___x_1298_ = lean_array_get_size(v_a_1295_);
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_nat_sub(v___x_1298_, v___x_1299_);
v___x_1301_ = lean_array_get_borrowed(v___x_1290_, v_a_1295_, v___x_1300_);
lean_dec(v___x_1300_);
v___x_1302_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1301_);
v___x_1303_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
v___x_1304_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1288_, v_a_1295_, v___x_1303_);
lean_dec_ref(v_a_1295_);
v___x_1305_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4));
lean_inc_ref(v___x_1304_);
v___x_1306_ = l_Lean_Compiler_LCNF_Code_toExpr(v___x_1288_, v___x_1304_, v___x_1305_);
v___x_1307_ = l_Lean_getClosedTermName_x3f(v_env_1297_, v___x_1306_);
if (lean_obj_tag(v___x_1307_) == 1)
{
lean_object* v_val_1308_; lean_object* v___x_1309_; 
lean_dec_ref(v___x_1306_);
lean_dec_ref(v_env_1297_);
lean_dec_ref(v_type_1282_);
v_val_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1309_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1288_, v___x_1304_, v_a_1276_);
lean_dec_ref(v___x_1304_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1309_, 0);
lean_dec(v_unused_1317_);
v___x_1311_ = v___x_1309_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v___x_1309_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v_val_1308_);
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_val_1308_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v_val_1308_);
v_a_1318_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1309_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1309_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v___x_1326_; lean_object* v_baseName_1327_; lean_object* v_decls_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v___x_1307_);
v___x_1326_ = lean_st_ref_get(v_a_1274_);
v_baseName_1327_ = lean_ctor_get(v_a_1273_, 0);
v_decls_1328_ = lean_ctor_get(v___x_1326_, 0);
lean_inc_ref(v_decls_1328_);
lean_dec(v___x_1326_);
v___x_1329_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6));
v___x_1330_ = lean_array_get_size(v_decls_1328_);
lean_dec_ref(v_decls_1328_);
v___x_1331_ = lean_name_append_index_after(v___x_1329_, v___x_1330_);
lean_inc(v_baseName_1327_);
v___x_1332_ = l_Lean_Name_append(v_baseName_1327_, v___x_1331_);
lean_inc(v___x_1332_);
v___x_1333_ = l_Lean_cacheClosedTermName(v_env_1297_, v___x_1306_, v___x_1332_);
v___x_1334_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v___x_1333_, v_a_1278_);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v___x_1334_, 0);
lean_dec(v_unused_1376_);
v___x_1336_ = v___x_1334_;
v_isShared_1337_ = v_isSharedCheck_1375_;
goto v_resetjp_1335_;
}
else
{
lean_dec(v___x_1334_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1375_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1338_ = lean_box(0);
v___x_1339_ = 1;
lean_inc(v___x_1332_);
v___x_1340_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1340_, 0, v___x_1332_);
lean_ctor_set(v___x_1340_, 1, v___x_1338_);
lean_ctor_set(v___x_1340_, 2, v_type_1282_);
lean_ctor_set(v___x_1340_, 3, v___x_1305_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*4, v___x_1339_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1304_);
v___x_1342_ = v___x_1336_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1304_);
v___x_1342_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1343_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7));
v___x_1344_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1344_, 0, v___x_1340_);
lean_ctor_set(v___x_1344_, 1, v___x_1342_);
lean_ctor_set(v___x_1344_, 2, v___x_1343_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3, v___x_1293_);
lean_inc_ref(v___x_1344_);
v___x_1345_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1344_, v_a_1278_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1364_; 
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v___x_1345_, 0);
lean_dec(v_unused_1365_);
v___x_1347_ = v___x_1345_;
v_isShared_1348_ = v_isSharedCheck_1364_;
goto v_resetjp_1346_;
}
else
{
lean_dec(v___x_1345_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1364_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v_decls_1350_; lean_object* v_fvarDecisionCache_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1363_; 
v___x_1349_ = lean_st_ref_take(v_a_1274_);
v_decls_1350_ = lean_ctor_get(v___x_1349_, 0);
v_fvarDecisionCache_1351_ = lean_ctor_get(v___x_1349_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1353_ = v___x_1349_;
v_isShared_1354_ = v_isSharedCheck_1363_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_fvarDecisionCache_1351_);
lean_inc(v_decls_1350_);
lean_dec(v___x_1349_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1363_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = lean_array_push(v_decls_1350_, v___x_1344_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1355_);
v___x_1357_ = v___x_1353_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_fvarDecisionCache_1351_);
v___x_1357_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_st_ref_put(v_a_1274_, v___x_1357_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1332_);
v___x_1360_ = v___x_1347_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1332_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref_known(v___x_1344_, 3);
lean_dec(v___x_1332_);
v_a_1366_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1345_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1345_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
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
lean_dec_ref(v_type_1282_);
lean_dec(v___x_1281_);
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
uint8_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = 0;
v___x_1409_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(lean_object* v_msg_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0);
v___x_1412_ = lean_panic_fn_borrowed(v___x_1411_, v_msg_1410_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1416_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2));
v___x_1417_ = lean_unsigned_to_nat(9u);
v___x_1418_ = lean_unsigned_to_nat(641u);
v___x_1419_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1));
v___x_1420_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0));
v___x_1421_ = l_mkPanicMessageWithDecl(v___x_1420_, v___x_1419_, v___x_1418_, v___x_1417_, v___x_1416_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* v_code_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_decl_1433_; lean_object* v_k_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; 
switch(lean_obj_tag(v_code_1424_))
{
case 0:
{
lean_object* v_decl_1548_; lean_object* v_k_1549_; lean_object* v_value_1550_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; 
v_decl_1548_ = lean_ctor_get(v_code_1424_, 0);
v_k_1549_ = lean_ctor_get(v_code_1424_, 1);
v_value_1550_ = lean_ctor_get(v_decl_1548_, 3);
lean_inc(v_value_1550_);
if (lean_obj_tag(v_value_1550_) == 3)
{
lean_object* v_declName_1747_; 
v_declName_1747_ = lean_ctor_get(v_value_1550_, 0);
if (lean_obj_tag(v_declName_1747_) == 1)
{
lean_object* v_pre_1748_; 
v_pre_1748_ = lean_ctor_get(v_declName_1747_, 0);
if (lean_obj_tag(v_pre_1748_) == 1)
{
lean_object* v_pre_1749_; 
v_pre_1749_ = lean_ctor_get(v_pre_1748_, 0);
if (lean_obj_tag(v_pre_1749_) == 0)
{
lean_object* v_args_1750_; lean_object* v_str_1751_; lean_object* v_str_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v_sizeId_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; 
v_args_1750_ = lean_ctor_get(v_value_1550_, 2);
v_str_1751_ = lean_ctor_get(v_declName_1747_, 1);
v_str_1752_ = lean_ctor_get(v_pre_1748_, 1);
v___x_1753_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1754_ = lean_string_dec_eq(v_str_1752_, v___x_1753_);
if (v___x_1754_ == 0)
{
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_2093_ = lean_string_dec_eq(v_str_1751_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_2095_ = lean_string_dec_eq(v_str_1751_, v___x_2094_);
if (v___x_2095_ == 0)
{
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v___x_2096_ = lean_array_get_size(v_args_1750_);
v___x_2097_ = lean_unsigned_to_nat(2u);
v___x_2098_ = lean_nat_dec_eq(v___x_2096_, v___x_2097_);
if (v___x_2098_ == 0)
{
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_unsigned_to_nat(1u);
v___x_2100_ = lean_array_fget_borrowed(v_args_1750_, v___x_2099_);
if (lean_obj_tag(v___x_2100_) == 1)
{
lean_object* v_fvarId_2101_; 
v_fvarId_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_fvarId_2101_);
v_sizeId_1960_ = v_fvarId_2101_;
v___y_1961_ = v_a_1425_;
v___y_1962_ = v_a_1426_;
v___y_1963_ = v_a_1427_;
v___y_1964_ = v_a_1428_;
v___y_1965_ = v_a_1429_;
v___y_1966_ = v_a_1430_;
goto v___jp_1959_;
}
else
{
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
goto v___jp_1551_;
}
}
}
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2102_ = lean_array_get_size(v_args_1750_);
v___x_2103_ = lean_unsigned_to_nat(2u);
v___x_2104_ = lean_nat_dec_eq(v___x_2102_, v___x_2103_);
if (v___x_2104_ == 0)
{
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = lean_array_fget_borrowed(v_args_1750_, v___x_2105_);
if (lean_obj_tag(v___x_2106_) == 1)
{
lean_object* v_fvarId_2107_; 
v_fvarId_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_fvarId_2107_);
v_sizeId_1960_ = v_fvarId_2107_;
v___y_1961_ = v_a_1425_;
v___y_1962_ = v_a_1426_;
v___y_1963_ = v_a_1427_;
v___y_1964_ = v_a_1428_;
v___y_1965_ = v_a_1429_;
v___y_1966_ = v_a_1430_;
goto v___jp_1959_;
}
else
{
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
goto v___jp_1551_;
}
}
}
}
v___jp_1755_:
{
lean_object* v___x_1762_; 
lean_inc_ref(v_k_1549_);
lean_inc_ref(v_decl_1548_);
v___x_1762_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1548_, v_k_1549_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
if (lean_obj_tag(v_a_1763_) == 1)
{
lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1835_; 
v_isSharedCheck_1835_ = !lean_is_exclusive(v_value_1550_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; lean_object* v_unused_1837_; lean_object* v_unused_1838_; 
v_unused_1836_ = lean_ctor_get(v_value_1550_, 2);
lean_dec(v_unused_1836_);
v_unused_1837_ = lean_ctor_get(v_value_1550_, 1);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_value_1550_, 0);
lean_dec(v_unused_1838_);
v___x_1765_ = v_value_1550_;
v_isShared_1766_ = v_isSharedCheck_1835_;
goto v_resetjp_1764_;
}
else
{
lean_dec(v_value_1550_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1835_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v_val_1767_; lean_object* v_fst_1768_; lean_object* v_snd_1769_; lean_object* v___x_1770_; 
v_val_1767_ = lean_ctor_get(v_a_1763_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v_a_1763_, 1);
v_fst_1768_ = lean_ctor_get(v_val_1767_, 0);
lean_inc_n(v_fst_1768_, 2);
v_snd_1769_ = lean_ctor_get(v_val_1767_, 1);
lean_inc(v_snd_1769_);
lean_dec(v_val_1767_);
v___x_1770_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1768_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = 0;
v___x_1773_ = lean_box(0);
v___x_1774_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 2, v___x_1774_);
lean_ctor_set(v___x_1765_, 1, v___x_1773_);
lean_ctor_set(v___x_1765_, 0, v_a_1771_);
v___x_1776_ = v___x_1765_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1771_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1826_, 2, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1772_, v_fst_1768_, v___x_1776_, v___y_1759_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1769_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1817_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1817_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1817_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
size_t v___x_1784_; size_t v___x_1785_; uint8_t v___x_1786_; 
v___x_1784_ = lean_ptr_addr(v_k_1549_);
v___x_1785_ = lean_ptr_addr(v_a_1780_);
v___x_1786_ = lean_usize_dec_eq(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1796_; 
v_isSharedCheck_1796_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; lean_object* v_unused_1798_; 
v_unused_1797_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1798_);
v___x_1788_ = v_code_1424_;
v_isShared_1789_ = v_isSharedCheck_1796_;
goto v_resetjp_1787_;
}
else
{
lean_dec(v_code_1424_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1796_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 1, v_a_1780_);
lean_ctor_set(v___x_1788_, 0, v_a_1778_);
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1778_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_a_1780_);
v___x_1791_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1793_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1791_);
v___x_1793_ = v___x_1782_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
size_t v___x_1799_; size_t v___x_1800_; uint8_t v___x_1801_; 
v___x_1799_ = lean_ptr_addr(v_decl_1548_);
v___x_1800_ = lean_ptr_addr(v_a_1778_);
v___x_1801_ = lean_usize_dec_eq(v___x_1799_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1811_; 
v_isSharedCheck_1811_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1811_ == 0)
{
lean_object* v_unused_1812_; lean_object* v_unused_1813_; 
v_unused_1812_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1812_);
v_unused_1813_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1813_);
v___x_1803_ = v_code_1424_;
v_isShared_1804_ = v_isSharedCheck_1811_;
goto v_resetjp_1802_;
}
else
{
lean_dec(v_code_1424_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1811_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v_a_1780_);
lean_ctor_set(v___x_1803_, 0, v_a_1778_);
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1778_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_a_1780_);
v___x_1806_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1806_);
v___x_1808_ = v___x_1782_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v___x_1815_; 
lean_dec(v_a_1780_);
lean_dec(v_a_1778_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v_code_1424_);
v___x_1815_ = v___x_1782_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_code_1424_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
else
{
lean_dec(v_a_1778_);
lean_dec_ref_known(v_code_1424_, 2);
return v___x_1779_;
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_snd_1769_);
lean_dec_ref_known(v_code_1424_, 2);
v_a_1818_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1777_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1777_);
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
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec(v_snd_1769_);
lean_dec(v_fst_1768_);
lean_del_object(v___x_1765_);
lean_dec_ref_known(v_code_1424_, 2);
v_a_1827_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1770_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1770_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
else
{
lean_object* v___x_1839_; 
lean_dec(v_a_1763_);
v___x_1839_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1754_, v_value_1550_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; uint8_t v___x_1841_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v___x_1841_ = lean_unbox(v_a_1840_);
lean_dec(v_a_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
lean_inc_ref(v_k_1549_);
v___x_1842_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1549_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1879_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1879_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1879_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
size_t v___x_1847_; size_t v___x_1848_; uint8_t v___x_1849_; 
v___x_1847_ = lean_ptr_addr(v_k_1549_);
v___x_1848_ = lean_ptr_addr(v_a_1843_);
v___x_1849_ = lean_usize_dec_eq(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1859_; 
lean_inc_ref(v_decl_1548_);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; lean_object* v_unused_1861_; 
v_unused_1860_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1861_);
v___x_1851_ = v_code_1424_;
v_isShared_1852_ = v_isSharedCheck_1859_;
goto v_resetjp_1850_;
}
else
{
lean_dec(v_code_1424_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1859_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v_a_1843_);
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_decl_1548_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_a_1843_);
v___x_1854_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1854_);
v___x_1856_ = v___x_1845_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
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
size_t v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = lean_ptr_addr(v_decl_1548_);
v___x_1863_ = lean_usize_dec_eq(v___x_1862_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1873_; 
lean_inc_ref(v_decl_1548_);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; lean_object* v_unused_1875_; 
v_unused_1874_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1874_);
v_unused_1875_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1875_);
v___x_1865_ = v_code_1424_;
v_isShared_1866_ = v_isSharedCheck_1873_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v_code_1424_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1873_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 1, v_a_1843_);
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_decl_1548_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_a_1843_);
v___x_1868_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1870_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1868_);
v___x_1870_ = v___x_1845_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v___x_1877_; 
lean_dec(v_a_1843_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v_code_1424_);
v___x_1877_ = v___x_1845_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_code_1424_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1424_, 2);
return v___x_1842_;
}
}
else
{
lean_object* v___x_1880_; 
lean_inc_ref(v_decl_1548_);
v___x_1880_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1548_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; uint8_t v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v___x_1882_ = 0;
v___x_1883_ = lean_box(0);
v___x_1884_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1885_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1885_, 0, v_a_1881_);
lean_ctor_set(v___x_1885_, 1, v___x_1883_);
lean_ctor_set(v___x_1885_, 2, v___x_1884_);
lean_inc_ref(v_decl_1548_);
v___x_1886_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1882_, v_decl_1548_, v___x_1885_, v___y_1759_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1888_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
lean_inc_ref(v_k_1549_);
v___x_1888_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1549_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1926_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1926_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1926_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
size_t v___x_1893_; size_t v___x_1894_; uint8_t v___x_1895_; 
v___x_1893_ = lean_ptr_addr(v_k_1549_);
v___x_1894_ = lean_ptr_addr(v_a_1889_);
v___x_1895_ = lean_usize_dec_eq(v___x_1893_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1905_; 
v_isSharedCheck_1905_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; lean_object* v_unused_1907_; 
v_unused_1906_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1906_);
v_unused_1907_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1907_);
v___x_1897_ = v_code_1424_;
v_isShared_1898_ = v_isSharedCheck_1905_;
goto v_resetjp_1896_;
}
else
{
lean_dec(v_code_1424_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1905_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v_a_1889_);
lean_ctor_set(v___x_1897_, 0, v_a_1887_);
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1887_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_a_1889_);
v___x_1900_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1902_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1900_);
v___x_1902_ = v___x_1891_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
size_t v___x_1908_; size_t v___x_1909_; uint8_t v___x_1910_; 
v___x_1908_ = lean_ptr_addr(v_decl_1548_);
v___x_1909_ = lean_ptr_addr(v_a_1887_);
v___x_1910_ = lean_usize_dec_eq(v___x_1908_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1920_; 
v_isSharedCheck_1920_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; lean_object* v_unused_1922_; 
v_unused_1921_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1921_);
v_unused_1922_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1922_);
v___x_1912_ = v_code_1424_;
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
else
{
lean_dec(v_code_1424_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v_a_1889_);
lean_ctor_set(v___x_1912_, 0, v_a_1887_);
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1887_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_a_1889_);
v___x_1915_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1917_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1915_);
v___x_1917_ = v___x_1891_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
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
lean_object* v___x_1924_; 
lean_dec(v_a_1889_);
lean_dec(v_a_1887_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_code_1424_);
v___x_1924_ = v___x_1891_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_code_1424_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
else
{
lean_dec(v_a_1887_);
lean_dec_ref_known(v_code_1424_, 2);
return v___x_1888_;
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref_known(v_code_1424_, 2);
v_a_1927_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1886_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1886_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec_ref_known(v_code_1424_, 2);
v_a_1935_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1880_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1880_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec_ref_known(v_code_1424_, 2);
v_a_1943_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1839_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1839_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref_known(v_value_1550_, 3);
lean_dec_ref_known(v_code_1424_, 2);
v_a_1951_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1762_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1762_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
v___jp_1959_:
{
uint8_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = 0;
v___x_1968_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1967_, v_sizeId_1960_, v___y_1964_);
lean_dec(v_sizeId_1960_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
if (lean_obj_tag(v_a_1969_) == 1)
{
lean_object* v_val_1970_; 
v_val_1970_ = lean_ctor_get(v_a_1969_, 0);
lean_inc(v_val_1970_);
lean_dec_ref_known(v_a_1969_, 1);
if (lean_obj_tag(v_val_1970_) == 0)
{
lean_object* v_value_1971_; 
v_value_1971_ = lean_ctor_get(v_val_1970_, 0);
lean_inc_ref(v_value_1971_);
lean_dec_ref_known(v_val_1970_, 1);
if (lean_obj_tag(v_value_1971_) == 0)
{
lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2080_; 
v_isSharedCheck_2080_ = !lean_is_exclusive(v_value_1550_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; lean_object* v_unused_2082_; lean_object* v_unused_2083_; 
v_unused_2081_ = lean_ctor_get(v_value_1550_, 2);
lean_dec(v_unused_2081_);
v_unused_2082_ = lean_ctor_get(v_value_1550_, 1);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_value_1550_, 0);
lean_dec(v_unused_2083_);
v___x_1973_ = v_value_1550_;
v_isShared_1974_ = v_isSharedCheck_2080_;
goto v_resetjp_1972_;
}
else
{
lean_dec(v_value_1550_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2080_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_val_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_val_1975_ = lean_ctor_get(v_value_1971_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v_value_1971_, 1);
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = lean_nat_dec_eq(v_val_1975_, v___x_1976_);
lean_dec(v_val_1975_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_del_object(v___x_1973_);
lean_inc_ref(v_k_1549_);
v___x_1978_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1549_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2015_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_2015_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2015_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
size_t v___x_1983_; size_t v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = lean_ptr_addr(v_k_1549_);
v___x_1984_ = lean_ptr_addr(v_a_1979_);
v___x_1985_ = lean_usize_dec_eq(v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1995_; 
lean_inc_ref(v_decl_1548_);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; lean_object* v_unused_1997_; 
v_unused_1996_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1997_);
v___x_1987_ = v_code_1424_;
v_isShared_1988_ = v_isSharedCheck_1995_;
goto v_resetjp_1986_;
}
else
{
lean_dec(v_code_1424_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1995_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v_a_1979_);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_decl_1548_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_a_1979_);
v___x_1990_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1990_);
v___x_1992_ = v___x_1981_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
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
else
{
size_t v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = lean_ptr_addr(v_decl_1548_);
v___x_1999_ = lean_usize_dec_eq(v___x_1998_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2009_; 
lean_inc_ref(v_decl_1548_);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; lean_object* v_unused_2011_; 
v_unused_2010_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_2011_);
v___x_2001_ = v_code_1424_;
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
else
{
lean_dec(v_code_1424_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v_a_1979_);
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_decl_1548_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_a_1979_);
v___x_2004_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_2004_);
v___x_2006_ = v___x_1981_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
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
lean_object* v___x_2013_; 
lean_dec(v_a_1979_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v_code_1424_);
v___x_2013_ = v___x_1981_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_code_1424_);
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
}
else
{
lean_dec_ref_known(v_code_1424_, 2);
return v___x_1978_;
}
}
else
{
lean_object* v___x_2016_; 
lean_inc_ref(v_decl_1548_);
v___x_2016_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1548_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = lean_box(0);
v___x_2019_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 2, v___x_2019_);
lean_ctor_set(v___x_1973_, 1, v___x_2018_);
lean_ctor_set(v___x_1973_, 0, v_a_2017_);
v___x_2021_ = v___x_1973_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2017_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; 
lean_inc_ref(v_decl_1548_);
v___x_2022_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1967_, v_decl_1548_, v___x_2021_, v___y_1964_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
lean_inc_ref(v_k_1549_);
v___x_2024_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1549_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2062_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2062_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2062_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
size_t v___x_2029_; size_t v___x_2030_; uint8_t v___x_2031_; 
v___x_2029_ = lean_ptr_addr(v_k_1549_);
v___x_2030_ = lean_ptr_addr(v_a_2025_);
v___x_2031_ = lean_usize_dec_eq(v___x_2029_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2041_; 
v_isSharedCheck_2041_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; lean_object* v_unused_2043_; 
v_unused_2042_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_2042_);
v_unused_2043_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_2043_);
v___x_2033_ = v_code_1424_;
v_isShared_2034_ = v_isSharedCheck_2041_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v_code_1424_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2041_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v_a_2025_);
lean_ctor_set(v___x_2033_, 0, v_a_2023_);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2023_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_a_2025_);
v___x_2036_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2038_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2036_);
v___x_2038_ = v___x_2027_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
size_t v___x_2044_; size_t v___x_2045_; uint8_t v___x_2046_; 
v___x_2044_ = lean_ptr_addr(v_decl_1548_);
v___x_2045_ = lean_ptr_addr(v_a_2023_);
v___x_2046_ = lean_usize_dec_eq(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2056_; 
v_isSharedCheck_2056_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; lean_object* v_unused_2058_; 
v_unused_2057_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_2057_);
v_unused_2058_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_2058_);
v___x_2048_ = v_code_1424_;
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
else
{
lean_dec(v_code_1424_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 1, v_a_2025_);
lean_ctor_set(v___x_2048_, 0, v_a_2023_);
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2023_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_a_2025_);
v___x_2051_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2053_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2051_);
v___x_2053_ = v___x_2027_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v___x_2060_; 
lean_dec(v_a_2025_);
lean_dec(v_a_2023_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v_code_1424_);
v___x_2060_ = v___x_2027_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_code_1424_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
else
{
lean_dec(v_a_2023_);
lean_dec_ref_known(v_code_1424_, 2);
return v___x_2024_;
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref_known(v_code_1424_, 2);
v_a_2063_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2022_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2022_);
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
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_del_object(v___x_1973_);
lean_dec_ref_known(v_code_1424_, 2);
v_a_2072_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2016_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2016_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_1971_);
v___y_1756_ = v___y_1961_;
v___y_1757_ = v___y_1962_;
v___y_1758_ = v___y_1963_;
v___y_1759_ = v___y_1964_;
v___y_1760_ = v___y_1965_;
v___y_1761_ = v___y_1966_;
goto v___jp_1755_;
}
}
else
{
lean_dec(v_val_1970_);
v___y_1756_ = v___y_1961_;
v___y_1757_ = v___y_1962_;
v___y_1758_ = v___y_1963_;
v___y_1759_ = v___y_1964_;
v___y_1760_ = v___y_1965_;
v___y_1761_ = v___y_1966_;
goto v___jp_1755_;
}
}
else
{
lean_dec(v_a_1969_);
v___y_1756_ = v___y_1961_;
v___y_1757_ = v___y_1962_;
v___y_1758_ = v___y_1963_;
v___y_1759_ = v___y_1964_;
v___y_1760_ = v___y_1965_;
v___y_1761_ = v___y_1966_;
goto v___jp_1755_;
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec_ref_known(v_value_1550_, 3);
lean_dec_ref_known(v_code_1424_, 2);
v_a_2084_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_1968_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_1968_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
else
{
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
goto v___jp_1551_;
}
}
else
{
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
goto v___jp_1551_;
}
}
else
{
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
goto v___jp_1551_;
}
}
else
{
v___y_1552_ = v_a_1425_;
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
goto v___jp_1551_;
}
v___jp_1551_:
{
lean_object* v___x_1558_; 
lean_inc_ref(v_k_1549_);
lean_inc_ref(v_decl_1548_);
v___x_1558_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1548_, v_k_1549_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
if (lean_obj_tag(v_a_1559_) == 1)
{
lean_object* v_val_1560_; lean_object* v_fst_1561_; lean_object* v_snd_1562_; lean_object* v___x_1563_; 
lean_dec(v_value_1550_);
v_val_1560_ = lean_ctor_get(v_a_1559_, 0);
lean_inc(v_val_1560_);
lean_dec_ref_known(v_a_1559_, 1);
v_fst_1561_ = lean_ctor_get(v_val_1560_, 0);
lean_inc_n(v_fst_1561_, 2);
v_snd_1562_ = lean_ctor_get(v_val_1560_, 1);
lean_inc(v_snd_1562_);
lean_dec(v_val_1560_);
v___x_1563_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1561_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = 0;
v___x_1566_ = lean_box(0);
v___x_1567_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1568_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1568_, 0, v_a_1564_);
lean_ctor_set(v___x_1568_, 1, v___x_1566_);
lean_ctor_set(v___x_1568_, 2, v___x_1567_);
v___x_1569_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1565_, v_fst_1561_, v___x_1568_, v___y_1555_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1562_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1609_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1609_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1609_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
size_t v___x_1576_; size_t v___x_1577_; uint8_t v___x_1578_; 
v___x_1576_ = lean_ptr_addr(v_k_1549_);
v___x_1577_ = lean_ptr_addr(v_a_1572_);
v___x_1578_ = lean_usize_dec_eq(v___x_1576_, v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1588_; 
v_isSharedCheck_1588_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; lean_object* v_unused_1590_; 
v_unused_1589_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1590_);
v___x_1580_ = v_code_1424_;
v_isShared_1581_ = v_isSharedCheck_1588_;
goto v_resetjp_1579_;
}
else
{
lean_dec(v_code_1424_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1588_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v_a_1572_);
lean_ctor_set(v___x_1580_, 0, v_a_1570_);
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1570_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_a_1572_);
v___x_1583_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1585_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1583_);
v___x_1585_ = v___x_1574_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
size_t v___x_1591_; size_t v___x_1592_; uint8_t v___x_1593_; 
v___x_1591_ = lean_ptr_addr(v_decl_1548_);
v___x_1592_ = lean_ptr_addr(v_a_1570_);
v___x_1593_ = lean_usize_dec_eq(v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1603_; 
v_isSharedCheck_1603_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; lean_object* v_unused_1605_; 
v_unused_1604_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1605_);
v___x_1595_ = v_code_1424_;
v_isShared_1596_ = v_isSharedCheck_1603_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v_code_1424_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1603_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 1, v_a_1572_);
lean_ctor_set(v___x_1595_, 0, v_a_1570_);
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1570_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_a_1572_);
v___x_1598_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1598_);
v___x_1600_ = v___x_1574_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v___x_1607_; 
lean_dec(v_a_1572_);
lean_dec(v_a_1570_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v_code_1424_);
v___x_1607_ = v___x_1574_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_code_1424_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
lean_dec(v_a_1570_);
lean_dec_ref_known(v_code_1424_, 2);
return v___x_1571_;
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_snd_1562_);
lean_dec_ref_known(v_code_1424_, 2);
v_a_1610_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1569_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1569_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v_snd_1562_);
lean_dec(v_fst_1561_);
lean_dec_ref_known(v_code_1424_, 2);
v_a_1618_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1563_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1563_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
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
uint8_t v___x_1626_; lean_object* v___x_1627_; 
lean_dec(v_a_1559_);
v___x_1626_ = 1;
v___x_1627_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1626_, v_value_1550_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; uint8_t v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v___x_1629_ = lean_unbox(v_a_1628_);
lean_dec(v_a_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
lean_inc_ref(v_k_1549_);
v___x_1630_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1549_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1667_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1667_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1667_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
size_t v___x_1635_; size_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1635_ = lean_ptr_addr(v_k_1549_);
v___x_1636_ = lean_ptr_addr(v_a_1631_);
v___x_1637_ = lean_usize_dec_eq(v___x_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1647_; 
lean_inc_ref(v_decl_1548_);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; lean_object* v_unused_1649_; 
v_unused_1648_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1648_);
v_unused_1649_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1649_);
v___x_1639_ = v_code_1424_;
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
else
{
lean_dec(v_code_1424_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1647_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 1, v_a_1631_);
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_decl_1548_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_a_1631_);
v___x_1642_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
lean_object* v___x_1644_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1642_);
v___x_1644_ = v___x_1633_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
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
else
{
size_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = lean_ptr_addr(v_decl_1548_);
v___x_1651_ = lean_usize_dec_eq(v___x_1650_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1661_; 
lean_inc_ref(v_decl_1548_);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; lean_object* v_unused_1663_; 
v_unused_1662_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1663_);
v___x_1653_ = v_code_1424_;
v_isShared_1654_ = v_isSharedCheck_1661_;
goto v_resetjp_1652_;
}
else
{
lean_dec(v_code_1424_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1661_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v_a_1631_);
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_decl_1548_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_a_1631_);
v___x_1656_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1658_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1656_);
v___x_1658_ = v___x_1633_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v___x_1665_; 
lean_dec(v_a_1631_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_code_1424_);
v___x_1665_ = v___x_1633_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_code_1424_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1424_, 2);
return v___x_1630_;
}
}
else
{
lean_object* v___x_1668_; 
lean_inc_ref(v_decl_1548_);
v___x_1668_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1548_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; uint8_t v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v___x_1670_ = 0;
v___x_1671_ = lean_box(0);
v___x_1672_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1673_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1673_, 0, v_a_1669_);
lean_ctor_set(v___x_1673_, 1, v___x_1671_);
lean_ctor_set(v___x_1673_, 2, v___x_1672_);
lean_inc_ref(v_decl_1548_);
v___x_1674_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1670_, v_decl_1548_, v___x_1673_, v___y_1555_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1676_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1674_, 1);
lean_inc_ref(v_k_1549_);
v___x_1676_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1549_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1714_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1679_ = v___x_1676_;
v_isShared_1680_ = v_isSharedCheck_1714_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1676_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1714_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
size_t v___x_1681_; size_t v___x_1682_; uint8_t v___x_1683_; 
v___x_1681_ = lean_ptr_addr(v_k_1549_);
v___x_1682_ = lean_ptr_addr(v_a_1677_);
v___x_1683_ = lean_usize_dec_eq(v___x_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1693_; 
v_isSharedCheck_1693_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; lean_object* v_unused_1695_; 
v_unused_1694_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1694_);
v_unused_1695_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1695_);
v___x_1685_ = v_code_1424_;
v_isShared_1686_ = v_isSharedCheck_1693_;
goto v_resetjp_1684_;
}
else
{
lean_dec(v_code_1424_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1693_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v_a_1677_);
lean_ctor_set(v___x_1685_, 0, v_a_1675_);
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1675_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_a_1677_);
v___x_1688_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v___x_1688_);
v___x_1690_ = v___x_1679_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
else
{
size_t v___x_1696_; size_t v___x_1697_; uint8_t v___x_1698_; 
v___x_1696_ = lean_ptr_addr(v_decl_1548_);
v___x_1697_ = lean_ptr_addr(v_a_1675_);
v___x_1698_ = lean_usize_dec_eq(v___x_1696_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1708_; 
v_isSharedCheck_1708_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; lean_object* v_unused_1710_; 
v_unused_1709_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1710_);
v___x_1700_ = v_code_1424_;
v_isShared_1701_ = v_isSharedCheck_1708_;
goto v_resetjp_1699_;
}
else
{
lean_dec(v_code_1424_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1708_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v_a_1677_);
lean_ctor_set(v___x_1700_, 0, v_a_1675_);
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1675_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1677_);
v___x_1703_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1705_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v___x_1703_);
v___x_1705_ = v___x_1679_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
else
{
lean_object* v___x_1712_; 
lean_dec(v_a_1677_);
lean_dec(v_a_1675_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 0, v_code_1424_);
v___x_1712_ = v___x_1679_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_code_1424_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
else
{
lean_dec(v_a_1675_);
lean_dec_ref_known(v_code_1424_, 2);
return v___x_1676_;
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref_known(v_code_1424_, 2);
v_a_1715_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1674_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1674_);
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
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref_known(v_code_1424_, 2);
v_a_1723_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1668_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1668_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref_known(v_code_1424_, 2);
v_a_1731_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1627_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1627_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_value_1550_);
lean_dec_ref_known(v_code_1424_, 2);
v_a_1739_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1558_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1558_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_2108_; lean_object* v_k_2109_; 
v_decl_2108_ = lean_ctor_get(v_code_1424_, 0);
v_k_2109_ = lean_ctor_get(v_code_1424_, 1);
lean_inc_ref(v_k_2109_);
lean_inc_ref(v_decl_2108_);
v_decl_1433_ = v_decl_2108_;
v_k_1434_ = v_k_2109_;
v___y_1435_ = v_a_1425_;
v___y_1436_ = v_a_1426_;
v___y_1437_ = v_a_1427_;
v___y_1438_ = v_a_1428_;
v___y_1439_ = v_a_1429_;
v___y_1440_ = v_a_1430_;
goto v___jp_1432_;
}
case 2:
{
lean_object* v_decl_2110_; lean_object* v_k_2111_; 
v_decl_2110_ = lean_ctor_get(v_code_1424_, 0);
v_k_2111_ = lean_ctor_get(v_code_1424_, 1);
lean_inc_ref(v_k_2111_);
lean_inc_ref(v_decl_2110_);
v_decl_1433_ = v_decl_2110_;
v_k_1434_ = v_k_2111_;
v___y_1435_ = v_a_1425_;
v___y_1436_ = v_a_1426_;
v___y_1437_ = v_a_1427_;
v___y_1438_ = v_a_1428_;
v___y_1439_ = v_a_1429_;
v___y_1440_ = v_a_1430_;
goto v___jp_1432_;
}
case 4:
{
lean_object* v_cases_2112_; lean_object* v_typeName_2113_; lean_object* v_resultType_2114_; lean_object* v_discr_2115_; lean_object* v_alts_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2155_; 
v_cases_2112_ = lean_ctor_get(v_code_1424_, 0);
lean_inc_ref(v_cases_2112_);
v_typeName_2113_ = lean_ctor_get(v_cases_2112_, 0);
v_resultType_2114_ = lean_ctor_get(v_cases_2112_, 1);
v_discr_2115_ = lean_ctor_get(v_cases_2112_, 2);
v_alts_2116_ = lean_ctor_get(v_cases_2112_, 3);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_cases_2112_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2118_ = v_cases_2112_;
v_isShared_2119_ = v_isSharedCheck_2155_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_alts_2116_);
lean_inc(v_discr_2115_);
lean_inc(v_resultType_2114_);
lean_inc(v_typeName_2113_);
lean_dec(v_cases_2112_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2155_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2116_);
v___x_2121_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v___x_2120_, v_alts_2116_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2146_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2146_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2146_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
size_t v___x_2126_; size_t v___x_2127_; uint8_t v___x_2128_; 
v___x_2126_ = lean_ptr_addr(v_alts_2116_);
lean_dec_ref(v_alts_2116_);
v___x_2127_ = lean_ptr_addr(v_a_2122_);
v___x_2128_ = lean_usize_dec_eq(v___x_2126_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2141_; 
v_isSharedCheck_2141_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_2141_ == 0)
{
lean_object* v_unused_2142_; 
v_unused_2142_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_2142_);
v___x_2130_ = v_code_1424_;
v_isShared_2131_ = v_isSharedCheck_2141_;
goto v_resetjp_2129_;
}
else
{
lean_dec(v_code_1424_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2141_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 3, v_a_2122_);
v___x_2133_ = v___x_2118_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_typeName_2113_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v_resultType_2114_);
lean_ctor_set(v_reuseFailAlloc_2140_, 2, v_discr_2115_);
lean_ctor_set(v_reuseFailAlloc_2140_, 3, v_a_2122_);
v___x_2133_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2133_);
v___x_2135_ = v___x_2130_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2137_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2135_);
v___x_2137_ = v___x_2124_;
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
}
else
{
lean_object* v___x_2144_; 
lean_dec(v_a_2122_);
lean_del_object(v___x_2118_);
lean_dec(v_discr_2115_);
lean_dec_ref(v_resultType_2114_);
lean_dec(v_typeName_2113_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_code_1424_);
v___x_2144_ = v___x_2124_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_code_1424_);
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
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_del_object(v___x_2118_);
lean_dec_ref(v_alts_2116_);
lean_dec(v_discr_2115_);
lean_dec_ref(v_resultType_2114_);
lean_dec(v_typeName_2113_);
lean_dec_ref_known(v_code_1424_, 1);
v_a_2147_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2121_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2121_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
default: 
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_code_1424_);
return v___x_2156_;
}
}
v___jp_1432_:
{
lean_object* v_params_1441_; lean_object* v_type_1442_; lean_object* v_value_1443_; lean_object* v___x_1444_; 
v_params_1441_ = lean_ctor_get(v_decl_1433_, 2);
lean_inc_ref(v_params_1441_);
v_type_1442_ = lean_ctor_get(v_decl_1433_, 3);
lean_inc_ref(v_type_1442_);
v_value_1443_ = lean_ctor_get(v_decl_1433_, 4);
lean_inc_ref(v_value_1443_);
v___x_1444_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_value_1443_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; uint8_t v___x_1446_; lean_object* v___x_1447_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1444_, 1);
v___x_1446_ = 0;
v___x_1447_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1446_, v_decl_1433_, v_type_1442_, v_params_1441_, v_a_1445_, v___y_1438_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1449_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1449_) == 0)
{
switch(lean_obj_tag(v_code_1424_))
{
case 1:
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1489_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1489_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1489_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v_decl_1454_; lean_object* v_k_1455_; size_t v___x_1456_; size_t v___x_1457_; uint8_t v___x_1458_; 
v_decl_1454_ = lean_ctor_get(v_code_1424_, 0);
v_k_1455_ = lean_ctor_get(v_code_1424_, 1);
v___x_1456_ = lean_ptr_addr(v_k_1455_);
v___x_1457_ = lean_ptr_addr(v_a_1450_);
v___x_1458_ = lean_usize_dec_eq(v___x_1456_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1468_; 
v_isSharedCheck_1468_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; lean_object* v_unused_1470_; 
v_unused_1469_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1470_);
v___x_1460_ = v_code_1424_;
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
else
{
lean_dec(v_code_1424_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 1, v_a_1450_);
lean_ctor_set(v___x_1460_, 0, v_a_1448_);
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1448_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_a_1450_);
v___x_1463_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1463_);
v___x_1465_ = v___x_1452_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
size_t v___x_1471_; size_t v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = lean_ptr_addr(v_decl_1454_);
v___x_1472_ = lean_ptr_addr(v_a_1448_);
v___x_1473_ = lean_usize_dec_eq(v___x_1471_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1483_; 
v_isSharedCheck_1483_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; lean_object* v_unused_1485_; 
v_unused_1484_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1485_);
v___x_1475_ = v_code_1424_;
v_isShared_1476_ = v_isSharedCheck_1483_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v_code_1424_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1483_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v_a_1450_);
lean_ctor_set(v___x_1475_, 0, v_a_1448_);
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1448_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_a_1450_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1478_);
v___x_1480_ = v___x_1452_;
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
else
{
lean_object* v___x_1487_; 
lean_dec(v_a_1450_);
lean_dec(v_a_1448_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v_code_1424_);
v___x_1487_ = v___x_1452_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_code_1424_);
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
}
case 2:
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1529_; 
v_a_1490_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1492_ = v___x_1449_;
v_isShared_1493_ = v_isSharedCheck_1529_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1449_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1529_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_decl_1494_; lean_object* v_k_1495_; size_t v___x_1496_; size_t v___x_1497_; uint8_t v___x_1498_; 
v_decl_1494_ = lean_ctor_get(v_code_1424_, 0);
v_k_1495_ = lean_ctor_get(v_code_1424_, 1);
v___x_1496_ = lean_ptr_addr(v_k_1495_);
v___x_1497_ = lean_ptr_addr(v_a_1490_);
v___x_1498_ = lean_usize_dec_eq(v___x_1496_, v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1508_; 
v_isSharedCheck_1508_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; lean_object* v_unused_1510_; 
v_unused_1509_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1510_);
v___x_1500_ = v_code_1424_;
v_isShared_1501_ = v_isSharedCheck_1508_;
goto v_resetjp_1499_;
}
else
{
lean_dec(v_code_1424_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1508_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v_a_1490_);
lean_ctor_set(v___x_1500_, 0, v_a_1448_);
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1448_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_a_1490_);
v___x_1503_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1503_);
v___x_1505_ = v___x_1492_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
size_t v___x_1511_; size_t v___x_1512_; uint8_t v___x_1513_; 
v___x_1511_ = lean_ptr_addr(v_decl_1494_);
v___x_1512_ = lean_ptr_addr(v_a_1448_);
v___x_1513_ = lean_usize_dec_eq(v___x_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1523_; 
v_isSharedCheck_1523_ = !lean_is_exclusive(v_code_1424_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; lean_object* v_unused_1525_; 
v_unused_1524_ = lean_ctor_get(v_code_1424_, 1);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_code_1424_, 0);
lean_dec(v_unused_1525_);
v___x_1515_ = v_code_1424_;
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
else
{
lean_dec(v_code_1424_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v_a_1490_);
lean_ctor_set(v___x_1515_, 0, v_a_1448_);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1448_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_a_1490_);
v___x_1518_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1518_);
v___x_1520_ = v___x_1492_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
else
{
lean_object* v___x_1527_; 
lean_dec(v_a_1490_);
lean_dec(v_a_1448_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v_code_1424_);
v___x_1527_ = v___x_1492_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_code_1424_);
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
default: 
{
lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_a_1448_);
lean_dec_ref(v_code_1424_);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v___x_1449_, 0);
lean_dec(v_unused_1539_);
v___x_1531_ = v___x_1449_;
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
else
{
lean_dec(v___x_1449_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1533_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3, &l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3);
v___x_1534_ = l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(v___x_1533_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1534_);
v___x_1536_ = v___x_1531_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
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
}
else
{
lean_dec(v_a_1448_);
lean_dec_ref(v_code_1424_);
return v___x_1449_;
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec_ref(v_k_1434_);
lean_dec_ref(v_code_1424_);
v_a_1540_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1447_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1447_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_dec_ref(v_type_1442_);
lean_dec_ref(v_params_1441_);
lean_dec_ref(v_k_1434_);
lean_dec_ref(v_decl_1433_);
lean_dec_ref(v_code_1424_);
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object* v_i_2157_, lean_object* v_as_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_array_get_size(v_as_2158_);
v___x_2167_ = lean_nat_dec_lt(v_i_2157_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
lean_dec(v_i_2157_);
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v_as_2158_);
return v___x_2168_;
}
else
{
lean_object* v_a_2169_; lean_object* v___y_2171_; 
v_a_2169_ = lean_array_fget_borrowed(v_as_2158_, v_i_2157_);
switch(lean_obj_tag(v_a_2169_))
{
case 0:
{
lean_object* v_code_2193_; 
v_code_2193_ = lean_ctor_get(v_a_2169_, 2);
lean_inc_ref(v_code_2193_);
v___y_2171_ = v_code_2193_;
goto v___jp_2170_;
}
case 1:
{
lean_object* v_code_2194_; 
v_code_2194_ = lean_ctor_get(v_a_2169_, 1);
lean_inc_ref(v_code_2194_);
v___y_2171_ = v_code_2194_;
goto v___jp_2170_;
}
default: 
{
lean_object* v_code_2195_; 
v_code_2195_ = lean_ctor_get(v_a_2169_, 0);
lean_inc_ref(v_code_2195_);
v___y_2171_ = v_code_2195_;
goto v___jp_2170_;
}
}
v___jp_2170_:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v___y_2171_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2174_; size_t v___x_2175_; size_t v___x_2176_; uint8_t v___x_2177_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
lean_inc(v_a_2169_);
v___x_2174_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2169_, v_a_2173_);
v___x_2175_ = lean_ptr_addr(v_a_2169_);
v___x_2176_ = lean_ptr_addr(v___x_2174_);
v___x_2177_ = lean_usize_dec_eq(v___x_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_add(v_i_2157_, v___x_2178_);
v___x_2180_ = lean_array_fset(v_as_2158_, v_i_2157_, v___x_2174_);
lean_dec(v_i_2157_);
v_i_2157_ = v___x_2179_;
v_as_2158_ = v___x_2180_;
goto _start;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec_ref(v___x_2174_);
v___x_2182_ = lean_unsigned_to_nat(1u);
v___x_2183_ = lean_nat_add(v_i_2157_, v___x_2182_);
lean_dec(v_i_2157_);
v_i_2157_ = v___x_2183_;
goto _start;
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v_as_2158_);
lean_dec(v_i_2157_);
v_a_2185_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2172_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2172_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object* v_i_2196_, lean_object* v_as_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_2196_, v_as_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object* v_code_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_code_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(lean_object* v_f_2215_, lean_object* v_v_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
if (lean_obj_tag(v_v_2216_) == 0)
{
lean_object* v_code_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2248_; 
v_code_2224_ = lean_ctor_get(v_v_2216_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v_v_2216_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2226_ = v_v_2216_;
v_isShared_2227_ = v_isSharedCheck_2248_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_code_2224_);
lean_dec(v_v_2216_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2248_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; 
lean_inc(v___y_2222_);
lean_inc_ref(v___y_2221_);
lean_inc(v___y_2220_);
lean_inc_ref(v___y_2219_);
lean_inc(v___y_2218_);
lean_inc_ref(v___y_2217_);
v___x_2228_ = lean_apply_8(v_f_2215_, v_code_2224_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, lean_box(0));
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2239_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2239_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2239_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 0, v_a_2229_);
v___x_2234_ = v___x_2226_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2236_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
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
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_del_object(v___x_2226_);
v_a_2240_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2228_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2228_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
}
else
{
lean_object* v___x_2249_; 
lean_dec_ref(v_f_2215_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_v_2216_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(lean_object* v_f_2250_, lean_object* v_v_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2250_, v_v_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(uint8_t v_pu_2260_, lean_object* v_f_2261_, lean_object* v_v_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2261_, v_v_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(lean_object* v_pu_2271_, lean_object* v_f_2272_, lean_object* v_v_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
uint8_t v_pu_boxed_2281_; lean_object* v_res_2282_; 
v_pu_boxed_2281_ = lean_unbox(v_pu_2271_);
v_res_2282_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_boxed_2281_, v_f_2272_, v_v_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object* v_decl_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_toSignature_2292_; lean_object* v_value_2293_; uint8_t v_recursive_2294_; lean_object* v_inlineAttr_x3f_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2320_; 
v_toSignature_2292_ = lean_ctor_get(v_decl_2284_, 0);
v_value_2293_ = lean_ctor_get(v_decl_2284_, 1);
v_recursive_2294_ = lean_ctor_get_uint8(v_decl_2284_, sizeof(void*)*3);
v_inlineAttr_x3f_2295_ = lean_ctor_get(v_decl_2284_, 2);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_decl_2284_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2297_ = v_decl_2284_;
v_isShared_2298_ = v_isSharedCheck_2320_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_inlineAttr_x3f_2295_);
lean_inc(v_value_2293_);
lean_inc(v_toSignature_2292_);
lean_dec(v_decl_2284_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2320_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0));
v___x_2300_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v___x_2299_, v_value_2293_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2311_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2311_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2311_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v_a_2301_);
v___x_2306_ = v___x_2297_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_toSignature_2292_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v_a_2301_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_inlineAttr_x3f_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2310_, sizeof(void*)*3, v_recursive_2294_);
v___x_2306_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2308_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2306_);
v___x_2308_ = v___x_2303_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
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
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_del_object(v___x_2297_);
lean_dec(v_inlineAttr_x3f_2295_);
lean_dec_ref(v_toSignature_2292_);
v_a_2312_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2300_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2300_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(lean_object* v_decl_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
return v_res_2329_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_2333_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0));
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
lean_ctor_set(v___x_2334_, 1, v___x_2332_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* v_decl_2335_, lean_object* v_sccDecls_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v_toSignature_2345_; lean_object* v_name_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2342_ = lean_unsigned_to_nat(0u);
v___x_2343_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1);
v___x_2344_ = lean_st_mk_ref(v___x_2343_);
v_toSignature_2345_ = lean_ctor_get(v_decl_2335_, 0);
v_name_2346_ = lean_ctor_get(v_toSignature_2345_, 0);
lean_inc(v_name_2346_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v_name_2346_);
lean_ctor_set(v___x_2347_, 1, v_sccDecls_2336_);
v___x_2348_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2335_, v___x_2347_, v___x_2344_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
lean_dec_ref_known(v___x_2347_, 2);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2374_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2374_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2374_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v_decls_2354_; lean_object* v_decl_2356_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2353_ = lean_st_ref_get(v___x_2344_);
lean_dec(v___x_2344_);
v_decls_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc_ref(v_decls_2354_);
lean_dec(v___x_2353_);
v___x_2361_ = lean_array_get_size(v_decls_2354_);
v___x_2362_ = lean_nat_dec_eq(v___x_2361_, v___x_2342_);
if (v___x_2362_ == 0)
{
uint8_t v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = 0;
v___x_2364_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2363_, v_a_2349_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v_decl_2356_ = v_a_2365_;
goto v___jp_2355_;
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec_ref(v_decls_2354_);
lean_del_object(v___x_2351_);
v_a_2366_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2364_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2364_);
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
else
{
v_decl_2356_ = v_a_2349_;
goto v___jp_2355_;
}
v___jp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = lean_array_push(v_decls_2354_, v_decl_2356_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2357_);
v___x_2359_ = v___x_2351_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
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
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v___x_2344_);
v_a_2375_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2348_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2348_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(lean_object* v_decl_2383_, lean_object* v_sccDecls_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v_decl_2383_, v_sccDecls_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(lean_object* v_decls_2391_, lean_object* v_as_2392_, size_t v_i_2393_, size_t v_stop_2394_, lean_object* v_b_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_a_2402_; uint8_t v___x_2406_; 
v___x_2406_ = lean_usize_dec_eq(v_i_2393_, v_stop_2394_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_array_uget_borrowed(v_as_2392_, v_i_2393_);
lean_inc_ref(v_decls_2391_);
lean_inc(v___x_2407_);
v___x_2408_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v___x_2407_, v_decls_2391_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2410_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = l_Array_append___redArg(v_b_2395_, v_a_2409_);
lean_dec(v_a_2409_);
v_a_2402_ = v___x_2410_;
goto v___jp_2401_;
}
else
{
lean_dec_ref(v_b_2395_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2411_; 
v_a_2411_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2408_, 1);
v_a_2402_ = v_a_2411_;
goto v___jp_2401_;
}
else
{
lean_dec_ref(v_decls_2391_);
return v___x_2408_;
}
}
}
else
{
lean_object* v___x_2412_; 
lean_dec_ref(v_decls_2391_);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v_b_2395_);
return v___x_2412_;
}
v___jp_2401_:
{
size_t v___x_2403_; size_t v___x_2404_; 
v___x_2403_ = ((size_t)1ULL);
v___x_2404_ = lean_usize_add(v_i_2393_, v___x_2403_);
v_i_2393_ = v___x_2404_;
v_b_2395_ = v_a_2402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object* v_decls_2413_, lean_object* v_as_2414_, lean_object* v_i_2415_, lean_object* v_stop_2416_, lean_object* v_b_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
size_t v_i_boxed_2423_; size_t v_stop_boxed_2424_; lean_object* v_res_2425_; 
v_i_boxed_2423_ = lean_unbox_usize(v_i_2415_);
lean_dec(v_i_2415_);
v_stop_boxed_2424_ = lean_unbox_usize(v_stop_2416_);
lean_dec(v_stop_2416_);
v_res_2425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2413_, v_as_2414_, v_i_boxed_2423_, v_stop_boxed_2424_, v_b_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v_as_2414_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* v___x_2426_, lean_object* v_decls_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_2428_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2458_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2436_ = v___x_2433_;
v_isShared_2437_ = v_isSharedCheck_2458_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2458_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
uint8_t v_extractClosed_2438_; 
v_extractClosed_2438_ = lean_ctor_get_uint8(v_a_2434_, sizeof(void*)*4 + 1);
lean_dec(v_a_2434_);
if (v_extractClosed_2438_ == 0)
{
lean_object* v___x_2440_; 
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v_decls_2427_);
v___x_2440_ = v___x_2436_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_decls_2427_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
v___x_2442_ = lean_mk_empty_array_with_capacity(v___x_2426_);
v___x_2443_ = lean_array_get_size(v_decls_2427_);
v___x_2444_ = lean_nat_dec_lt(v___x_2426_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2446_; 
lean_dec_ref(v_decls_2427_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2442_);
v___x_2446_ = v___x_2436_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2442_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
else
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_nat_dec_le(v___x_2443_, v___x_2443_);
if (v___x_2448_ == 0)
{
if (v___x_2444_ == 0)
{
lean_object* v___x_2450_; 
lean_dec_ref(v_decls_2427_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2442_);
v___x_2450_ = v___x_2436_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2442_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
else
{
size_t v___x_2452_; size_t v___x_2453_; lean_object* v___x_2454_; 
lean_del_object(v___x_2436_);
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = lean_usize_of_nat(v___x_2443_);
lean_inc_ref(v_decls_2427_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2427_, v_decls_2427_, v___x_2452_, v___x_2453_, v___x_2442_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec_ref(v_decls_2427_);
return v___x_2454_;
}
}
else
{
size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
lean_del_object(v___x_2436_);
v___x_2455_ = ((size_t)0ULL);
v___x_2456_ = lean_usize_of_nat(v___x_2443_);
lean_inc_ref(v_decls_2427_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2427_, v_decls_2427_, v___x_2455_, v___x_2456_, v___x_2442_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec_ref(v_decls_2427_);
return v___x_2457_;
}
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref(v_decls_2427_);
v_a_2459_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2433_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2433_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object* v___x_2467_, lean_object* v_decls_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(v___x_2467_, v_decls_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___x_2467_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2557_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2558_ = 1;
v___x_2559_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2560_ = l_Lean_registerTraceClass(v___x_2557_, v___x_2558_, v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(lean_object* v_a_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
return v_res_2562_;
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
