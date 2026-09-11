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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t v_____do__lift_15158__boxed_193_; lean_object* v_res_194_; 
v_____do__lift_15158__boxed_193_ = lean_unbox(v_____do__lift_185_);
v_res_194_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v_____do__lift_15158__boxed_193_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
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
uint8_t v_isRoot_boxed_395_; uint8_t v___x_15465__boxed_396_; size_t v_i_boxed_397_; size_t v_stop_boxed_398_; uint8_t v_res_399_; lean_object* v_r_400_; 
v_isRoot_boxed_395_ = lean_unbox(v_isRoot_390_);
v___x_15465__boxed_396_ = lean_unbox(v___x_391_);
v_i_boxed_397_ = lean_unbox_usize(v_i_393_);
lean_dec(v_i_393_);
v_stop_boxed_398_ = lean_unbox_usize(v_stop_394_);
lean_dec(v_stop_394_);
v_res_399_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_boxed_395_, v___x_15465__boxed_396_, v_as_392_, v_i_boxed_397_, v_stop_boxed_398_);
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
uint8_t v___x_15518__boxed_789_; size_t v_i_boxed_790_; size_t v_stop_boxed_791_; lean_object* v_res_792_; 
v___x_15518__boxed_789_ = lean_unbox(v___x_778_);
v_i_boxed_790_ = lean_unbox_usize(v_i_780_);
lean_dec(v_i_780_);
v_stop_boxed_791_ = lean_unbox_usize(v_stop_781_);
lean_dec(v_stop_781_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___x_15518__boxed_789_, v_as_779_, v_i_boxed_790_, v_stop_boxed_791_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
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
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
lean_del_object(v___x_918_);
v___x_925_ = lean_unsigned_to_nat(2u);
v___x_926_ = lean_array_fget_borrowed(v_args_904_, v___x_925_);
lean_inc(v___x_926_);
v___x_927_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_926_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_1024_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_1024_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_1024_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
uint8_t v___x_932_; 
v___x_932_ = lean_unbox(v_a_928_);
lean_dec(v_a_928_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_935_; 
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
v___x_933_ = lean_box(0);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_933_);
v___x_935_ = v___x_930_;
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
else
{
lean_object* v_n_937_; uint8_t v___x_938_; 
v_n_937_ = lean_nat_sub(v_size_873_, v___x_914_);
lean_dec(v_size_873_);
v___x_938_ = lean_nat_dec_eq(v_n_937_, v_zero_895_);
if (v___x_938_ == 0)
{
lean_inc(v_fvarId_903_);
lean_dec_ref(v_decl_870_);
if (lean_obj_tag(v_k_871_) == 0)
{
lean_object* v_decl_939_; lean_object* v_k_940_; lean_object* v___x_941_; 
lean_del_object(v___x_930_);
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
v_size_873_ = v_n_937_;
goto _start;
}
else
{
lean_object* v___x_943_; lean_object* v___x_945_; 
lean_dec(v_n_937_);
lean_dec(v_fvarId_903_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
v___x_943_ = lean_box(0);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_943_);
v___x_945_ = v___x_930_;
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
lean_dec(v_n_937_);
lean_del_object(v___x_930_);
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
lean_dec(v_size_873_);
lean_dec(v_illegalSet_872_);
lean_dec_ref(v_k_871_);
lean_dec_ref(v_decl_870_);
v_a_1025_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_927_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_927_);
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
lean_object* v_fvarId_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; 
v_fvarId_1083_ = lean_ctor_get(v___x_1082_, 0);
v___x_1084_ = 0;
v___x_1085_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_1084_, v_fvarId_1083_, v_a_1054_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1141_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1141_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1141_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
if (lean_obj_tag(v_a_1086_) == 1)
{
lean_object* v_val_1090_; lean_object* v_value_1091_; 
lean_del_object(v___x_1088_);
v_val_1090_ = lean_ctor_get(v_a_1086_, 0);
lean_inc(v_val_1090_);
lean_dec_ref_known(v_a_1086_, 1);
v_value_1091_ = lean_ctor_get(v_val_1090_, 3);
lean_inc(v_value_1091_);
if (lean_obj_tag(v_value_1091_) == 3)
{
lean_object* v_declName_1092_; 
v_declName_1092_ = lean_ctor_get(v_value_1091_, 0);
lean_inc(v_declName_1092_);
if (lean_obj_tag(v_declName_1092_) == 1)
{
lean_object* v_pre_1093_; 
v_pre_1093_ = lean_ctor_get(v_declName_1092_, 0);
lean_inc(v_pre_1093_);
if (lean_obj_tag(v_pre_1093_) == 1)
{
lean_object* v_pre_1094_; 
v_pre_1094_ = lean_ctor_get(v_pre_1093_, 0);
if (lean_obj_tag(v_pre_1094_) == 0)
{
lean_object* v_fvarId_1095_; lean_object* v_args_1096_; lean_object* v_str_1097_; lean_object* v_str_1098_; uint8_t v___x_1099_; 
v_fvarId_1095_ = lean_ctor_get(v_val_1090_, 0);
lean_inc(v_fvarId_1095_);
lean_dec(v_val_1090_);
v_args_1096_ = lean_ctor_get(v_value_1091_, 2);
lean_inc_ref(v_args_1096_);
lean_dec_ref_known(v_value_1091_, 3);
v_str_1097_ = lean_ctor_get(v_declName_1092_, 1);
lean_inc_ref(v_str_1097_);
lean_dec_ref_known(v_declName_1092_, 2);
v_str_1098_ = lean_ctor_get(v_pre_1093_, 1);
lean_inc_ref(v_str_1098_);
lean_dec_ref_known(v_pre_1093_, 2);
v___x_1099_ = lean_string_dec_eq(v_str_1098_, v___x_1074_);
lean_dec_ref(v_str_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v_str_1097_);
lean_dec_ref(v_args_1096_);
lean_dec(v_fvarId_1095_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1100_; lean_object* v_sizeFVar_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1100_ = lean_box(1);
v___x_1123_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1124_ = lean_string_dec_eq(v_str_1097_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1126_ = lean_string_dec_eq(v_str_1097_, v___x_1125_);
lean_dec_ref(v_str_1097_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v_args_1096_);
lean_dec(v_fvarId_1095_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_array_get_size(v_args_1096_);
v___x_1128_ = lean_unsigned_to_nat(2u);
v___x_1129_ = lean_nat_dec_eq(v___x_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_dec_ref(v_args_1096_);
lean_dec(v_fvarId_1095_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_array_fget(v_args_1096_, v___x_1081_);
lean_dec_ref(v_args_1096_);
if (lean_obj_tag(v___x_1130_) == 1)
{
lean_object* v_fvarId_1131_; 
v_fvarId_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_fvarId_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v_sizeFVar_1102_ = v_fvarId_1131_;
v___y_1103_ = v_a_1051_;
v___y_1104_ = v_a_1052_;
v___y_1105_ = v_a_1053_;
v___y_1106_ = v_a_1054_;
v___y_1107_ = v_a_1055_;
v___y_1108_ = v_a_1056_;
goto v___jp_1101_;
}
else
{
lean_dec(v___x_1130_);
lean_dec(v_fvarId_1095_);
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
lean_dec_ref(v_str_1097_);
v___x_1132_ = lean_array_get_size(v_args_1096_);
v___x_1133_ = lean_unsigned_to_nat(2u);
v___x_1134_ = lean_nat_dec_eq(v___x_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_dec_ref(v_args_1096_);
lean_dec(v_fvarId_1095_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_array_fget(v_args_1096_, v___x_1081_);
lean_dec_ref(v_args_1096_);
if (lean_obj_tag(v___x_1135_) == 1)
{
lean_object* v_fvarId_1136_; 
v_fvarId_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_fvarId_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v_sizeFVar_1102_ = v_fvarId_1136_;
v___y_1103_ = v_a_1051_;
v___y_1104_ = v_a_1052_;
v___y_1105_ = v_a_1053_;
v___y_1106_ = v_a_1054_;
v___y_1107_ = v_a_1055_;
v___y_1108_ = v_a_1056_;
goto v___jp_1101_;
}
else
{
lean_dec(v___x_1135_);
lean_dec(v_fvarId_1095_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
}
}
v___jp_1101_:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1084_, v_sizeFVar_1102_, v___y_1106_);
lean_dec(v_sizeFVar_1102_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
if (lean_obj_tag(v_a_1110_) == 1)
{
lean_object* v_val_1111_; 
v_val_1111_ = lean_ctor_get(v_a_1110_, 0);
lean_inc(v_val_1111_);
lean_dec_ref_known(v_a_1110_, 1);
if (lean_obj_tag(v_val_1111_) == 0)
{
lean_object* v_value_1112_; 
v_value_1112_ = lean_ctor_get(v_val_1111_, 0);
lean_inc_ref(v_value_1112_);
lean_dec_ref_known(v_val_1111_, 1);
if (lean_obj_tag(v_value_1112_) == 0)
{
lean_object* v_val_1113_; lean_object* v___x_1114_; 
v_val_1113_ = lean_ctor_get(v_value_1112_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v_value_1112_, 1);
v___x_1114_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_fvarId_1095_, v_decl_1049_, v_k_1050_, v___x_1100_, v_val_1113_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
return v___x_1114_;
}
else
{
lean_dec_ref(v_value_1112_);
lean_dec(v_fvarId_1095_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1058_;
}
}
else
{
lean_dec(v_val_1111_);
lean_dec(v_fvarId_1095_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1058_;
}
}
else
{
lean_dec(v_a_1110_);
lean_dec(v_fvarId_1095_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1058_;
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v_fvarId_1095_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
v_a_1115_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1109_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1109_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1093_, 2);
lean_dec_ref_known(v_declName_1092_, 2);
lean_dec_ref_known(v_value_1091_, 3);
lean_dec(v_val_1090_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
}
else
{
lean_dec_ref_known(v_declName_1092_, 2);
lean_dec(v_pre_1093_);
lean_dec_ref_known(v_value_1091_, 3);
lean_dec(v_val_1090_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
}
else
{
lean_dec_ref_known(v_value_1091_, 3);
lean_dec(v_declName_1092_);
lean_dec(v_val_1090_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
}
else
{
lean_dec(v_value_1091_);
lean_dec(v_val_1090_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
goto v___jp_1061_;
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
lean_dec(v_a_1086_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_decl_1049_);
v___x_1137_ = lean_box(0);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1137_);
v___x_1139_ = v___x_1088_;
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
v_a_1142_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1085_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1085_);
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
v___x_1160_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 5, v___x_1179_);
lean_ctor_set(v___x_1177_, 0, v_env_1165_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
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
lean_ctor_set(v_reuseFailAlloc_1185_, 5, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1185_, 6, v_messages_1173_);
lean_ctor_set(v_reuseFailAlloc_1185_, 7, v_infoState_1174_);
lean_ctor_set(v_reuseFailAlloc_1185_, 8, v_snapshotTasks_1175_);
v___x_1181_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_st_ref_put(v___y_1166_, v___x_1181_);
v___x_1183_ = lean_box(0);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
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
uint8_t v___x_1223_; lean_object* v_v_1224_; lean_object* v___x_1225_; 
v___x_1223_ = 0;
v_v_1224_ = lean_array_uget_borrowed(v_bs_1213_, v_i_1212_);
lean_inc(v_v_1224_);
v___x_1225_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_1223_, v_v_1224_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1227_; lean_object* v_bs_x27_1228_; size_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1227_ = lean_unsigned_to_nat(0u);
v_bs_x27_1228_ = lean_array_uset(v_bs_1213_, v_i_1212_, v___x_1227_);
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_add(v_i_1212_, v___x_1229_);
v___x_1231_ = lean_array_uset(v_bs_x27_1228_, v_i_1212_, v_a_1226_);
v_i_1212_ = v___x_1230_;
v_bs_1213_ = v___x_1231_;
goto _start;
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v_bs_1213_);
v_a_1233_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1225_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1225_);
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
size_t v_sz_boxed_1251_; size_t v_i_boxed_1252_; uint8_t v___y_8180__boxed_1253_; lean_object* v_res_1254_; 
v_sz_boxed_1251_ = lean_unbox_usize(v_sz_1241_);
lean_dec(v_sz_1241_);
v_i_boxed_1252_ = lean_unbox_usize(v_i_1242_);
lean_dec(v_i_1242_);
v___y_8180__boxed_1253_ = lean_unbox(v___y_1244_);
v_res_1254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_boxed_1251_, v_i_boxed_1252_, v_bs_1243_, v___y_8180__boxed_1253_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
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
uint8_t v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = 0;
v___x_1264_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(lean_object* v_decl_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_type_1283_; lean_object* v_value_1284_; lean_object* v___x_1285_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0));
v___x_1282_ = lean_st_mk_ref(v___x_1281_);
v_type_1283_ = lean_ctor_get(v_decl_1273_, 2);
lean_inc_ref(v_type_1283_);
v_value_1284_ = lean_ctor_get(v_decl_1273_, 3);
lean_inc(v_value_1284_);
v___x_1285_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_1284_, v___x_1282_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; lean_object* v_a_1296_; size_t v_sz_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
lean_dec_ref_known(v___x_1285_, 1);
v___x_1286_ = lean_st_ref_get(v___x_1282_);
lean_dec(v___x_1282_);
v___x_1287_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_1288_ = lean_st_mk_ref(v___x_1287_);
v___x_1289_ = 0;
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_decl_1273_);
v___x_1291_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3);
v___x_1292_ = l_Array_reverse___redArg(v___x_1286_);
v___x_1293_ = lean_array_push(v___x_1292_, v___x_1290_);
v___x_1294_ = 0;
v_sz_1378_ = lean_array_size(v___x_1293_);
v___x_1379_ = ((size_t)0ULL);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_1378_, v___x_1379_, v___x_1293_, v___x_1294_, v___x_1288_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1382_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v___x_1382_ = lean_st_ref_get(v___x_1288_);
lean_dec(v___x_1288_);
lean_dec(v___x_1382_);
v_a_1296_ = v_a_1381_;
goto v___jp_1295_;
}
else
{
lean_dec(v___x_1288_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1383_; 
v_a_1383_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1380_, 1);
v_a_1296_ = v_a_1383_;
goto v___jp_1295_;
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec_ref(v_type_1283_);
v_a_1384_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1380_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1380_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
v___jp_1295_:
{
lean_object* v___x_1297_; lean_object* v_env_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1297_ = lean_st_ref_get(v_a_1279_);
v_env_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc_ref_n(v_env_1298_, 2);
lean_dec(v___x_1297_);
v___x_1299_ = lean_array_get_size(v_a_1296_);
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_nat_sub(v___x_1299_, v___x_1300_);
v___x_1302_ = lean_array_get_borrowed(v___x_1291_, v_a_1296_, v___x_1301_);
lean_dec(v___x_1301_);
v___x_1303_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1302_);
v___x_1304_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
v___x_1305_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1289_, v_a_1296_, v___x_1304_);
lean_dec_ref(v_a_1296_);
v___x_1306_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4));
lean_inc_ref(v___x_1305_);
v___x_1307_ = l_Lean_Compiler_LCNF_Code_toExpr(v___x_1289_, v___x_1305_, v___x_1306_);
v___x_1308_ = l_Lean_getClosedTermName_x3f(v_env_1298_, v___x_1307_);
if (lean_obj_tag(v___x_1308_) == 1)
{
lean_object* v_val_1309_; lean_object* v___x_1310_; 
lean_dec_ref(v___x_1307_);
lean_dec_ref(v_env_1298_);
lean_dec_ref(v_type_1283_);
v_val_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_val_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v___x_1310_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1289_, v___x_1305_, v_a_1277_);
lean_dec_ref(v___x_1305_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1310_, 0);
lean_dec(v_unused_1318_);
v___x_1312_ = v___x_1310_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v___x_1310_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v_val_1309_);
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_val_1309_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_val_1309_);
v_a_1319_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1310_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1310_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v___x_1327_; lean_object* v_baseName_1328_; lean_object* v_decls_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1376_; 
lean_dec(v___x_1308_);
v___x_1327_ = lean_st_ref_get(v_a_1275_);
v_baseName_1328_ = lean_ctor_get(v_a_1274_, 0);
v_decls_1329_ = lean_ctor_get(v___x_1327_, 0);
lean_inc_ref(v_decls_1329_);
lean_dec(v___x_1327_);
v___x_1330_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6));
v___x_1331_ = lean_array_get_size(v_decls_1329_);
lean_dec_ref(v_decls_1329_);
v___x_1332_ = lean_name_append_index_after(v___x_1330_, v___x_1331_);
lean_inc(v_baseName_1328_);
v___x_1333_ = l_Lean_Name_append(v_baseName_1328_, v___x_1332_);
lean_inc(v___x_1333_);
v___x_1334_ = l_Lean_cacheClosedTermName(v_env_1298_, v___x_1307_, v___x_1333_);
v___x_1335_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v___x_1334_, v_a_1279_);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1335_, 0);
lean_dec(v_unused_1377_);
v___x_1337_ = v___x_1335_;
v_isShared_1338_ = v_isSharedCheck_1376_;
goto v_resetjp_1336_;
}
else
{
lean_dec(v___x_1335_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1376_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = 1;
lean_inc(v___x_1333_);
v___x_1341_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1341_, 0, v___x_1333_);
lean_ctor_set(v___x_1341_, 1, v___x_1339_);
lean_ctor_set(v___x_1341_, 2, v_type_1283_);
lean_ctor_set(v___x_1341_, 3, v___x_1306_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*4, v___x_1340_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1305_);
v___x_1343_ = v___x_1337_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1305_);
v___x_1343_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7));
v___x_1345_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1345_, 0, v___x_1341_);
lean_ctor_set(v___x_1345_, 1, v___x_1343_);
lean_ctor_set(v___x_1345_, 2, v___x_1344_);
lean_ctor_set_uint8(v___x_1345_, sizeof(void*)*3, v___x_1294_);
lean_inc_ref(v___x_1345_);
v___x_1346_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1345_, v_a_1279_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1365_; 
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v___x_1346_, 0);
lean_dec(v_unused_1366_);
v___x_1348_ = v___x_1346_;
v_isShared_1349_ = v_isSharedCheck_1365_;
goto v_resetjp_1347_;
}
else
{
lean_dec(v___x_1346_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1365_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v_decls_1351_; lean_object* v_fvarDecisionCache_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1364_; 
v___x_1350_ = lean_st_ref_take(v_a_1275_);
v_decls_1351_ = lean_ctor_get(v___x_1350_, 0);
v_fvarDecisionCache_1352_ = lean_ctor_get(v___x_1350_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1354_ = v___x_1350_;
v_isShared_1355_ = v_isSharedCheck_1364_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_fvarDecisionCache_1352_);
lean_inc(v_decls_1351_);
lean_dec(v___x_1350_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1364_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_array_push(v_decls_1351_, v___x_1345_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_fvarDecisionCache_1352_);
v___x_1358_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = lean_st_ref_put(v_a_1275_, v___x_1358_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1333_);
v___x_1361_ = v___x_1348_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1333_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec_ref_known(v___x_1345_, 3);
lean_dec(v___x_1333_);
v_a_1367_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1346_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1346_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
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
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v_type_1283_);
lean_dec(v___x_1282_);
lean_dec_ref(v_decl_1273_);
v_a_1392_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1285_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1285_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___boxed(lean_object* v_decl_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
return v_res_1408_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0(void){
_start:
{
uint8_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = 0;
v___x_1410_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(lean_object* v_msg_1411_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0);
v___x_1413_ = lean_panic_fn_borrowed(v___x_1412_, v_msg_1411_);
return v___x_1413_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3(void){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1417_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2));
v___x_1418_ = lean_unsigned_to_nat(9u);
v___x_1419_ = lean_unsigned_to_nat(650u);
v___x_1420_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1));
v___x_1421_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0));
v___x_1422_ = l_mkPanicMessageWithDecl(v___x_1421_, v___x_1420_, v___x_1419_, v___x_1418_, v___x_1417_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* v_code_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_decl_1434_; lean_object* v_k_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; 
switch(lean_obj_tag(v_code_1425_))
{
case 0:
{
lean_object* v_decl_1549_; lean_object* v_k_1550_; lean_object* v_value_1551_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; 
v_decl_1549_ = lean_ctor_get(v_code_1425_, 0);
v_k_1550_ = lean_ctor_get(v_code_1425_, 1);
v_value_1551_ = lean_ctor_get(v_decl_1549_, 3);
lean_inc(v_value_1551_);
if (lean_obj_tag(v_value_1551_) == 3)
{
lean_object* v_declName_1748_; 
v_declName_1748_ = lean_ctor_get(v_value_1551_, 0);
if (lean_obj_tag(v_declName_1748_) == 1)
{
lean_object* v_pre_1749_; 
v_pre_1749_ = lean_ctor_get(v_declName_1748_, 0);
if (lean_obj_tag(v_pre_1749_) == 1)
{
lean_object* v_pre_1750_; 
v_pre_1750_ = lean_ctor_get(v_pre_1749_, 0);
if (lean_obj_tag(v_pre_1750_) == 0)
{
lean_object* v_args_1751_; lean_object* v_str_1752_; lean_object* v_str_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v_sizeId_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; 
v_args_1751_ = lean_ctor_get(v_value_1551_, 2);
v_str_1752_ = lean_ctor_get(v_declName_1748_, 1);
v_str_1753_ = lean_ctor_get(v_pre_1749_, 1);
v___x_1754_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1755_ = lean_string_dec_eq(v_str_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
v___y_1558_ = v_a_1431_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_2094_ = lean_string_dec_eq(v_str_1752_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_2096_ = lean_string_dec_eq(v_str_1752_, v___x_2095_);
if (v___x_2096_ == 0)
{
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
v___y_1558_ = v_a_1431_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2097_ = lean_array_get_size(v_args_1751_);
v___x_2098_ = lean_unsigned_to_nat(2u);
v___x_2099_ = lean_nat_dec_eq(v___x_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
v___y_1558_ = v_a_1431_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_unsigned_to_nat(1u);
v___x_2101_ = lean_array_fget_borrowed(v_args_1751_, v___x_2100_);
if (lean_obj_tag(v___x_2101_) == 1)
{
lean_object* v_fvarId_2102_; 
v_fvarId_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_fvarId_2102_);
v_sizeId_1961_ = v_fvarId_2102_;
v___y_1962_ = v_a_1426_;
v___y_1963_ = v_a_1427_;
v___y_1964_ = v_a_1428_;
v___y_1965_ = v_a_1429_;
v___y_1966_ = v_a_1430_;
v___y_1967_ = v_a_1431_;
goto v___jp_1960_;
}
else
{
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
v___y_1558_ = v_a_1431_;
goto v___jp_1552_;
}
}
}
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2103_ = lean_array_get_size(v_args_1751_);
v___x_2104_ = lean_unsigned_to_nat(2u);
v___x_2105_ = lean_nat_dec_eq(v___x_2103_, v___x_2104_);
if (v___x_2105_ == 0)
{
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
v___y_1558_ = v_a_1431_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_unsigned_to_nat(1u);
v___x_2107_ = lean_array_fget_borrowed(v_args_1751_, v___x_2106_);
if (lean_obj_tag(v___x_2107_) == 1)
{
lean_object* v_fvarId_2108_; 
v_fvarId_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_fvarId_2108_);
v_sizeId_1961_ = v_fvarId_2108_;
v___y_1962_ = v_a_1426_;
v___y_1963_ = v_a_1427_;
v___y_1964_ = v_a_1428_;
v___y_1965_ = v_a_1429_;
v___y_1966_ = v_a_1430_;
v___y_1967_ = v_a_1431_;
goto v___jp_1960_;
}
else
{
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
v___y_1558_ = v_a_1431_;
goto v___jp_1552_;
}
}
}
}
v___jp_1756_:
{
lean_object* v___x_1763_; 
lean_inc_ref(v_k_1550_);
lean_inc_ref(v_decl_1549_);
v___x_1763_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1549_, v_k_1550_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
if (lean_obj_tag(v_a_1764_) == 1)
{
lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1836_; 
v_isSharedCheck_1836_ = !lean_is_exclusive(v_value_1551_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; lean_object* v_unused_1838_; lean_object* v_unused_1839_; 
v_unused_1837_ = lean_ctor_get(v_value_1551_, 2);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_value_1551_, 1);
lean_dec(v_unused_1838_);
v_unused_1839_ = lean_ctor_get(v_value_1551_, 0);
lean_dec(v_unused_1839_);
v___x_1766_ = v_value_1551_;
v_isShared_1767_ = v_isSharedCheck_1836_;
goto v_resetjp_1765_;
}
else
{
lean_dec(v_value_1551_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1836_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v_val_1768_; lean_object* v_fst_1769_; lean_object* v_snd_1770_; lean_object* v___x_1771_; 
v_val_1768_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_val_1768_);
lean_dec_ref_known(v_a_1764_, 1);
v_fst_1769_ = lean_ctor_get(v_val_1768_, 0);
lean_inc_n(v_fst_1769_, 2);
v_snd_1770_ = lean_ctor_get(v_val_1768_, 1);
lean_inc(v_snd_1770_);
lean_dec(v_val_1768_);
v___x_1771_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1769_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1773_ = 0;
v___x_1774_ = lean_box(0);
v___x_1775_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 2, v___x_1775_);
lean_ctor_set(v___x_1766_, 1, v___x_1774_);
lean_ctor_set(v___x_1766_, 0, v_a_1772_);
v___x_1777_ = v___x_1766_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1772_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1773_, v_fst_1769_, v___x_1777_, v___y_1760_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1770_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1818_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1818_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1818_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
size_t v___x_1785_; size_t v___x_1786_; uint8_t v___x_1787_; 
v___x_1785_ = lean_ptr_addr(v_k_1550_);
v___x_1786_ = lean_ptr_addr(v_a_1781_);
v___x_1787_ = lean_usize_dec_eq(v___x_1785_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1797_; 
v_isSharedCheck_1797_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; lean_object* v_unused_1799_; 
v_unused_1798_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1798_);
v_unused_1799_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1799_);
v___x_1789_ = v_code_1425_;
v_isShared_1790_ = v_isSharedCheck_1797_;
goto v_resetjp_1788_;
}
else
{
lean_dec(v_code_1425_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1797_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v_a_1781_);
lean_ctor_set(v___x_1789_, 0, v_a_1779_);
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1779_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_a_1781_);
v___x_1792_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1794_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1792_);
v___x_1794_ = v___x_1783_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
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
else
{
size_t v___x_1800_; size_t v___x_1801_; uint8_t v___x_1802_; 
v___x_1800_ = lean_ptr_addr(v_decl_1549_);
v___x_1801_ = lean_ptr_addr(v_a_1779_);
v___x_1802_ = lean_usize_dec_eq(v___x_1800_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1812_; 
v_isSharedCheck_1812_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; lean_object* v_unused_1814_; 
v_unused_1813_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1813_);
v_unused_1814_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1814_);
v___x_1804_ = v_code_1425_;
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
else
{
lean_dec(v_code_1425_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 1, v_a_1781_);
lean_ctor_set(v___x_1804_, 0, v_a_1779_);
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1779_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_a_1781_);
v___x_1807_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1809_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1807_);
v___x_1809_ = v___x_1783_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
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
else
{
lean_object* v___x_1816_; 
lean_dec(v_a_1781_);
lean_dec(v_a_1779_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v_code_1425_);
v___x_1816_ = v___x_1783_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_code_1425_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
else
{
lean_dec(v_a_1779_);
lean_dec_ref_known(v_code_1425_, 2);
return v___x_1780_;
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_snd_1770_);
lean_dec_ref_known(v_code_1425_, 2);
v_a_1819_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1778_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1778_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_snd_1770_);
lean_dec(v_fst_1769_);
lean_del_object(v___x_1766_);
lean_dec_ref_known(v_code_1425_, 2);
v_a_1828_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1771_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1771_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
else
{
lean_object* v___x_1840_; 
lean_dec(v_a_1764_);
v___x_1840_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1755_, v_value_1551_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; uint8_t v___x_1842_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = lean_unbox(v_a_1841_);
lean_dec(v_a_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
lean_inc_ref(v_k_1550_);
v___x_1843_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1550_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1880_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1880_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1880_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
size_t v___x_1848_; size_t v___x_1849_; uint8_t v___x_1850_; 
v___x_1848_ = lean_ptr_addr(v_k_1550_);
v___x_1849_ = lean_ptr_addr(v_a_1844_);
v___x_1850_ = lean_usize_dec_eq(v___x_1848_, v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1860_; 
lean_inc_ref(v_decl_1549_);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; lean_object* v_unused_1862_; 
v_unused_1861_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1862_);
v___x_1852_ = v_code_1425_;
v_isShared_1853_ = v_isSharedCheck_1860_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v_code_1425_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1860_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v_a_1844_);
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_decl_1549_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_a_1844_);
v___x_1855_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1857_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1855_);
v___x_1857_ = v___x_1846_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
size_t v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = lean_ptr_addr(v_decl_1549_);
v___x_1864_ = lean_usize_dec_eq(v___x_1863_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1874_; 
lean_inc_ref(v_decl_1549_);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1874_ == 0)
{
lean_object* v_unused_1875_; lean_object* v_unused_1876_; 
v_unused_1875_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1875_);
v_unused_1876_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1876_);
v___x_1866_ = v_code_1425_;
v_isShared_1867_ = v_isSharedCheck_1874_;
goto v_resetjp_1865_;
}
else
{
lean_dec(v_code_1425_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1874_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 1, v_a_1844_);
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_decl_1549_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_a_1844_);
v___x_1869_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1871_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1869_);
v___x_1871_ = v___x_1846_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v___x_1878_; 
lean_dec(v_a_1844_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v_code_1425_);
v___x_1878_ = v___x_1846_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_code_1425_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1425_, 2);
return v___x_1843_;
}
}
else
{
lean_object* v___x_1881_; 
lean_inc_ref(v_decl_1549_);
v___x_1881_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1549_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; uint8_t v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v___x_1883_ = 0;
v___x_1884_ = lean_box(0);
v___x_1885_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1886_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1886_, 0, v_a_1882_);
lean_ctor_set(v___x_1886_, 1, v___x_1884_);
lean_ctor_set(v___x_1886_, 2, v___x_1885_);
lean_inc_ref(v_decl_1549_);
v___x_1887_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1883_, v_decl_1549_, v___x_1886_, v___y_1760_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
lean_inc_ref(v_k_1550_);
v___x_1889_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1550_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1927_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1927_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1927_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
size_t v___x_1894_; size_t v___x_1895_; uint8_t v___x_1896_; 
v___x_1894_ = lean_ptr_addr(v_k_1550_);
v___x_1895_ = lean_ptr_addr(v_a_1890_);
v___x_1896_ = lean_usize_dec_eq(v___x_1894_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1906_; 
v_isSharedCheck_1906_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1906_ == 0)
{
lean_object* v_unused_1907_; lean_object* v_unused_1908_; 
v_unused_1907_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1907_);
v_unused_1908_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1908_);
v___x_1898_ = v_code_1425_;
v_isShared_1899_ = v_isSharedCheck_1906_;
goto v_resetjp_1897_;
}
else
{
lean_dec(v_code_1425_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1906_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v_a_1890_);
lean_ctor_set(v___x_1898_, 0, v_a_1888_);
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1888_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_a_1890_);
v___x_1901_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1903_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1901_);
v___x_1903_ = v___x_1892_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
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
else
{
size_t v___x_1909_; size_t v___x_1910_; uint8_t v___x_1911_; 
v___x_1909_ = lean_ptr_addr(v_decl_1549_);
v___x_1910_ = lean_ptr_addr(v_a_1888_);
v___x_1911_ = lean_usize_dec_eq(v___x_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1921_; 
v_isSharedCheck_1921_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; lean_object* v_unused_1923_; 
v_unused_1922_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1922_);
v_unused_1923_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1923_);
v___x_1913_ = v_code_1425_;
v_isShared_1914_ = v_isSharedCheck_1921_;
goto v_resetjp_1912_;
}
else
{
lean_dec(v_code_1425_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1921_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v_a_1890_);
lean_ctor_set(v___x_1913_, 0, v_a_1888_);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1888_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_a_1890_);
v___x_1916_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1916_);
v___x_1918_ = v___x_1892_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v___x_1925_; 
lean_dec(v_a_1890_);
lean_dec(v_a_1888_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v_code_1425_);
v___x_1925_ = v___x_1892_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_code_1425_);
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
else
{
lean_dec(v_a_1888_);
lean_dec_ref_known(v_code_1425_, 2);
return v___x_1889_;
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref_known(v_code_1425_, 2);
v_a_1928_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1887_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1887_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref_known(v_code_1425_, 2);
v_a_1936_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1881_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1881_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref_known(v_code_1425_, 2);
v_a_1944_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1840_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1840_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref_known(v_value_1551_, 3);
lean_dec_ref_known(v_code_1425_, 2);
v_a_1952_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1763_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1763_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
v___jp_1960_:
{
uint8_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = 0;
v___x_1969_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1968_, v_sizeId_1961_, v___y_1965_);
lean_dec(v_sizeId_1961_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
if (lean_obj_tag(v_a_1970_) == 1)
{
lean_object* v_val_1971_; 
v_val_1971_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_val_1971_);
lean_dec_ref_known(v_a_1970_, 1);
if (lean_obj_tag(v_val_1971_) == 0)
{
lean_object* v_value_1972_; 
v_value_1972_ = lean_ctor_get(v_val_1971_, 0);
lean_inc_ref(v_value_1972_);
lean_dec_ref_known(v_val_1971_, 1);
if (lean_obj_tag(v_value_1972_) == 0)
{
lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2081_; 
v_isSharedCheck_2081_ = !lean_is_exclusive(v_value_1551_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; lean_object* v_unused_2083_; lean_object* v_unused_2084_; 
v_unused_2082_ = lean_ctor_get(v_value_1551_, 2);
lean_dec(v_unused_2082_);
v_unused_2083_ = lean_ctor_get(v_value_1551_, 1);
lean_dec(v_unused_2083_);
v_unused_2084_ = lean_ctor_get(v_value_1551_, 0);
lean_dec(v_unused_2084_);
v___x_1974_ = v_value_1551_;
v_isShared_1975_ = v_isSharedCheck_2081_;
goto v_resetjp_1973_;
}
else
{
lean_dec(v_value_1551_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2081_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v_val_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_val_1976_ = lean_ctor_get(v_value_1972_, 0);
lean_inc(v_val_1976_);
lean_dec_ref_known(v_value_1972_, 1);
v___x_1977_ = lean_unsigned_to_nat(0u);
v___x_1978_ = lean_nat_dec_eq(v_val_1976_, v___x_1977_);
lean_dec(v_val_1976_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_del_object(v___x_1974_);
lean_inc_ref(v_k_1550_);
v___x_1979_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1550_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2016_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_2016_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2016_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
size_t v___x_1984_; size_t v___x_1985_; uint8_t v___x_1986_; 
v___x_1984_ = lean_ptr_addr(v_k_1550_);
v___x_1985_ = lean_ptr_addr(v_a_1980_);
v___x_1986_ = lean_usize_dec_eq(v___x_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1996_; 
lean_inc_ref(v_decl_1549_);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; lean_object* v_unused_1998_; 
v_unused_1997_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1998_);
v___x_1988_ = v_code_1425_;
v_isShared_1989_ = v_isSharedCheck_1996_;
goto v_resetjp_1987_;
}
else
{
lean_dec(v_code_1425_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1996_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v_a_1980_);
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_decl_1549_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_a_1980_);
v___x_1991_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1991_);
v___x_1993_ = v___x_1982_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
size_t v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = lean_ptr_addr(v_decl_1549_);
v___x_2000_ = lean_usize_dec_eq(v___x_1999_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2010_; 
lean_inc_ref(v_decl_1549_);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; lean_object* v_unused_2012_; 
v_unused_2011_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_2011_);
v_unused_2012_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_2012_);
v___x_2002_ = v_code_1425_;
v_isShared_2003_ = v_isSharedCheck_2010_;
goto v_resetjp_2001_;
}
else
{
lean_dec(v_code_1425_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2010_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 1, v_a_1980_);
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_decl_1549_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_a_1980_);
v___x_2005_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2007_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_2005_);
v___x_2007_ = v___x_1982_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
else
{
lean_object* v___x_2014_; 
lean_dec(v_a_1980_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v_code_1425_);
v___x_2014_ = v___x_1982_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_code_1425_);
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
else
{
lean_dec_ref_known(v_code_1425_, 2);
return v___x_1979_;
}
}
else
{
lean_object* v___x_2017_; 
lean_inc_ref(v_decl_1549_);
v___x_2017_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1549_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = lean_box(0);
v___x_2020_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 2, v___x_2020_);
lean_ctor_set(v___x_1974_, 1, v___x_2019_);
lean_ctor_set(v___x_1974_, 0, v_a_2018_);
v___x_2022_ = v___x_1974_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2018_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; 
lean_inc_ref(v_decl_1549_);
v___x_2023_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1968_, v_decl_1549_, v___x_2022_, v___y_1965_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
lean_inc_ref(v_k_1550_);
v___x_2025_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1550_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2063_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2063_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2063_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
size_t v___x_2030_; size_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2030_ = lean_ptr_addr(v_k_1550_);
v___x_2031_ = lean_ptr_addr(v_a_2026_);
v___x_2032_ = lean_usize_dec_eq(v___x_2030_, v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2042_; 
v_isSharedCheck_2042_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; lean_object* v_unused_2044_; 
v_unused_2043_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_2043_);
v_unused_2044_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_2044_);
v___x_2034_ = v_code_1425_;
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v_code_1425_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v_a_2026_);
lean_ctor_set(v___x_2034_, 0, v_a_2024_);
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2024_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_a_2026_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2039_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2037_);
v___x_2039_ = v___x_2028_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
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
else
{
size_t v___x_2045_; size_t v___x_2046_; uint8_t v___x_2047_; 
v___x_2045_ = lean_ptr_addr(v_decl_1549_);
v___x_2046_ = lean_ptr_addr(v_a_2024_);
v___x_2047_ = lean_usize_dec_eq(v___x_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2057_; 
v_isSharedCheck_2057_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; lean_object* v_unused_2059_; 
v_unused_2058_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_2059_);
v___x_2049_ = v_code_1425_;
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
else
{
lean_dec(v_code_1425_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2057_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v_a_2026_);
lean_ctor_set(v___x_2049_, 0, v_a_2024_);
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2024_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_a_2026_);
v___x_2052_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2054_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2052_);
v___x_2054_ = v___x_2028_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
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
lean_object* v___x_2061_; 
lean_dec(v_a_2026_);
lean_dec(v_a_2024_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v_code_1425_);
v___x_2061_ = v___x_2028_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_code_1425_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
else
{
lean_dec(v_a_2024_);
lean_dec_ref_known(v_code_1425_, 2);
return v___x_2025_;
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref_known(v_code_1425_, 2);
v_a_2064_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2023_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2023_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_del_object(v___x_1974_);
lean_dec_ref_known(v_code_1425_, 2);
v_a_2073_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2017_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2017_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_1972_);
v___y_1757_ = v___y_1962_;
v___y_1758_ = v___y_1963_;
v___y_1759_ = v___y_1964_;
v___y_1760_ = v___y_1965_;
v___y_1761_ = v___y_1966_;
v___y_1762_ = v___y_1967_;
goto v___jp_1756_;
}
}
else
{
lean_dec(v_val_1971_);
v___y_1757_ = v___y_1962_;
v___y_1758_ = v___y_1963_;
v___y_1759_ = v___y_1964_;
v___y_1760_ = v___y_1965_;
v___y_1761_ = v___y_1966_;
v___y_1762_ = v___y_1967_;
goto v___jp_1756_;
}
}
else
{
lean_dec(v_a_1970_);
v___y_1757_ = v___y_1962_;
v___y_1758_ = v___y_1963_;
v___y_1759_ = v___y_1964_;
v___y_1760_ = v___y_1965_;
v___y_1761_ = v___y_1966_;
v___y_1762_ = v___y_1967_;
goto v___jp_1756_;
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref_known(v_value_1551_, 3);
lean_dec_ref_known(v_code_1425_, 2);
v_a_2085_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_1969_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_1969_);
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
else
{
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
v___y_1558_ = v_a_1431_;
goto v___jp_1552_;
}
}
else
{
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
v___y_1558_ = v_a_1431_;
goto v___jp_1552_;
}
}
else
{
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
v___y_1558_ = v_a_1431_;
goto v___jp_1552_;
}
}
else
{
v___y_1553_ = v_a_1426_;
v___y_1554_ = v_a_1427_;
v___y_1555_ = v_a_1428_;
v___y_1556_ = v_a_1429_;
v___y_1557_ = v_a_1430_;
v___y_1558_ = v_a_1431_;
goto v___jp_1552_;
}
v___jp_1552_:
{
lean_object* v___x_1559_; 
lean_inc_ref(v_k_1550_);
lean_inc_ref(v_decl_1549_);
v___x_1559_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1549_, v_k_1550_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
if (lean_obj_tag(v_a_1560_) == 1)
{
lean_object* v_val_1561_; lean_object* v_fst_1562_; lean_object* v_snd_1563_; lean_object* v___x_1564_; 
lean_dec(v_value_1551_);
v_val_1561_ = lean_ctor_get(v_a_1560_, 0);
lean_inc(v_val_1561_);
lean_dec_ref_known(v_a_1560_, 1);
v_fst_1562_ = lean_ctor_get(v_val_1561_, 0);
lean_inc_n(v_fst_1562_, 2);
v_snd_1563_ = lean_ctor_get(v_val_1561_, 1);
lean_inc(v_snd_1563_);
lean_dec(v_val_1561_);
v___x_1564_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1562_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = 0;
v___x_1567_ = lean_box(0);
v___x_1568_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1569_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1569_, 0, v_a_1565_);
lean_ctor_set(v___x_1569_, 1, v___x_1567_);
lean_ctor_set(v___x_1569_, 2, v___x_1568_);
v___x_1570_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1566_, v_fst_1562_, v___x_1569_, v___y_1556_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1572_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1563_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1610_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1610_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1610_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
size_t v___x_1577_; size_t v___x_1578_; uint8_t v___x_1579_; 
v___x_1577_ = lean_ptr_addr(v_k_1550_);
v___x_1578_ = lean_ptr_addr(v_a_1573_);
v___x_1579_ = lean_usize_dec_eq(v___x_1577_, v___x_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1589_; 
v_isSharedCheck_1589_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; lean_object* v_unused_1591_; 
v_unused_1590_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1591_);
v___x_1581_ = v_code_1425_;
v_isShared_1582_ = v_isSharedCheck_1589_;
goto v_resetjp_1580_;
}
else
{
lean_dec(v_code_1425_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1589_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v_a_1573_);
lean_ctor_set(v___x_1581_, 0, v_a_1571_);
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1571_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_a_1573_);
v___x_1584_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1586_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1584_);
v___x_1586_ = v___x_1575_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
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
else
{
size_t v___x_1592_; size_t v___x_1593_; uint8_t v___x_1594_; 
v___x_1592_ = lean_ptr_addr(v_decl_1549_);
v___x_1593_ = lean_ptr_addr(v_a_1571_);
v___x_1594_ = lean_usize_dec_eq(v___x_1592_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1604_; 
v_isSharedCheck_1604_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; lean_object* v_unused_1606_; 
v_unused_1605_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1606_);
v___x_1596_ = v_code_1425_;
v_isShared_1597_ = v_isSharedCheck_1604_;
goto v_resetjp_1595_;
}
else
{
lean_dec(v_code_1425_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1604_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 1, v_a_1573_);
lean_ctor_set(v___x_1596_, 0, v_a_1571_);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1571_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_a_1573_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1601_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1599_);
v___x_1601_ = v___x_1575_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v___x_1608_; 
lean_dec(v_a_1573_);
lean_dec(v_a_1571_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v_code_1425_);
v___x_1608_ = v___x_1575_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_code_1425_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
else
{
lean_dec(v_a_1571_);
lean_dec_ref_known(v_code_1425_, 2);
return v___x_1572_;
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec(v_snd_1563_);
lean_dec_ref_known(v_code_1425_, 2);
v_a_1611_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1570_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1570_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec(v_snd_1563_);
lean_dec(v_fst_1562_);
lean_dec_ref_known(v_code_1425_, 2);
v_a_1619_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1564_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1564_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
else
{
uint8_t v___x_1627_; lean_object* v___x_1628_; 
lean_dec(v_a_1560_);
v___x_1627_ = 1;
v___x_1628_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1627_, v_value_1551_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; uint8_t v___x_1630_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1630_ = lean_unbox(v_a_1629_);
lean_dec(v_a_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
lean_inc_ref(v_k_1550_);
v___x_1631_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1550_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1668_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1668_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1668_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
size_t v___x_1636_; size_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1636_ = lean_ptr_addr(v_k_1550_);
v___x_1637_ = lean_ptr_addr(v_a_1632_);
v___x_1638_ = lean_usize_dec_eq(v___x_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1648_; 
lean_inc_ref(v_decl_1549_);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; lean_object* v_unused_1650_; 
v_unused_1649_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1650_);
v___x_1640_ = v_code_1425_;
v_isShared_1641_ = v_isSharedCheck_1648_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v_code_1425_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1648_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v_a_1632_);
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_decl_1549_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_a_1632_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1643_);
v___x_1645_ = v___x_1634_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
size_t v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = lean_ptr_addr(v_decl_1549_);
v___x_1652_ = lean_usize_dec_eq(v___x_1651_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1662_; 
lean_inc_ref(v_decl_1549_);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; lean_object* v_unused_1664_; 
v_unused_1663_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1664_);
v___x_1654_ = v_code_1425_;
v_isShared_1655_ = v_isSharedCheck_1662_;
goto v_resetjp_1653_;
}
else
{
lean_dec(v_code_1425_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1662_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 1, v_a_1632_);
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_decl_1549_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_a_1632_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1657_);
v___x_1659_ = v___x_1634_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_a_1632_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v_code_1425_);
v___x_1666_ = v___x_1634_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_code_1425_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_code_1425_, 2);
return v___x_1631_;
}
}
else
{
lean_object* v___x_1669_; 
lean_inc_ref(v_decl_1549_);
v___x_1669_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1549_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1669_, 1);
v___x_1671_ = 0;
v___x_1672_ = lean_box(0);
v___x_1673_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1674_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1674_, 0, v_a_1670_);
lean_ctor_set(v___x_1674_, 1, v___x_1672_);
lean_ctor_set(v___x_1674_, 2, v___x_1673_);
lean_inc_ref(v_decl_1549_);
v___x_1675_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1671_, v_decl_1549_, v___x_1674_, v___y_1556_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1677_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
lean_inc_ref(v_k_1550_);
v___x_1677_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1550_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1715_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1715_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1715_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
size_t v___x_1682_; size_t v___x_1683_; uint8_t v___x_1684_; 
v___x_1682_ = lean_ptr_addr(v_k_1550_);
v___x_1683_ = lean_ptr_addr(v_a_1678_);
v___x_1684_ = lean_usize_dec_eq(v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1694_; 
v_isSharedCheck_1694_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; lean_object* v_unused_1696_; 
v_unused_1695_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1695_);
v_unused_1696_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1696_);
v___x_1686_ = v_code_1425_;
v_isShared_1687_ = v_isSharedCheck_1694_;
goto v_resetjp_1685_;
}
else
{
lean_dec(v_code_1425_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1694_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v_a_1678_);
lean_ctor_set(v___x_1686_, 0, v_a_1676_);
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1676_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_a_1678_);
v___x_1689_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1691_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1689_);
v___x_1691_ = v___x_1680_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
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
else
{
size_t v___x_1697_; size_t v___x_1698_; uint8_t v___x_1699_; 
v___x_1697_ = lean_ptr_addr(v_decl_1549_);
v___x_1698_ = lean_ptr_addr(v_a_1676_);
v___x_1699_ = lean_usize_dec_eq(v___x_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1709_; 
v_isSharedCheck_1709_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; lean_object* v_unused_1711_; 
v_unused_1710_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1711_);
v___x_1701_ = v_code_1425_;
v_isShared_1702_ = v_isSharedCheck_1709_;
goto v_resetjp_1700_;
}
else
{
lean_dec(v_code_1425_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1709_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v_a_1678_);
lean_ctor_set(v___x_1701_, 0, v_a_1676_);
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1676_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_a_1678_);
v___x_1704_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1706_; 
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1704_);
v___x_1706_ = v___x_1680_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
else
{
lean_object* v___x_1713_; 
lean_dec(v_a_1678_);
lean_dec(v_a_1676_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v_code_1425_);
v___x_1713_ = v___x_1680_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_code_1425_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
else
{
lean_dec(v_a_1676_);
lean_dec_ref_known(v_code_1425_, 2);
return v___x_1677_;
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref_known(v_code_1425_, 2);
v_a_1716_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1675_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1675_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref_known(v_code_1425_, 2);
v_a_1724_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1669_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1669_);
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
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec_ref_known(v_code_1425_, 2);
v_a_1732_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1628_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1628_);
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
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_value_1551_);
lean_dec_ref_known(v_code_1425_, 2);
v_a_1740_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1559_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1559_);
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
case 1:
{
lean_object* v_decl_2109_; lean_object* v_k_2110_; 
v_decl_2109_ = lean_ctor_get(v_code_1425_, 0);
v_k_2110_ = lean_ctor_get(v_code_1425_, 1);
lean_inc_ref(v_k_2110_);
lean_inc_ref(v_decl_2109_);
v_decl_1434_ = v_decl_2109_;
v_k_1435_ = v_k_2110_;
v___y_1436_ = v_a_1426_;
v___y_1437_ = v_a_1427_;
v___y_1438_ = v_a_1428_;
v___y_1439_ = v_a_1429_;
v___y_1440_ = v_a_1430_;
v___y_1441_ = v_a_1431_;
goto v___jp_1433_;
}
case 2:
{
lean_object* v_decl_2111_; lean_object* v_k_2112_; 
v_decl_2111_ = lean_ctor_get(v_code_1425_, 0);
v_k_2112_ = lean_ctor_get(v_code_1425_, 1);
lean_inc_ref(v_k_2112_);
lean_inc_ref(v_decl_2111_);
v_decl_1434_ = v_decl_2111_;
v_k_1435_ = v_k_2112_;
v___y_1436_ = v_a_1426_;
v___y_1437_ = v_a_1427_;
v___y_1438_ = v_a_1428_;
v___y_1439_ = v_a_1429_;
v___y_1440_ = v_a_1430_;
v___y_1441_ = v_a_1431_;
goto v___jp_1433_;
}
case 4:
{
lean_object* v_cases_2113_; lean_object* v_typeName_2114_; lean_object* v_resultType_2115_; lean_object* v_discr_2116_; lean_object* v_alts_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2156_; 
v_cases_2113_ = lean_ctor_get(v_code_1425_, 0);
lean_inc_ref(v_cases_2113_);
v_typeName_2114_ = lean_ctor_get(v_cases_2113_, 0);
v_resultType_2115_ = lean_ctor_get(v_cases_2113_, 1);
v_discr_2116_ = lean_ctor_get(v_cases_2113_, 2);
v_alts_2117_ = lean_ctor_get(v_cases_2113_, 3);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_cases_2113_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2119_ = v_cases_2113_;
v_isShared_2120_ = v_isSharedCheck_2156_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_alts_2117_);
lean_inc(v_discr_2116_);
lean_inc(v_resultType_2115_);
lean_inc(v_typeName_2114_);
lean_dec(v_cases_2113_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2156_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_2117_);
v___x_2122_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v___x_2121_, v_alts_2117_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2147_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2147_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2147_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
size_t v___x_2127_; size_t v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = lean_ptr_addr(v_alts_2117_);
lean_dec_ref(v_alts_2117_);
v___x_2128_ = lean_ptr_addr(v_a_2123_);
v___x_2129_ = lean_usize_dec_eq(v___x_2127_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2142_; 
v_isSharedCheck_2142_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; 
v_unused_2143_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_2143_);
v___x_2131_ = v_code_1425_;
v_isShared_2132_ = v_isSharedCheck_2142_;
goto v_resetjp_2130_;
}
else
{
lean_dec(v_code_1425_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2142_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 3, v_a_2123_);
v___x_2134_ = v___x_2119_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_typeName_2114_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_resultType_2115_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_discr_2116_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_a_2123_);
v___x_2134_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2136_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2134_);
v___x_2136_ = v___x_2131_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2138_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2136_);
v___x_2138_ = v___x_2125_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_object* v___x_2145_; 
lean_dec(v_a_2123_);
lean_del_object(v___x_2119_);
lean_dec(v_discr_2116_);
lean_dec_ref(v_resultType_2115_);
lean_dec(v_typeName_2114_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v_code_1425_);
v___x_2145_ = v___x_2125_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_code_1425_);
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
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_del_object(v___x_2119_);
lean_dec_ref(v_alts_2117_);
lean_dec(v_discr_2116_);
lean_dec_ref(v_resultType_2115_);
lean_dec(v_typeName_2114_);
lean_dec_ref_known(v_code_1425_, 1);
v_a_2148_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2122_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2122_);
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
default: 
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v_code_1425_);
return v___x_2157_;
}
}
v___jp_1433_:
{
lean_object* v_params_1442_; lean_object* v_type_1443_; lean_object* v_value_1444_; lean_object* v___x_1445_; 
v_params_1442_ = lean_ctor_get(v_decl_1434_, 2);
lean_inc_ref(v_params_1442_);
v_type_1443_ = lean_ctor_get(v_decl_1434_, 3);
lean_inc_ref(v_type_1443_);
v_value_1444_ = lean_ctor_get(v_decl_1434_, 4);
lean_inc_ref(v_value_1444_);
v___x_1445_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_value_1444_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v___x_1447_ = 0;
v___x_1448_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1447_, v_decl_1434_, v_type_1443_, v_params_1442_, v_a_1446_, v___y_1439_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1450_) == 0)
{
switch(lean_obj_tag(v_code_1425_))
{
case 1:
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1490_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1490_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1490_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v_decl_1455_; lean_object* v_k_1456_; size_t v___x_1457_; size_t v___x_1458_; uint8_t v___x_1459_; 
v_decl_1455_ = lean_ctor_get(v_code_1425_, 0);
v_k_1456_ = lean_ctor_get(v_code_1425_, 1);
v___x_1457_ = lean_ptr_addr(v_k_1456_);
v___x_1458_ = lean_ptr_addr(v_a_1451_);
v___x_1459_ = lean_usize_dec_eq(v___x_1457_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1469_; 
v_isSharedCheck_1469_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; lean_object* v_unused_1471_; 
v_unused_1470_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1471_);
v___x_1461_ = v_code_1425_;
v_isShared_1462_ = v_isSharedCheck_1469_;
goto v_resetjp_1460_;
}
else
{
lean_dec(v_code_1425_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1469_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 1, v_a_1451_);
lean_ctor_set(v___x_1461_, 0, v_a_1449_);
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1449_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_a_1451_);
v___x_1464_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
lean_object* v___x_1466_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1464_);
v___x_1466_ = v___x_1453_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
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
else
{
size_t v___x_1472_; size_t v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = lean_ptr_addr(v_decl_1455_);
v___x_1473_ = lean_ptr_addr(v_a_1449_);
v___x_1474_ = lean_usize_dec_eq(v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1484_; 
v_isSharedCheck_1484_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; lean_object* v_unused_1486_; 
v_unused_1485_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1486_);
v___x_1476_ = v_code_1425_;
v_isShared_1477_ = v_isSharedCheck_1484_;
goto v_resetjp_1475_;
}
else
{
lean_dec(v_code_1425_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1484_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v_a_1451_);
lean_ctor_set(v___x_1476_, 0, v_a_1449_);
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1449_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_a_1451_);
v___x_1479_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1481_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1479_);
v___x_1481_ = v___x_1453_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v___x_1488_; 
lean_dec(v_a_1451_);
lean_dec(v_a_1449_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v_code_1425_);
v___x_1488_ = v___x_1453_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_code_1425_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
case 2:
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1530_; 
v_a_1491_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1493_ = v___x_1450_;
v_isShared_1494_ = v_isSharedCheck_1530_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1450_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1530_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_decl_1495_; lean_object* v_k_1496_; size_t v___x_1497_; size_t v___x_1498_; uint8_t v___x_1499_; 
v_decl_1495_ = lean_ctor_get(v_code_1425_, 0);
v_k_1496_ = lean_ctor_get(v_code_1425_, 1);
v___x_1497_ = lean_ptr_addr(v_k_1496_);
v___x_1498_ = lean_ptr_addr(v_a_1491_);
v___x_1499_ = lean_usize_dec_eq(v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1509_; 
v_isSharedCheck_1509_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; 
v_unused_1510_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1511_);
v___x_1501_ = v_code_1425_;
v_isShared_1502_ = v_isSharedCheck_1509_;
goto v_resetjp_1500_;
}
else
{
lean_dec(v_code_1425_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1509_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 1, v_a_1491_);
lean_ctor_set(v___x_1501_, 0, v_a_1449_);
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1449_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_a_1491_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1504_);
v___x_1506_ = v___x_1493_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
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
else
{
size_t v___x_1512_; size_t v___x_1513_; uint8_t v___x_1514_; 
v___x_1512_ = lean_ptr_addr(v_decl_1495_);
v___x_1513_ = lean_ptr_addr(v_a_1449_);
v___x_1514_ = lean_usize_dec_eq(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1524_; 
v_isSharedCheck_1524_ = !lean_is_exclusive(v_code_1425_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; lean_object* v_unused_1526_; 
v_unused_1525_ = lean_ctor_get(v_code_1425_, 1);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_code_1425_, 0);
lean_dec(v_unused_1526_);
v___x_1516_ = v_code_1425_;
v_isShared_1517_ = v_isSharedCheck_1524_;
goto v_resetjp_1515_;
}
else
{
lean_dec(v_code_1425_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1524_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 1, v_a_1491_);
lean_ctor_set(v___x_1516_, 0, v_a_1449_);
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1449_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_a_1491_);
v___x_1519_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1519_);
v___x_1521_ = v___x_1493_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
lean_object* v___x_1528_; 
lean_dec(v_a_1491_);
lean_dec(v_a_1449_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v_code_1425_);
v___x_1528_ = v___x_1493_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_code_1425_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
default: 
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_a_1449_);
lean_dec_ref(v_code_1425_);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v___x_1450_, 0);
lean_dec(v_unused_1540_);
v___x_1532_ = v___x_1450_;
v_isShared_1533_ = v_isSharedCheck_1539_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v___x_1450_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1539_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1534_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3, &l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3);
v___x_1535_ = l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(v___x_1534_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1535_);
v___x_1537_ = v___x_1532_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
else
{
lean_dec(v_a_1449_);
lean_dec_ref(v_code_1425_);
return v___x_1450_;
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_k_1435_);
lean_dec_ref(v_code_1425_);
v_a_1541_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1448_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1448_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_dec_ref(v_type_1443_);
lean_dec_ref(v_params_1442_);
lean_dec_ref(v_k_1435_);
lean_dec_ref(v_decl_1434_);
lean_dec_ref(v_code_1425_);
return v___x_1445_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object* v_i_2158_, lean_object* v_as_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = lean_array_get_size(v_as_2159_);
v___x_2168_ = lean_nat_dec_lt(v_i_2158_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; 
lean_dec(v_i_2158_);
v___x_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2169_, 0, v_as_2159_);
return v___x_2169_;
}
else
{
lean_object* v_a_2170_; lean_object* v___y_2172_; 
v_a_2170_ = lean_array_fget_borrowed(v_as_2159_, v_i_2158_);
switch(lean_obj_tag(v_a_2170_))
{
case 0:
{
lean_object* v_code_2194_; 
v_code_2194_ = lean_ctor_get(v_a_2170_, 2);
lean_inc_ref(v_code_2194_);
v___y_2172_ = v_code_2194_;
goto v___jp_2171_;
}
case 1:
{
lean_object* v_code_2195_; 
v_code_2195_ = lean_ctor_get(v_a_2170_, 1);
lean_inc_ref(v_code_2195_);
v___y_2172_ = v_code_2195_;
goto v___jp_2171_;
}
default: 
{
lean_object* v_code_2196_; 
v_code_2196_ = lean_ctor_get(v_a_2170_, 0);
lean_inc_ref(v_code_2196_);
v___y_2172_ = v_code_2196_;
goto v___jp_2171_;
}
}
v___jp_2171_:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v___y_2172_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; size_t v___x_2176_; size_t v___x_2177_; uint8_t v___x_2178_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
lean_inc(v_a_2170_);
v___x_2175_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_2170_, v_a_2174_);
v___x_2176_ = lean_ptr_addr(v_a_2170_);
v___x_2177_ = lean_ptr_addr(v___x_2175_);
v___x_2178_ = lean_usize_dec_eq(v___x_2176_, v___x_2177_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = lean_unsigned_to_nat(1u);
v___x_2180_ = lean_nat_add(v_i_2158_, v___x_2179_);
v___x_2181_ = lean_array_fset(v_as_2159_, v_i_2158_, v___x_2175_);
lean_dec(v_i_2158_);
v_i_2158_ = v___x_2180_;
v_as_2159_ = v___x_2181_;
goto _start;
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec_ref(v___x_2175_);
v___x_2183_ = lean_unsigned_to_nat(1u);
v___x_2184_ = lean_nat_add(v_i_2158_, v___x_2183_);
lean_dec(v_i_2158_);
v_i_2158_ = v___x_2184_;
goto _start;
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v_as_2159_);
lean_dec(v_i_2158_);
v_a_2186_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2173_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2173_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object* v_i_2197_, lean_object* v_as_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_2197_, v_as_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object* v_code_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_code_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(lean_object* v_f_2216_, lean_object* v_v_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
if (lean_obj_tag(v_v_2217_) == 0)
{
lean_object* v_code_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2249_; 
v_code_2225_ = lean_ctor_get(v_v_2217_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_v_2217_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2227_ = v_v_2217_;
v_isShared_2228_ = v_isSharedCheck_2249_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_code_2225_);
lean_dec(v_v_2217_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2249_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; 
lean_inc(v___y_2223_);
lean_inc_ref(v___y_2222_);
lean_inc(v___y_2221_);
lean_inc_ref(v___y_2220_);
lean_inc(v___y_2219_);
lean_inc_ref(v___y_2218_);
v___x_2229_ = lean_apply_8(v_f_2216_, v_code_2225_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, lean_box(0));
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2240_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2240_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2240_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v_a_2230_);
v___x_2235_ = v___x_2227_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2237_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2235_);
v___x_2237_ = v___x_2232_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
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
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_del_object(v___x_2227_);
v_a_2241_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2229_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2229_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
else
{
lean_object* v___x_2250_; 
lean_dec_ref(v_f_2216_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v_v_2217_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(lean_object* v_f_2251_, lean_object* v_v_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2251_, v_v_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(uint8_t v_pu_2261_, lean_object* v_f_2262_, lean_object* v_v_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_2262_, v_v_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(lean_object* v_pu_2272_, lean_object* v_f_2273_, lean_object* v_v_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v_pu_boxed_2282_; lean_object* v_res_2283_; 
v_pu_boxed_2282_ = lean_unbox(v_pu_2272_);
v_res_2283_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_boxed_2282_, v_f_2273_, v_v_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object* v_decl_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v_toSignature_2293_; lean_object* v_value_2294_; uint8_t v_recursive_2295_; lean_object* v_inlineAttr_x3f_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2321_; 
v_toSignature_2293_ = lean_ctor_get(v_decl_2285_, 0);
v_value_2294_ = lean_ctor_get(v_decl_2285_, 1);
v_recursive_2295_ = lean_ctor_get_uint8(v_decl_2285_, sizeof(void*)*3);
v_inlineAttr_x3f_2296_ = lean_ctor_get(v_decl_2285_, 2);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_decl_2285_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2298_ = v_decl_2285_;
v_isShared_2299_ = v_isSharedCheck_2321_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_inlineAttr_x3f_2296_);
lean_inc(v_value_2294_);
lean_inc(v_toSignature_2293_);
lean_dec(v_decl_2285_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2321_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0));
v___x_2301_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v___x_2300_, v_value_2294_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2312_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2312_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2312_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v_a_2302_);
v___x_2307_ = v___x_2298_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_toSignature_2293_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_a_2302_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_inlineAttr_x3f_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2311_, sizeof(void*)*3, v_recursive_2295_);
v___x_2307_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2309_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2307_);
v___x_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_del_object(v___x_2298_);
lean_dec(v_inlineAttr_x3f_2296_);
lean_dec_ref(v_toSignature_2293_);
v_a_2313_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2301_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2301_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(lean_object* v_decl_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
return v_res_2330_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_2334_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0));
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v___x_2333_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* v_decl_2336_, lean_object* v_sccDecls_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v_toSignature_2346_; lean_object* v_name_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2343_ = lean_unsigned_to_nat(0u);
v___x_2344_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1);
v___x_2345_ = lean_st_mk_ref(v___x_2344_);
v_toSignature_2346_ = lean_ctor_get(v_decl_2336_, 0);
v_name_2347_ = lean_ctor_get(v_toSignature_2346_, 0);
lean_inc(v_name_2347_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v_name_2347_);
lean_ctor_set(v___x_2348_, 1, v_sccDecls_2337_);
v___x_2349_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2336_, v___x_2348_, v___x_2345_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec_ref_known(v___x_2348_, 2);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2375_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2375_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2375_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v_decls_2355_; lean_object* v_decl_2357_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2354_ = lean_st_ref_get(v___x_2345_);
lean_dec(v___x_2345_);
v_decls_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc_ref(v_decls_2355_);
lean_dec(v___x_2354_);
v___x_2362_ = lean_array_get_size(v_decls_2355_);
v___x_2363_ = lean_nat_dec_eq(v___x_2362_, v___x_2343_);
if (v___x_2363_ == 0)
{
uint8_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = 0;
v___x_2365_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2364_, v_a_2350_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2365_, 1);
v_decl_2357_ = v_a_2366_;
goto v___jp_2356_;
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec_ref(v_decls_2355_);
lean_del_object(v___x_2352_);
v_a_2367_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2365_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2365_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
v_decl_2357_ = v_a_2350_;
goto v___jp_2356_;
}
v___jp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = lean_array_push(v_decls_2355_, v_decl_2357_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2358_);
v___x_2360_ = v___x_2352_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v___x_2345_);
v_a_2376_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2349_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2349_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(lean_object* v_decl_2384_, lean_object* v_sccDecls_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v_decl_2384_, v_sccDecls_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(lean_object* v_decls_2392_, lean_object* v_as_2393_, size_t v_i_2394_, size_t v_stop_2395_, lean_object* v_b_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_a_2403_; uint8_t v___x_2407_; 
v___x_2407_ = lean_usize_dec_eq(v_i_2394_, v_stop_2395_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_array_uget_borrowed(v_as_2393_, v_i_2394_);
lean_inc_ref(v_decls_2392_);
lean_inc(v___x_2408_);
v___x_2409_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v___x_2408_, v_decls_2392_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2411_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v___x_2411_ = l_Array_append___redArg(v_b_2396_, v_a_2410_);
lean_dec(v_a_2410_);
v_a_2403_ = v___x_2411_;
goto v___jp_2402_;
}
else
{
lean_dec_ref(v_b_2396_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2412_; 
v_a_2412_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2409_, 1);
v_a_2403_ = v_a_2412_;
goto v___jp_2402_;
}
else
{
lean_dec_ref(v_decls_2392_);
return v___x_2409_;
}
}
}
else
{
lean_object* v___x_2413_; 
lean_dec_ref(v_decls_2392_);
v___x_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2413_, 0, v_b_2396_);
return v___x_2413_;
}
v___jp_2402_:
{
size_t v___x_2404_; size_t v___x_2405_; 
v___x_2404_ = ((size_t)1ULL);
v___x_2405_ = lean_usize_add(v_i_2394_, v___x_2404_);
v_i_2394_ = v___x_2405_;
v_b_2396_ = v_a_2403_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object* v_decls_2414_, lean_object* v_as_2415_, lean_object* v_i_2416_, lean_object* v_stop_2417_, lean_object* v_b_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
size_t v_i_boxed_2424_; size_t v_stop_boxed_2425_; lean_object* v_res_2426_; 
v_i_boxed_2424_ = lean_unbox_usize(v_i_2416_);
lean_dec(v_i_2416_);
v_stop_boxed_2425_ = lean_unbox_usize(v_stop_2417_);
lean_dec(v_stop_2417_);
v_res_2426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2414_, v_as_2415_, v_i_boxed_2424_, v_stop_boxed_2425_, v_b_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec_ref(v_as_2415_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* v___x_2427_, lean_object* v_decls_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_2429_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2459_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2459_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2459_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
uint8_t v_extractClosed_2439_; 
v_extractClosed_2439_ = lean_ctor_get_uint8(v_a_2435_, sizeof(void*)*4 + 1);
lean_dec(v_a_2435_);
if (v_extractClosed_2439_ == 0)
{
lean_object* v___x_2441_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v_decls_2428_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_decls_2428_);
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
lean_object* v___x_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2443_ = lean_mk_empty_array_with_capacity(v___x_2427_);
v___x_2444_ = lean_array_get_size(v_decls_2428_);
v___x_2445_ = lean_nat_dec_lt(v___x_2427_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2447_; 
lean_dec_ref(v_decls_2428_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2443_);
v___x_2447_ = v___x_2437_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2443_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
else
{
uint8_t v___x_2449_; 
v___x_2449_ = lean_nat_dec_le(v___x_2444_, v___x_2444_);
if (v___x_2449_ == 0)
{
if (v___x_2445_ == 0)
{
lean_object* v___x_2451_; 
lean_dec_ref(v_decls_2428_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2443_);
v___x_2451_ = v___x_2437_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2443_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
else
{
size_t v___x_2453_; size_t v___x_2454_; lean_object* v___x_2455_; 
lean_del_object(v___x_2437_);
v___x_2453_ = ((size_t)0ULL);
v___x_2454_ = lean_usize_of_nat(v___x_2444_);
lean_inc_ref(v_decls_2428_);
v___x_2455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2428_, v_decls_2428_, v___x_2453_, v___x_2454_, v___x_2443_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec_ref(v_decls_2428_);
return v___x_2455_;
}
}
else
{
size_t v___x_2456_; size_t v___x_2457_; lean_object* v___x_2458_; 
lean_del_object(v___x_2437_);
v___x_2456_ = ((size_t)0ULL);
v___x_2457_ = lean_usize_of_nat(v___x_2444_);
lean_inc_ref(v_decls_2428_);
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2428_, v_decls_2428_, v___x_2456_, v___x_2457_, v___x_2443_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec_ref(v_decls_2428_);
return v___x_2458_;
}
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v_decls_2428_);
v_a_2460_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2434_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2434_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object* v___x_2468_, lean_object* v_decls_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(v___x_2468_, v_decls_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___x_2468_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2558_; uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2558_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2559_ = 1;
v___x_2560_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2561_ = l_Lean_registerTraceClass(v___x_2558_, v___x_2559_, v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
return v_res_2563_;
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
