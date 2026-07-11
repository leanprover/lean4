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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_bool_not(v_____do__lift_171_);
v___x_180_ = lean_box(v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object* v_____do__lift_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
uint8_t v_____do__lift_16814__boxed_190_; lean_object* v_res_191_; 
v_____do__lift_16814__boxed_190_ = lean_unbox(v_____do__lift_182_);
v_res_191_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v_____do__lift_16814__boxed_190_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_191_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8___redArg(lean_object* v_a_192_, lean_object* v_x_193_){
_start:
{
if (lean_obj_tag(v_x_193_) == 0)
{
uint8_t v___x_194_; 
v___x_194_ = 0;
return v___x_194_;
}
else
{
lean_object* v_key_195_; lean_object* v_tail_196_; uint8_t v___x_197_; 
v_key_195_ = lean_ctor_get(v_x_193_, 0);
v_tail_196_ = lean_ctor_get(v_x_193_, 2);
v___x_197_ = l_Lean_instBEqFVarId_beq(v_key_195_, v_a_192_);
if (v___x_197_ == 0)
{
v_x_193_ = v_tail_196_;
goto _start;
}
else
{
return v___x_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8___redArg___boxed(lean_object* v_a_199_, lean_object* v_x_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8___redArg(v_a_199_, v_x_200_);
lean_dec(v_x_200_);
lean_dec(v_a_199_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__10___redArg(lean_object* v_a_203_, lean_object* v_b_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_dec(v_b_204_);
lean_dec(v_a_203_);
return v_x_205_;
}
else
{
lean_object* v_key_206_; lean_object* v_value_207_; lean_object* v_tail_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_220_; 
v_key_206_ = lean_ctor_get(v_x_205_, 0);
v_value_207_ = lean_ctor_get(v_x_205_, 1);
v_tail_208_ = lean_ctor_get(v_x_205_, 2);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_220_ == 0)
{
v___x_210_ = v_x_205_;
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_tail_208_);
lean_inc(v_value_207_);
lean_inc(v_key_206_);
lean_dec(v_x_205_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
uint8_t v___x_212_; 
v___x_212_ = l_Lean_instBEqFVarId_beq(v_key_206_, v_a_203_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__10___redArg(v_a_203_, v_b_204_, v_tail_208_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 2, v___x_213_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_key_206_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_value_207_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
else
{
lean_object* v___x_218_; 
lean_dec(v_value_207_);
lean_dec(v_key_206_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v_b_204_);
lean_ctor_set(v___x_210_, 0, v_a_203_);
v___x_218_ = v___x_210_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_203_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_b_204_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_tail_208_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10_spec__11___redArg(lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
return v_x_221_;
}
else
{
lean_object* v_key_223_; lean_object* v_value_224_; lean_object* v_tail_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_248_; 
v_key_223_ = lean_ctor_get(v_x_222_, 0);
v_value_224_ = lean_ctor_get(v_x_222_, 1);
v_tail_225_ = lean_ctor_get(v_x_222_, 2);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_248_ == 0)
{
v___x_227_ = v_x_222_;
v_isShared_228_ = v_isSharedCheck_248_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_tail_225_);
lean_inc(v_value_224_);
lean_inc(v_key_223_);
lean_dec(v_x_222_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_248_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v_fold_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_229_ = lean_array_get_size(v_x_221_);
v___x_230_ = l_Lean_instHashableFVarId_hash(v_key_223_);
v___x_231_ = 32ULL;
v___x_232_ = lean_uint64_shift_right(v___x_230_, v___x_231_);
v_fold_233_ = lean_uint64_xor(v___x_230_, v___x_232_);
v___x_234_ = 16ULL;
v___x_235_ = lean_uint64_shift_right(v_fold_233_, v___x_234_);
v___x_236_ = lean_uint64_xor(v_fold_233_, v___x_235_);
v___x_237_ = lean_uint64_to_usize(v___x_236_);
v___x_238_ = lean_usize_of_nat(v___x_229_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_sub(v___x_238_, v___x_239_);
v___x_241_ = lean_usize_land(v___x_237_, v___x_240_);
v___x_242_ = lean_array_uget_borrowed(v_x_221_, v___x_241_);
lean_inc(v___x_242_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 2, v___x_242_);
v___x_244_ = v___x_227_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_key_223_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_value_224_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v___x_242_);
v___x_244_ = v_reuseFailAlloc_247_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; 
v___x_245_ = lean_array_uset(v_x_221_, v___x_241_, v___x_244_);
v_x_221_ = v___x_245_;
v_x_222_ = v_tail_225_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10___redArg(lean_object* v_i_249_, lean_object* v_source_250_, lean_object* v_target_251_){
_start:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_array_get_size(v_source_250_);
v___x_253_ = lean_nat_dec_lt(v_i_249_, v___x_252_);
if (v___x_253_ == 0)
{
lean_dec_ref(v_source_250_);
lean_dec(v_i_249_);
return v_target_251_;
}
else
{
lean_object* v_es_254_; lean_object* v___x_255_; lean_object* v_source_256_; lean_object* v_target_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_es_254_ = lean_array_fget(v_source_250_, v_i_249_);
v___x_255_ = lean_box(0);
v_source_256_ = lean_array_fset(v_source_250_, v_i_249_, v___x_255_);
v_target_257_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10_spec__11___redArg(v_target_251_, v_es_254_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_add(v_i_249_, v___x_258_);
lean_dec(v_i_249_);
v_i_249_ = v___x_259_;
v_source_250_ = v_source_256_;
v_target_251_ = v_target_257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9___redArg(lean_object* v_data_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_nbuckets_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_262_ = lean_array_get_size(v_data_261_);
v___x_263_ = lean_unsigned_to_nat(2u);
v_nbuckets_264_ = lean_nat_mul(v___x_262_, v___x_263_);
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_box(0);
v___x_267_ = lean_mk_array(v_nbuckets_264_, v___x_266_);
v___x_268_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10___redArg(v___x_265_, v_data_261_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(lean_object* v_m_269_, lean_object* v_a_270_, lean_object* v_b_271_){
_start:
{
lean_object* v_size_272_; lean_object* v_buckets_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_316_; 
v_size_272_ = lean_ctor_get(v_m_269_, 0);
v_buckets_273_ = lean_ctor_get(v_m_269_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_m_269_);
if (v_isSharedCheck_316_ == 0)
{
v___x_275_ = v_m_269_;
v_isShared_276_ = v_isSharedCheck_316_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_buckets_273_);
lean_inc(v_size_272_);
lean_dec(v_m_269_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_316_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; uint64_t v_fold_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; lean_object* v_bkt_290_; uint8_t v___x_291_; 
v___x_277_ = lean_array_get_size(v_buckets_273_);
v___x_278_ = l_Lean_instHashableFVarId_hash(v_a_270_);
v___x_279_ = 32ULL;
v___x_280_ = lean_uint64_shift_right(v___x_278_, v___x_279_);
v_fold_281_ = lean_uint64_xor(v___x_278_, v___x_280_);
v___x_282_ = 16ULL;
v___x_283_ = lean_uint64_shift_right(v_fold_281_, v___x_282_);
v___x_284_ = lean_uint64_xor(v_fold_281_, v___x_283_);
v___x_285_ = lean_uint64_to_usize(v___x_284_);
v___x_286_ = lean_usize_of_nat(v___x_277_);
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_sub(v___x_286_, v___x_287_);
v___x_289_ = lean_usize_land(v___x_285_, v___x_288_);
v_bkt_290_ = lean_array_uget_borrowed(v_buckets_273_, v___x_289_);
v___x_291_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8___redArg(v_a_270_, v_bkt_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v_size_x27_293_; lean_object* v___x_294_; lean_object* v_buckets_x27_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v_size_x27_293_ = lean_nat_add(v_size_272_, v___x_292_);
lean_dec(v_size_272_);
lean_inc(v_bkt_290_);
v___x_294_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_294_, 0, v_a_270_);
lean_ctor_set(v___x_294_, 1, v_b_271_);
lean_ctor_set(v___x_294_, 2, v_bkt_290_);
v_buckets_x27_295_ = lean_array_uset(v_buckets_273_, v___x_289_, v___x_294_);
v___x_296_ = lean_unsigned_to_nat(4u);
v___x_297_ = lean_nat_mul(v_size_x27_293_, v___x_296_);
v___x_298_ = lean_unsigned_to_nat(3u);
v___x_299_ = lean_nat_div(v___x_297_, v___x_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_array_get_size(v_buckets_x27_295_);
v___x_301_ = lean_nat_dec_le(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
if (v___x_301_ == 0)
{
lean_object* v_val_302_; lean_object* v___x_304_; 
v_val_302_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9___redArg(v_buckets_x27_295_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v_val_302_);
lean_ctor_set(v___x_275_, 0, v_size_x27_293_);
v___x_304_ = v___x_275_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_size_x27_293_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_val_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
lean_object* v___x_307_; 
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v_buckets_x27_295_);
lean_ctor_set(v___x_275_, 0, v_size_x27_293_);
v___x_307_ = v___x_275_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_size_x27_293_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_buckets_x27_295_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v___x_309_; lean_object* v_buckets_x27_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
lean_inc(v_bkt_290_);
v___x_309_ = lean_box(0);
v_buckets_x27_310_ = lean_array_uset(v_buckets_273_, v___x_289_, v___x_309_);
v___x_311_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__10___redArg(v_a_270_, v_b_271_, v_bkt_290_);
v___x_312_ = lean_array_uset(v_buckets_x27_310_, v___x_289_, v___x_311_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 1, v___x_312_);
v___x_314_ = v___x_275_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_size_272_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6___redArg(lean_object* v_a_317_, lean_object* v_x_318_){
_start:
{
if (lean_obj_tag(v_x_318_) == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_box(0);
return v___x_319_;
}
else
{
lean_object* v_key_320_; lean_object* v_value_321_; lean_object* v_tail_322_; uint8_t v___x_323_; 
v_key_320_ = lean_ctor_get(v_x_318_, 0);
v_value_321_ = lean_ctor_get(v_x_318_, 1);
v_tail_322_ = lean_ctor_get(v_x_318_, 2);
v___x_323_ = l_Lean_instBEqFVarId_beq(v_key_320_, v_a_317_);
if (v___x_323_ == 0)
{
v_x_318_ = v_tail_322_;
goto _start;
}
else
{
lean_object* v___x_325_; 
lean_inc(v_value_321_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v_value_321_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6___redArg___boxed(lean_object* v_a_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6___redArg(v_a_326_, v_x_327_);
lean_dec(v_x_327_);
lean_dec(v_a_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5___redArg(lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_buckets_331_; lean_object* v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v_fold_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_buckets_331_ = lean_ctor_get(v_m_329_, 1);
v___x_332_ = lean_array_get_size(v_buckets_331_);
v___x_333_ = l_Lean_instHashableFVarId_hash(v_a_330_);
v___x_334_ = 32ULL;
v___x_335_ = lean_uint64_shift_right(v___x_333_, v___x_334_);
v_fold_336_ = lean_uint64_xor(v___x_333_, v___x_335_);
v___x_337_ = 16ULL;
v___x_338_ = lean_uint64_shift_right(v_fold_336_, v___x_337_);
v___x_339_ = lean_uint64_xor(v_fold_336_, v___x_338_);
v___x_340_ = lean_uint64_to_usize(v___x_339_);
v___x_341_ = lean_usize_of_nat(v___x_332_);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_sub(v___x_341_, v___x_342_);
v___x_344_ = lean_usize_land(v___x_340_, v___x_343_);
v___x_345_ = lean_array_uget_borrowed(v_buckets_331_, v___x_344_);
v___x_346_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6___redArg(v_a_330_, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5___redArg___boxed(lean_object* v_m_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5___redArg(v_m_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_m_347_);
return v_res_349_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(lean_object* v_declName_350_, lean_object* v_as_351_, size_t v_i_352_, size_t v_stop_353_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = lean_usize_dec_eq(v_i_352_, v_stop_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v_toSignature_356_; lean_object* v_name_357_; uint8_t v___x_358_; 
v___x_355_ = lean_array_uget_borrowed(v_as_351_, v_i_352_);
v_toSignature_356_ = lean_ctor_get(v___x_355_, 0);
v_name_357_ = lean_ctor_get(v_toSignature_356_, 0);
v___x_358_ = lean_name_eq(v_name_357_, v_declName_350_);
if (v___x_358_ == 0)
{
size_t v___x_359_; size_t v___x_360_; 
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_add(v_i_352_, v___x_359_);
v_i_352_ = v___x_360_;
goto _start;
}
else
{
return v___x_358_;
}
}
else
{
uint8_t v___x_362_; 
v___x_362_ = 0;
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3___boxed(lean_object* v_declName_363_, lean_object* v_as_364_, lean_object* v_i_365_, lean_object* v_stop_366_){
_start:
{
size_t v_i_boxed_367_; size_t v_stop_boxed_368_; uint8_t v_res_369_; lean_object* v_r_370_; 
v_i_boxed_367_ = lean_unbox_usize(v_i_365_);
lean_dec(v_i_365_);
v_stop_boxed_368_ = lean_unbox_usize(v_stop_366_);
lean_dec(v_stop_366_);
v_res_369_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_363_, v_as_364_, v_i_boxed_367_, v_stop_boxed_368_);
lean_dec_ref(v_as_364_);
lean_dec(v_declName_363_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(lean_object* v_as_371_, size_t v_i_372_, size_t v_stop_373_){
_start:
{
uint8_t v___x_374_; 
v___x_374_ = lean_usize_dec_eq(v_i_372_, v_stop_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; uint8_t v___x_376_; uint8_t v___x_377_; 
v___x_375_ = lean_array_uget_borrowed(v_as_371_, v_i_372_);
v___x_376_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v___x_375_);
v___x_377_ = lean_bool_not(v___x_376_);
if (v___x_377_ == 0)
{
size_t v___x_378_; size_t v___x_379_; 
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_i_372_, v___x_378_);
v_i_372_ = v___x_379_;
goto _start;
}
else
{
return v___x_377_;
}
}
else
{
uint8_t v___x_381_; 
v___x_381_ = 0;
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object* v_as_382_, lean_object* v_i_383_, lean_object* v_stop_384_){
_start:
{
size_t v_i_boxed_385_; size_t v_stop_boxed_386_; uint8_t v_res_387_; lean_object* v_r_388_; 
v_i_boxed_385_ = lean_unbox_usize(v_i_383_);
lean_dec(v_i_383_);
v_stop_boxed_386_ = lean_unbox_usize(v_stop_384_);
lean_dec(v_stop_384_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_as_382_, v_i_boxed_385_, v_stop_boxed_386_);
lean_dec_ref(v_as_382_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0(void){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_cstr_to_nat("9223372036854775808");
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(lean_object* v_as_390_, size_t v_i_391_, size_t v_stop_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
uint8_t v___x_400_; 
v___x_400_ = lean_usize_dec_eq(v_i_391_, v_stop_392_);
if (v___x_400_ == 0)
{
uint8_t v___x_401_; uint8_t v_a_403_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_401_ = 1;
v___x_409_ = lean_array_uget_borrowed(v_as_390_, v_i_391_);
lean_inc(v___x_409_);
v___x_410_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_409_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; uint8_t v___x_412_; uint8_t v___x_413_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v___x_412_ = lean_unbox(v_a_411_);
lean_dec(v_a_411_);
v___x_413_ = lean_bool_not(v___x_412_);
v_a_403_ = v___x_413_;
goto v___jp_402_;
}
else
{
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_414_; uint8_t v___x_415_; 
v_a_414_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_410_, 1);
v___x_415_ = lean_unbox(v_a_414_);
lean_dec(v_a_414_);
v_a_403_ = v___x_415_;
goto v___jp_402_;
}
else
{
return v___x_410_;
}
}
v___jp_402_:
{
if (v_a_403_ == 0)
{
size_t v___x_404_; size_t v___x_405_; 
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_391_, v___x_404_);
v_i_391_ = v___x_405_;
goto _start;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_box(v___x_401_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
}
else
{
uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = 0;
v___x_417_ = lean_box(v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t v_isRoot_419_, lean_object* v_v_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
uint8_t v_____do__lift_429_; 
switch(lean_obj_tag(v_v_420_))
{
case 0:
{
lean_object* v_value_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_468_; 
v_value_433_ = lean_ctor_get(v_v_420_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_v_420_);
if (v_isSharedCheck_468_ == 0)
{
v___x_435_ = v_v_420_;
v_isShared_436_ = v_isSharedCheck_468_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_value_433_);
lean_dec(v_v_420_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_468_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
switch(lean_obj_tag(v_value_433_))
{
case 1:
{
lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_445_; 
lean_del_object(v___x_435_);
v_isSharedCheck_445_ = !lean_is_exclusive(v_value_433_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v_value_433_, 0);
lean_dec(v_unused_446_);
v___x_438_ = v_value_433_;
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
else
{
lean_dec(v_value_433_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = 1;
v___x_441_ = lean_box(v___x_440_);
if (v_isShared_439_ == 0)
{
lean_ctor_set_tag(v___x_438_, 0);
lean_ctor_set(v___x_438_, 0, v___x_441_);
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
case 0:
{
lean_object* v_val_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_462_; 
lean_del_object(v___x_435_);
v_val_447_ = lean_ctor_get(v_value_433_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_value_433_);
if (v_isSharedCheck_462_ == 0)
{
v___x_449_ = v_value_433_;
v_isShared_450_ = v_isSharedCheck_462_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_val_447_);
lean_dec(v_value_433_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_462_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
uint8_t v___x_451_; 
v___x_451_ = lean_bool_not(v_isRoot_419_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_452_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0, &l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0);
v___x_453_ = lean_nat_dec_le(v___x_452_, v_val_447_);
lean_dec(v_val_447_);
v___x_454_ = lean_box(v___x_453_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_454_);
v___x_456_ = v___x_449_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_460_; 
lean_dec(v_val_447_);
v___x_458_ = lean_box(v___x_451_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_458_);
v___x_460_ = v___x_449_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
default: 
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
lean_dec_ref(v_value_433_);
v___x_463_ = lean_bool_not(v_isRoot_419_);
v___x_464_ = lean_box(v___x_463_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_464_);
v___x_466_ = v___x_435_;
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
}
}
}
case 1:
{
uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_bool_not(v_isRoot_419_);
v___x_470_ = lean_box(v___x_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
case 2:
{
lean_object* v_struct_472_; lean_object* v___x_473_; 
v_struct_472_ = lean_ctor_get(v_v_420_, 2);
lean_inc(v_struct_472_);
lean_dec_ref_known(v_v_420_, 3);
v___x_473_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_struct_472_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
return v___x_473_;
}
case 3:
{
lean_object* v_declName_474_; lean_object* v_args_475_; lean_object* v_sccDecls_476_; lean_object* v___x_477_; uint8_t v___y_479_; lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; uint8_t v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; uint8_t v___y_523_; uint8_t v___y_524_; uint8_t v___y_529_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_declName_474_ = lean_ctor_get(v_v_420_, 0);
lean_inc(v_declName_474_);
v_args_475_ = lean_ctor_get(v_v_420_, 2);
lean_inc_ref(v_args_475_);
lean_dec_ref_known(v_v_420_, 3);
v_sccDecls_476_ = lean_ctor_get(v_a_421_, 1);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_array_get_size(v_sccDecls_476_);
v___x_555_ = lean_nat_dec_lt(v___x_477_, v___x_554_);
if (v___x_555_ == 0)
{
v___y_529_ = v___x_555_;
goto v___jp_528_;
}
else
{
if (v___x_555_ == 0)
{
v___y_529_ = v___x_555_;
goto v___jp_528_;
}
else
{
size_t v___x_556_; size_t v___x_557_; uint8_t v___x_558_; 
v___x_556_ = ((size_t)0ULL);
v___x_557_ = lean_usize_of_nat(v___x_554_);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_474_, v_sccDecls_476_, v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
v___y_529_ = v___x_558_;
goto v___jp_528_;
}
else
{
uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec_ref(v_args_475_);
lean_dec(v_declName_474_);
v___x_559_ = 0;
v___x_560_ = lean_box(v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
}
v___jp_478_:
{
lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_486_ = lean_array_get_size(v_args_475_);
v___x_487_ = lean_nat_dec_lt(v___x_477_, v___x_486_);
if (v___x_487_ == 0)
{
lean_dec_ref(v_args_475_);
v_____do__lift_429_ = v___y_479_;
goto v___jp_428_;
}
else
{
if (v___x_487_ == 0)
{
lean_dec_ref(v_args_475_);
v_____do__lift_429_ = v___y_479_;
goto v___jp_428_;
}
else
{
size_t v___x_488_; size_t v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((size_t)0ULL);
v___x_489_ = lean_usize_of_nat(v___x_486_);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v_args_475_, v___x_488_, v___x_489_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec_ref(v_args_475_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; uint8_t v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = lean_unbox(v_a_491_);
lean_dec(v_a_491_);
v_____do__lift_429_ = v___x_492_;
goto v___jp_428_;
}
else
{
return v___x_490_;
}
}
}
}
v___jp_493_:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_474_, v___y_500_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_513_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_513_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_513_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_513_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
if (lean_obj_tag(v_a_502_) == 1)
{
lean_object* v_val_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_val_506_ = lean_ctor_get(v_a_502_, 0);
lean_inc(v_val_506_);
lean_dec_ref_known(v_a_502_, 1);
v___x_507_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_506_);
lean_dec(v_val_506_);
v___x_508_ = lean_nat_dec_eq(v___x_507_, v___x_477_);
lean_dec(v___x_507_);
if (v___x_508_ == 0)
{
lean_del_object(v___x_504_);
v___y_479_ = v___y_494_;
v___y_480_ = v___y_495_;
v___y_481_ = v___y_496_;
v___y_482_ = v___y_497_;
v___y_483_ = v___y_498_;
v___y_484_ = v___y_499_;
v___y_485_ = v___y_500_;
goto v___jp_478_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_511_; 
lean_dec_ref(v_args_475_);
v___x_509_ = lean_box(v___y_494_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_509_);
v___x_511_ = v___x_504_;
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
lean_del_object(v___x_504_);
lean_dec(v_a_502_);
v___y_479_ = v___y_494_;
v___y_480_ = v___y_495_;
v___y_481_ = v___y_496_;
v___y_482_ = v___y_497_;
v___y_483_ = v___y_498_;
v___y_484_ = v___y_499_;
v___y_485_ = v___y_500_;
goto v___jp_478_;
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v_args_475_);
v_a_514_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_501_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_501_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
v___jp_522_:
{
uint8_t v___x_525_; 
v___x_525_ = lean_bool_not(v___y_524_);
if (v___x_525_ == 0)
{
v___y_494_ = v___y_523_;
v___y_495_ = v_a_421_;
v___y_496_ = v_a_422_;
v___y_497_ = v_a_423_;
v___y_498_ = v_a_424_;
v___y_499_ = v_a_425_;
v___y_500_ = v_a_426_;
goto v___jp_493_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec_ref(v_args_475_);
lean_dec(v_declName_474_);
v___x_526_ = lean_box(v___y_523_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
v___jp_528_:
{
lean_object* v___x_530_; lean_object* v_env_531_; uint8_t v___x_532_; 
v___x_530_ = lean_st_ref_get(v_a_426_);
v_env_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_env_531_);
lean_dec(v___x_530_);
lean_inc(v_declName_474_);
v___x_532_ = l_Lean_hasNeverExtractAttribute(v_env_531_, v_declName_474_);
if (v___x_532_ == 0)
{
if (v_isRoot_419_ == 0)
{
lean_dec(v_declName_474_);
v___y_479_ = v___x_532_;
v___y_480_ = v_a_421_;
v___y_481_ = v_a_422_;
v___y_482_ = v_a_423_;
v___y_483_ = v_a_424_;
v___y_484_ = v_a_425_;
v___y_485_ = v_a_426_;
goto v___jp_478_;
}
else
{
lean_object* v___x_533_; lean_object* v_env_534_; lean_object* v___x_535_; 
v___x_533_ = lean_st_ref_get(v_a_426_);
v_env_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc_ref(v_env_534_);
lean_dec(v___x_533_);
lean_inc(v_declName_474_);
v___x_535_ = l_Lean_Environment_find_x3f(v_env_534_, v_declName_474_, v___x_532_);
if (lean_obj_tag(v___x_535_) == 1)
{
lean_object* v_val_536_; 
v_val_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_val_536_);
lean_dec_ref_known(v___x_535_, 1);
switch(lean_obj_tag(v_val_536_))
{
case 1:
{
lean_object* v_val_537_; lean_object* v_toConstantVal_538_; lean_object* v_type_539_; uint8_t v___x_540_; 
v_val_537_ = lean_ctor_get(v_val_536_, 0);
lean_inc_ref(v_val_537_);
lean_dec_ref_known(v_val_536_, 1);
v_toConstantVal_538_ = lean_ctor_get(v_val_537_, 0);
lean_inc_ref(v_toConstantVal_538_);
lean_dec_ref(v_val_537_);
v_type_539_ = lean_ctor_get(v_toConstantVal_538_, 2);
lean_inc_ref(v_type_539_);
lean_dec_ref(v_toConstantVal_538_);
v___x_540_ = l_Lean_Expr_isForall(v_type_539_);
lean_dec_ref(v_type_539_);
v___y_523_ = v___x_532_;
v___y_524_ = v___x_540_;
goto v___jp_522_;
}
case 6:
{
lean_object* v___x_541_; uint8_t v___x_542_; 
lean_dec_ref_known(v_val_536_, 1);
v___x_541_ = lean_array_get_size(v_args_475_);
v___x_542_ = lean_nat_dec_lt(v___x_477_, v___x_541_);
if (v___x_542_ == 0)
{
uint8_t v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_bool_not(v___x_532_);
v___x_544_ = lean_bool_not(v___x_543_);
v___y_523_ = v___x_532_;
v___y_524_ = v___x_544_;
goto v___jp_522_;
}
else
{
if (v___x_542_ == 0)
{
uint8_t v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_bool_not(v___x_532_);
v___x_546_ = lean_bool_not(v___x_545_);
v___y_523_ = v___x_532_;
v___y_524_ = v___x_546_;
goto v___jp_522_;
}
else
{
size_t v___x_547_; size_t v___x_548_; uint8_t v___x_549_; uint8_t v___x_550_; uint8_t v___x_551_; 
v___x_547_ = ((size_t)0ULL);
v___x_548_ = lean_usize_of_nat(v___x_541_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_args_475_, v___x_547_, v___x_548_);
v___x_550_ = lean_bool_not(v___x_549_);
v___x_551_ = lean_bool_not(v___x_550_);
v___y_523_ = v___x_532_;
v___y_524_ = v___x_551_;
goto v___jp_522_;
}
}
}
default: 
{
lean_dec(v_val_536_);
v___y_523_ = v___x_532_;
v___y_524_ = v_isRoot_419_;
goto v___jp_522_;
}
}
}
else
{
lean_dec(v___x_535_);
v___y_494_ = v___x_532_;
v___y_495_ = v_a_421_;
v___y_496_ = v_a_422_;
v___y_497_ = v_a_423_;
v___y_498_ = v_a_424_;
v___y_499_ = v_a_425_;
v___y_500_ = v_a_426_;
goto v___jp_493_;
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec_ref(v_args_475_);
lean_dec(v_declName_474_);
v___x_552_ = lean_box(v___y_529_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
}
default: 
{
lean_object* v_fvarId_562_; lean_object* v_args_563_; lean_object* v___x_564_; 
v_fvarId_562_ = lean_ctor_get(v_v_420_, 0);
lean_inc(v_fvarId_562_);
v_args_563_ = lean_ctor_get(v_v_420_, 1);
lean_inc_ref(v_args_563_);
lean_dec_ref_known(v_v_420_, 2);
v___x_564_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_562_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___y_567_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref_known(v___x_564_, 1);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_array_get_size(v_args_563_);
v___x_579_ = lean_nat_dec_lt(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
lean_dec_ref(v_args_563_);
v___x_580_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_579_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
v___y_567_ = v___x_580_;
goto v___jp_566_;
}
else
{
if (v___x_579_ == 0)
{
lean_object* v___x_581_; 
lean_dec_ref(v_args_563_);
v___x_581_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_579_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
v___y_567_ = v___x_581_;
goto v___jp_566_;
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_578_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v_args_563_, v___x_582_, v___x_583_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec_ref(v_args_563_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; uint8_t v___x_586_; lean_object* v___x_587_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = lean_unbox(v_a_585_);
lean_dec(v_a_585_);
v___x_587_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_586_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
v___y_567_ = v___x_587_;
goto v___jp_566_;
}
else
{
v___y_567_ = v___x_584_;
goto v___jp_566_;
}
}
}
v___jp_566_:
{
if (lean_obj_tag(v___y_567_) == 0)
{
uint8_t v___x_568_; 
v___x_568_ = lean_unbox(v_a_565_);
if (v___x_568_ == 0)
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_isSharedCheck_575_ = !lean_is_exclusive(v___y_567_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v___y_567_, 0);
lean_dec(v_unused_576_);
v___x_570_ = v___y_567_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_dec(v___y_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v_a_565_);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_565_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_dec(v_a_565_);
return v___y_567_;
}
}
else
{
lean_dec(v_a_565_);
return v___y_567_;
}
}
}
else
{
lean_dec_ref(v_args_563_);
return v___x_564_;
}
}
}
v___jp_428_:
{
uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_bool_not(v_____do__lift_429_);
v___x_431_ = lean_box(v___x_430_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(lean_object* v_fvarId_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
uint8_t v___x_596_; lean_object* v___x_597_; 
v___x_596_ = 0;
v___x_597_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_596_, v_fvarId_588_, v_a_592_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_611_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_611_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_611_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_611_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
if (lean_obj_tag(v_a_598_) == 1)
{
lean_object* v_val_602_; lean_object* v_value_603_; uint8_t v___x_604_; lean_object* v___x_605_; 
lean_del_object(v___x_600_);
v_val_602_ = lean_ctor_get(v_a_598_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v_a_598_, 1);
v_value_603_ = lean_ctor_get(v_val_602_, 3);
lean_inc(v_value_603_);
lean_dec(v_val_602_);
v___x_604_ = 0;
v___x_605_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_604_, v_value_603_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
return v___x_605_;
}
else
{
uint8_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
lean_dec(v_a_598_);
v___x_606_ = 0;
v___x_607_ = lean_box(v___x_606_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_607_);
v___x_609_ = v___x_600_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
v_a_612_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_597_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_597_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object* v_fvarId_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_628_; lean_object* v_fvarDecisionCache_629_; lean_object* v___x_630_; 
v___x_628_ = lean_st_ref_get(v_a_622_);
v_fvarDecisionCache_629_ = lean_ctor_get(v___x_628_, 1);
lean_inc_ref(v_fvarDecisionCache_629_);
lean_dec(v___x_628_);
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5___redArg(v_fvarDecisionCache_629_, v_fvarId_620_);
lean_dec_ref(v_fvarDecisionCache_629_);
if (lean_obj_tag(v___x_630_) == 1)
{
lean_object* v_val_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_fvarId_620_);
v_val_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_val_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set_tag(v___x_633_, 0);
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_val_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
else
{
lean_object* v___x_639_; 
lean_dec(v___x_630_);
v___x_639_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_659_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_659_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_659_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_659_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v_decls_645_; lean_object* v_fvarDecisionCache_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_658_; 
v___x_644_ = lean_st_ref_take(v_a_622_);
v_decls_645_ = lean_ctor_get(v___x_644_, 0);
v_fvarDecisionCache_646_ = lean_ctor_get(v___x_644_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_658_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_fvarDecisionCache_646_);
lean_inc(v_decls_645_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_658_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v___x_652_; 
lean_inc(v_a_640_);
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_fvarDecisionCache_646_, v_fvarId_620_, v_a_640_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 1, v___x_650_);
v___x_652_ = v___x_648_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_decls_645_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_657_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_st_ref_set(v_a_622_, v___x_652_);
if (v_isShared_643_ == 0)
{
v___x_655_ = v___x_642_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_640_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_620_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object* v_arg_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
if (lean_obj_tag(v_arg_660_) == 1)
{
lean_object* v_fvarId_668_; lean_object* v___x_669_; 
v_fvarId_668_ = lean_ctor_get(v_arg_660_, 0);
lean_inc(v_fvarId_668_);
lean_dec_ref_known(v_arg_660_, 1);
v___x_669_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_668_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
return v___x_669_;
}
else
{
uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec(v_arg_660_);
v___x_670_ = 1;
v___x_671_ = lean_box(v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object* v_arg_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v_arg_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(lean_object* v_fvarId_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_fvarId_682_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object* v_fvarId_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(v_fvarId_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object* v_as_700_, lean_object* v_i_701_, lean_object* v_stop_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
size_t v_i_boxed_710_; size_t v_stop_boxed_711_; lean_object* v_res_712_; 
v_i_boxed_710_ = lean_unbox_usize(v_i_701_);
lean_dec(v_i_701_);
v_stop_boxed_711_ = lean_unbox_usize(v_stop_702_);
lean_dec(v_stop_702_);
v_res_712_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v_as_700_, v_i_boxed_710_, v_stop_boxed_711_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec_ref(v_as_700_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object* v_isRoot_713_, lean_object* v_v_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
uint8_t v_isRoot_boxed_722_; lean_object* v_res_723_; 
v_isRoot_boxed_722_ = lean_unbox(v_isRoot_713_);
v_res_723_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v_isRoot_boxed_722_, v_v_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5(lean_object* v_00_u03b2_724_, lean_object* v_m_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5___redArg(v_m_725_, v_a_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5___boxed(lean_object* v_00_u03b2_728_, lean_object* v_m_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5(v_00_u03b2_728_, v_m_729_, v_a_730_);
lean_dec(v_a_730_);
lean_dec_ref(v_m_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(lean_object* v_00_u03b2_732_, lean_object* v_m_733_, lean_object* v_a_734_, lean_object* v_b_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_733_, v_a_734_, v_b_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6(lean_object* v_00_u03b2_737_, lean_object* v_a_738_, lean_object* v_x_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6___redArg(v_a_738_, v_x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6___boxed(lean_object* v_00_u03b2_741_, lean_object* v_a_742_, lean_object* v_x_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__5_spec__6(v_00_u03b2_741_, v_a_742_, v_x_743_);
lean_dec(v_x_743_);
lean_dec(v_a_742_);
return v_res_744_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8(lean_object* v_00_u03b2_745_, lean_object* v_a_746_, lean_object* v_x_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8___redArg(v_a_746_, v_x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8___boxed(lean_object* v_00_u03b2_749_, lean_object* v_a_750_, lean_object* v_x_751_){
_start:
{
uint8_t v_res_752_; lean_object* v_r_753_; 
v_res_752_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__8(v_00_u03b2_749_, v_a_750_, v_x_751_);
lean_dec(v_x_751_);
lean_dec(v_a_750_);
v_r_753_ = lean_box(v_res_752_);
return v_r_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9(lean_object* v_00_u03b2_754_, lean_object* v_data_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9___redArg(v_data_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__10(lean_object* v_00_u03b2_757_, lean_object* v_a_758_, lean_object* v_b_759_, lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__10___redArg(v_a_758_, v_b_759_, v_x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10(lean_object* v_00_u03b2_762_, lean_object* v_i_763_, lean_object* v_source_764_, lean_object* v_target_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10___redArg(v_i_763_, v_source_764_, v_target_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10_spec__11(lean_object* v_00_u03b2_767_, lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__9_spec__10_spec__11___redArg(v_x_768_, v_x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(lean_object* v_prevArrayId_776_, lean_object* v_decl_777_, lean_object* v_k_778_, lean_object* v_illegalSet_779_, lean_object* v_size_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_decl_792_; lean_object* v_k_793_; lean_object* v_illegalSet_794_; lean_object* v_zero_802_; uint8_t v_isZero_803_; 
v_zero_802_ = lean_unsigned_to_nat(0u);
v_isZero_803_ = lean_nat_dec_eq(v_size_780_, v_zero_802_);
if (v_isZero_803_ == 1)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
lean_dec(v_prevArrayId_776_);
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
else
{
lean_object* v_value_806_; 
v_value_806_ = lean_ctor_get(v_decl_777_, 3);
if (lean_obj_tag(v_value_806_) == 3)
{
lean_object* v_declName_807_; 
v_declName_807_ = lean_ctor_get(v_value_806_, 0);
if (lean_obj_tag(v_declName_807_) == 1)
{
lean_object* v_pre_808_; 
v_pre_808_ = lean_ctor_get(v_declName_807_, 0);
if (lean_obj_tag(v_pre_808_) == 1)
{
lean_object* v_pre_809_; 
v_pre_809_ = lean_ctor_get(v_pre_808_, 0);
if (lean_obj_tag(v_pre_809_) == 0)
{
lean_object* v_fvarId_810_; lean_object* v_args_811_; lean_object* v_str_812_; lean_object* v_str_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_fvarId_810_ = lean_ctor_get(v_decl_777_, 0);
v_args_811_ = lean_ctor_get(v_value_806_, 2);
v_str_812_ = lean_ctor_get(v_declName_807_, 1);
v_str_813_ = lean_ctor_get(v_pre_808_, 1);
v___x_814_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_815_ = lean_string_dec_eq(v_str_813_, v___x_814_);
if (v___x_815_ == 0)
{
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
lean_dec(v_prevArrayId_776_);
goto v___jp_788_;
}
else
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_817_ = lean_string_dec_eq(v_str_812_, v___x_816_);
if (v___x_817_ == 0)
{
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
lean_dec(v_prevArrayId_776_);
goto v___jp_788_;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_818_ = lean_array_get_size(v_args_811_);
v___x_819_ = lean_unsigned_to_nat(3u);
v___x_820_ = lean_nat_dec_eq(v___x_818_, v___x_819_);
if (v___x_820_ == 0)
{
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
lean_dec(v_prevArrayId_776_);
goto v___jp_788_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_array_fget(v_args_811_, v___x_821_);
if (lean_obj_tag(v___x_822_) == 1)
{
lean_object* v_fvarId_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_945_; 
v_fvarId_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_945_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_945_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_fvarId_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_945_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint8_t v___x_827_; uint8_t v___x_828_; 
v___x_827_ = l_Lean_instBEqFVarId_beq(v_fvarId_823_, v_prevArrayId_776_);
lean_dec(v_prevArrayId_776_);
lean_dec(v_fvarId_823_);
v___x_828_ = lean_bool_not(v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_del_object(v___x_825_);
v___x_829_ = lean_unsigned_to_nat(2u);
v___x_830_ = lean_array_fget_borrowed(v_args_811_, v___x_829_);
lean_inc(v___x_830_);
v___x_831_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(v___x_830_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_932_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_932_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_932_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_932_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
uint8_t v___x_836_; uint8_t v___x_837_; 
v___x_836_ = lean_unbox(v_a_832_);
lean_dec(v_a_832_);
v___x_837_ = lean_bool_not(v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v_n_838_; uint8_t v___x_839_; uint8_t v___x_840_; 
v_n_838_ = lean_nat_sub(v_size_780_, v___x_821_);
lean_dec(v_size_780_);
v___x_839_ = lean_nat_dec_eq(v_n_838_, v_zero_802_);
v___x_840_ = lean_bool_not(v___x_839_);
if (v___x_840_ == 0)
{
lean_dec(v_n_838_);
lean_del_object(v___x_834_);
if (lean_obj_tag(v_k_778_) == 0)
{
lean_object* v_decl_841_; lean_object* v_value_842_; 
v_decl_841_ = lean_ctor_get(v_k_778_, 0);
lean_inc_ref(v_decl_841_);
v_value_842_ = lean_ctor_get(v_decl_841_, 3);
lean_inc(v_value_842_);
if (lean_obj_tag(v_value_842_) == 3)
{
lean_object* v_declName_843_; 
v_declName_843_ = lean_ctor_get(v_value_842_, 0);
lean_inc(v_declName_843_);
if (lean_obj_tag(v_declName_843_) == 1)
{
lean_object* v_pre_844_; 
v_pre_844_ = lean_ctor_get(v_declName_843_, 0);
lean_inc(v_pre_844_);
if (lean_obj_tag(v_pre_844_) == 1)
{
lean_object* v_pre_845_; 
v_pre_845_ = lean_ctor_get(v_pre_844_, 0);
lean_inc(v_pre_845_);
if (lean_obj_tag(v_pre_845_) == 0)
{
lean_object* v_k_846_; lean_object* v_fvarId_847_; lean_object* v_binderName_848_; lean_object* v_type_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_918_; 
v_k_846_ = lean_ctor_get(v_k_778_, 1);
v_fvarId_847_ = lean_ctor_get(v_decl_841_, 0);
v_binderName_848_ = lean_ctor_get(v_decl_841_, 1);
v_type_849_ = lean_ctor_get(v_decl_841_, 2);
v_isSharedCheck_918_ = !lean_is_exclusive(v_decl_841_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v_decl_841_, 3);
lean_dec(v_unused_919_);
v___x_851_ = v_decl_841_;
v_isShared_852_ = v_isSharedCheck_918_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_type_849_);
lean_inc(v_binderName_848_);
lean_inc(v_fvarId_847_);
lean_dec(v_decl_841_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_918_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_us_853_; lean_object* v_args_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_916_; 
v_us_853_ = lean_ctor_get(v_value_842_, 1);
v_args_854_ = lean_ctor_get(v_value_842_, 2);
v_isSharedCheck_916_ = !lean_is_exclusive(v_value_842_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v_value_842_, 0);
lean_dec(v_unused_917_);
v___x_856_ = v_value_842_;
v_isShared_857_ = v_isSharedCheck_916_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_args_854_);
lean_inc(v_us_853_);
lean_dec(v_value_842_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_916_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_str_858_; lean_object* v_str_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_str_858_ = lean_ctor_get(v_declName_843_, 1);
lean_inc_ref(v_str_858_);
lean_dec_ref_known(v_declName_843_, 2);
v_str_859_ = lean_ctor_get(v_pre_844_, 1);
lean_inc_ref(v_str_859_);
lean_dec_ref_known(v_pre_844_, 2);
v___x_860_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2));
v___x_861_ = lean_string_dec_eq(v_str_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3));
v___x_863_ = lean_string_dec_eq(v_str_859_, v___x_862_);
lean_dec_ref(v_str_859_);
if (v___x_863_ == 0)
{
lean_dec_ref(v_str_858_);
lean_del_object(v___x_856_);
lean_dec_ref(v_args_854_);
lean_dec(v_us_853_);
lean_del_object(v___x_851_);
lean_dec_ref(v_type_849_);
lean_dec(v_binderName_848_);
lean_dec(v_fvarId_847_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
else
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_865_ = lean_string_dec_eq(v_str_858_, v___x_864_);
lean_dec_ref(v_str_858_);
if (v___x_865_ == 0)
{
lean_del_object(v___x_856_);
lean_dec_ref(v_args_854_);
lean_dec(v_us_853_);
lean_del_object(v___x_851_);
lean_dec_ref(v_type_849_);
lean_dec(v_binderName_848_);
lean_dec(v_fvarId_847_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
else
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = lean_array_get_size(v_args_854_);
v___x_867_ = lean_nat_dec_eq(v___x_866_, v___x_821_);
if (v___x_867_ == 0)
{
lean_del_object(v___x_856_);
lean_dec_ref(v_args_854_);
lean_dec(v_us_853_);
lean_del_object(v___x_851_);
lean_dec_ref(v_type_849_);
lean_dec(v_binderName_848_);
lean_dec(v_fvarId_847_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
else
{
lean_object* v___x_868_; 
v___x_868_ = lean_array_fget(v_args_854_, v_zero_802_);
lean_dec_ref(v_args_854_);
if (lean_obj_tag(v___x_868_) == 1)
{
lean_object* v_fvarId_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_889_; 
v_fvarId_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_889_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_889_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_fvarId_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_889_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
uint8_t v___x_873_; uint8_t v___x_874_; 
v___x_873_ = l_Lean_instBEqFVarId_beq(v_fvarId_869_, v_fvarId_810_);
v___x_874_ = lean_bool_not(v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
lean_inc_ref(v_k_846_);
lean_inc(v_fvarId_810_);
lean_dec_ref_known(v_k_778_, 2);
lean_dec_ref(v_decl_777_);
v___x_875_ = l_Lean_Name_str___override(v_pre_845_, v___x_862_);
v___x_876_ = l_Lean_Name_str___override(v___x_875_, v___x_864_);
if (v_isShared_872_ == 0)
{
v___x_878_ = v___x_871_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_fvarId_869_);
v___x_878_ = v_reuseFailAlloc_888_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_879_ = lean_mk_empty_array_with_capacity(v___x_821_);
v___x_880_ = lean_array_push(v___x_879_, v___x_878_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 2, v___x_880_);
lean_ctor_set(v___x_856_, 0, v___x_876_);
v___x_882_ = v___x_856_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_us_853_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v___x_880_);
v___x_882_ = v_reuseFailAlloc_887_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 3, v___x_882_);
v___x_884_ = v___x_851_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_fvarId_847_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_binderName_848_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_type_849_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v___x_882_);
v___x_884_ = v_reuseFailAlloc_886_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_FVarIdSet_insert(v_illegalSet_779_, v_fvarId_810_);
v_decl_792_ = v___x_884_;
v_k_793_ = v_k_846_;
v_illegalSet_794_ = v___x_885_;
goto v___jp_791_;
}
}
}
}
else
{
lean_del_object(v___x_871_);
lean_dec(v_fvarId_869_);
lean_del_object(v___x_856_);
lean_dec(v_us_853_);
lean_del_object(v___x_851_);
lean_dec_ref(v_type_849_);
lean_dec(v_binderName_848_);
lean_dec(v_fvarId_847_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
}
}
else
{
lean_dec(v___x_868_);
lean_del_object(v___x_856_);
lean_dec(v_us_853_);
lean_del_object(v___x_851_);
lean_dec_ref(v_type_849_);
lean_dec(v_binderName_848_);
lean_dec(v_fvarId_847_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
}
}
}
}
else
{
lean_object* v___x_890_; uint8_t v___x_891_; 
lean_dec_ref(v_str_859_);
v___x_890_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4));
v___x_891_ = lean_string_dec_eq(v_str_858_, v___x_890_);
lean_dec_ref(v_str_858_);
if (v___x_891_ == 0)
{
lean_del_object(v___x_856_);
lean_dec_ref(v_args_854_);
lean_dec(v_us_853_);
lean_del_object(v___x_851_);
lean_dec_ref(v_type_849_);
lean_dec(v_binderName_848_);
lean_dec(v_fvarId_847_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
else
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_array_get_size(v_args_854_);
v___x_893_ = lean_nat_dec_eq(v___x_892_, v___x_821_);
if (v___x_893_ == 0)
{
lean_del_object(v___x_856_);
lean_dec_ref(v_args_854_);
lean_dec(v_us_853_);
lean_del_object(v___x_851_);
lean_dec_ref(v_type_849_);
lean_dec(v_binderName_848_);
lean_dec(v_fvarId_847_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = lean_array_fget(v_args_854_, v_zero_802_);
lean_dec_ref(v_args_854_);
if (lean_obj_tag(v___x_894_) == 1)
{
lean_object* v_fvarId_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_915_; 
v_fvarId_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_915_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_915_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_fvarId_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_915_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
uint8_t v___x_899_; uint8_t v___x_900_; 
v___x_899_ = l_Lean_instBEqFVarId_beq(v_fvarId_895_, v_fvarId_810_);
v___x_900_ = lean_bool_not(v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
lean_inc_ref(v_k_846_);
lean_inc(v_fvarId_810_);
lean_dec_ref_known(v_k_778_, 2);
lean_dec_ref(v_decl_777_);
v___x_901_ = l_Lean_Name_str___override(v_pre_845_, v___x_860_);
v___x_902_ = l_Lean_Name_str___override(v___x_901_, v___x_890_);
if (v_isShared_898_ == 0)
{
v___x_904_ = v___x_897_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_fvarId_895_);
v___x_904_ = v_reuseFailAlloc_914_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_905_ = lean_mk_empty_array_with_capacity(v___x_821_);
v___x_906_ = lean_array_push(v___x_905_, v___x_904_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 2, v___x_906_);
lean_ctor_set(v___x_856_, 0, v___x_902_);
v___x_908_ = v___x_856_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_us_853_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v___x_906_);
v___x_908_ = v_reuseFailAlloc_913_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 3, v___x_908_);
v___x_910_ = v___x_851_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_fvarId_847_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_binderName_848_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_type_849_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v___x_908_);
v___x_910_ = v_reuseFailAlloc_912_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_FVarIdSet_insert(v_illegalSet_779_, v_fvarId_810_);
v_decl_792_ = v___x_910_;
v_k_793_ = v_k_846_;
v_illegalSet_794_ = v___x_911_;
goto v___jp_791_;
}
}
}
}
else
{
lean_del_object(v___x_897_);
lean_dec(v_fvarId_895_);
lean_del_object(v___x_856_);
lean_dec(v_us_853_);
lean_del_object(v___x_851_);
lean_dec_ref(v_type_849_);
lean_dec(v_binderName_848_);
lean_dec(v_fvarId_847_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
}
}
else
{
lean_dec(v___x_894_);
lean_del_object(v___x_856_);
lean_dec(v_us_853_);
lean_del_object(v___x_851_);
lean_dec_ref(v_type_849_);
lean_dec(v_binderName_848_);
lean_dec(v_fvarId_847_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_844_, 2);
lean_dec(v_pre_845_);
lean_dec_ref_known(v_declName_843_, 2);
lean_dec_ref_known(v_value_842_, 3);
lean_dec_ref(v_decl_841_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
}
else
{
lean_dec_ref_known(v_declName_843_, 2);
lean_dec(v_pre_844_);
lean_dec_ref_known(v_value_842_, 3);
lean_dec_ref(v_decl_841_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
}
else
{
lean_dec(v_declName_843_);
lean_dec_ref_known(v_value_842_, 3);
lean_dec_ref(v_decl_841_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
}
else
{
lean_dec(v_value_842_);
lean_dec_ref(v_decl_841_);
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
}
else
{
v_decl_792_ = v_decl_777_;
v_k_793_ = v_k_778_;
v_illegalSet_794_ = v_illegalSet_779_;
goto v___jp_791_;
}
}
else
{
lean_inc(v_fvarId_810_);
lean_dec_ref(v_decl_777_);
if (lean_obj_tag(v_k_778_) == 0)
{
lean_object* v_decl_920_; lean_object* v_k_921_; lean_object* v___x_922_; 
lean_del_object(v___x_834_);
v_decl_920_ = lean_ctor_get(v_k_778_, 0);
lean_inc_ref(v_decl_920_);
v_k_921_ = lean_ctor_get(v_k_778_, 1);
lean_inc_ref(v_k_921_);
lean_dec_ref_known(v_k_778_, 2);
lean_inc(v_fvarId_810_);
v___x_922_ = l_Lean_FVarIdSet_insert(v_illegalSet_779_, v_fvarId_810_);
v_prevArrayId_776_ = v_fvarId_810_;
v_decl_777_ = v_decl_920_;
v_k_778_ = v_k_921_;
v_illegalSet_779_ = v___x_922_;
v_size_780_ = v_n_838_;
goto _start;
}
else
{
lean_object* v___x_924_; lean_object* v___x_926_; 
lean_dec(v_n_838_);
lean_dec(v_fvarId_810_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
v___x_924_ = lean_box(0);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_924_);
v___x_926_ = v___x_834_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_930_; 
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
v___x_928_ = lean_box(0);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_928_);
v___x_930_ = v___x_834_;
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
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
v_a_933_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_831_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_831_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
v___x_941_ = lean_box(0);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 0);
lean_ctor_set(v___x_825_, 0, v___x_941_);
v___x_943_ = v___x_825_;
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
else
{
lean_dec(v___x_822_);
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
lean_dec(v_prevArrayId_776_);
goto v___jp_788_;
}
}
}
}
}
else
{
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
lean_dec(v_prevArrayId_776_);
goto v___jp_788_;
}
}
else
{
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
lean_dec(v_prevArrayId_776_);
goto v___jp_788_;
}
}
else
{
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
lean_dec(v_prevArrayId_776_);
goto v___jp_788_;
}
}
else
{
lean_dec(v_size_780_);
lean_dec(v_illegalSet_779_);
lean_dec_ref(v_k_778_);
lean_dec_ref(v_decl_777_);
lean_dec(v_prevArrayId_776_);
goto v___jp_788_;
}
}
v___jp_788_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_box(0);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
v___jp_791_:
{
uint8_t v___x_795_; uint8_t v___x_796_; 
v___x_795_ = 0;
v___x_796_ = l_Lean_Compiler_LCNF_Code_dependsOn(v___x_795_, v_k_793_, v_illegalSet_794_);
lean_dec(v_illegalSet_794_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_decl_792_);
lean_ctor_set(v___x_797_, 1, v_k_793_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref(v_k_793_);
lean_dec_ref(v_decl_792_);
v___x_800_ = lean_box(0);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___boxed(lean_object* v_prevArrayId_946_, lean_object* v_decl_947_, lean_object* v_k_948_, lean_object* v_illegalSet_949_, lean_object* v_size_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_prevArrayId_946_, v_decl_947_, v_k_948_, v_illegalSet_949_, v_size_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(lean_object* v_decl_961_, lean_object* v_k_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_value_979_; 
v_value_979_ = lean_ctor_get(v_decl_961_, 3);
if (lean_obj_tag(v_value_979_) == 3)
{
lean_object* v_declName_980_; 
v_declName_980_ = lean_ctor_get(v_value_979_, 0);
if (lean_obj_tag(v_declName_980_) == 1)
{
lean_object* v_pre_981_; 
v_pre_981_ = lean_ctor_get(v_declName_980_, 0);
if (lean_obj_tag(v_pre_981_) == 1)
{
lean_object* v_pre_982_; 
v_pre_982_ = lean_ctor_get(v_pre_981_, 0);
if (lean_obj_tag(v_pre_982_) == 0)
{
lean_object* v_args_983_; lean_object* v_str_984_; lean_object* v_str_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_args_983_ = lean_ctor_get(v_value_979_, 2);
v_str_984_ = lean_ctor_get(v_declName_980_, 1);
v_str_985_ = lean_ctor_get(v_pre_981_, 1);
v___x_986_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_987_ = lean_string_dec_eq(v_str_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_976_;
}
else
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1));
v___x_989_ = lean_string_dec_eq(v_str_984_, v___x_988_);
if (v___x_989_ == 0)
{
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_976_;
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_990_ = lean_array_get_size(v_args_983_);
v___x_991_ = lean_unsigned_to_nat(3u);
v___x_992_ = lean_nat_dec_eq(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_976_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_unsigned_to_nat(1u);
v___x_994_ = lean_array_fget_borrowed(v_args_983_, v___x_993_);
if (lean_obj_tag(v___x_994_) == 1)
{
lean_object* v_fvarId_995_; uint8_t v___x_996_; lean_object* v___x_997_; 
v_fvarId_995_ = lean_ctor_get(v___x_994_, 0);
v___x_996_ = 0;
v___x_997_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_996_, v_fvarId_995_, v_a_966_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1053_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1053_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1053_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
if (lean_obj_tag(v_a_998_) == 1)
{
lean_object* v_val_1002_; lean_object* v_value_1003_; 
lean_del_object(v___x_1000_);
v_val_1002_ = lean_ctor_get(v_a_998_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v_a_998_, 1);
v_value_1003_ = lean_ctor_get(v_val_1002_, 3);
lean_inc(v_value_1003_);
if (lean_obj_tag(v_value_1003_) == 3)
{
lean_object* v_declName_1004_; 
v_declName_1004_ = lean_ctor_get(v_value_1003_, 0);
lean_inc(v_declName_1004_);
if (lean_obj_tag(v_declName_1004_) == 1)
{
lean_object* v_pre_1005_; 
v_pre_1005_ = lean_ctor_get(v_declName_1004_, 0);
lean_inc(v_pre_1005_);
if (lean_obj_tag(v_pre_1005_) == 1)
{
lean_object* v_pre_1006_; 
v_pre_1006_ = lean_ctor_get(v_pre_1005_, 0);
if (lean_obj_tag(v_pre_1006_) == 0)
{
lean_object* v_fvarId_1007_; lean_object* v_args_1008_; lean_object* v_str_1009_; lean_object* v_str_1010_; uint8_t v___x_1011_; 
v_fvarId_1007_ = lean_ctor_get(v_val_1002_, 0);
lean_inc(v_fvarId_1007_);
lean_dec(v_val_1002_);
v_args_1008_ = lean_ctor_get(v_value_1003_, 2);
lean_inc_ref(v_args_1008_);
lean_dec_ref_known(v_value_1003_, 3);
v_str_1009_ = lean_ctor_get(v_declName_1004_, 1);
lean_inc_ref(v_str_1009_);
lean_dec_ref_known(v_declName_1004_, 2);
v_str_1010_ = lean_ctor_get(v_pre_1005_, 1);
lean_inc_ref(v_str_1010_);
lean_dec_ref_known(v_pre_1005_, 2);
v___x_1011_ = lean_string_dec_eq(v_str_1010_, v___x_986_);
lean_dec_ref(v_str_1010_);
if (v___x_1011_ == 0)
{
lean_dec_ref(v_str_1009_);
lean_dec_ref(v_args_1008_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_973_;
}
else
{
lean_object* v___x_1012_; lean_object* v_sizeFVar_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1012_ = lean_box(1);
v___x_1035_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1036_ = lean_string_dec_eq(v_str_1009_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1038_ = lean_string_dec_eq(v_str_1009_, v___x_1037_);
lean_dec_ref(v_str_1009_);
if (v___x_1038_ == 0)
{
lean_dec_ref(v_args_1008_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_973_;
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = lean_array_get_size(v_args_1008_);
v___x_1040_ = lean_unsigned_to_nat(2u);
v___x_1041_ = lean_nat_dec_eq(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_dec_ref(v_args_1008_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_973_;
}
else
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_array_fget(v_args_1008_, v___x_993_);
lean_dec_ref(v_args_1008_);
if (lean_obj_tag(v___x_1042_) == 1)
{
lean_object* v_fvarId_1043_; 
v_fvarId_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_fvarId_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v_sizeFVar_1014_ = v_fvarId_1043_;
v___y_1015_ = v_a_963_;
v___y_1016_ = v_a_964_;
v___y_1017_ = v_a_965_;
v___y_1018_ = v_a_966_;
v___y_1019_ = v_a_967_;
v___y_1020_ = v_a_968_;
goto v___jp_1013_;
}
else
{
lean_dec(v___x_1042_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_973_;
}
}
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
lean_dec_ref(v_str_1009_);
v___x_1044_ = lean_array_get_size(v_args_1008_);
v___x_1045_ = lean_unsigned_to_nat(2u);
v___x_1046_ = lean_nat_dec_eq(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_dec_ref(v_args_1008_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_973_;
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_array_fget(v_args_1008_, v___x_993_);
lean_dec_ref(v_args_1008_);
if (lean_obj_tag(v___x_1047_) == 1)
{
lean_object* v_fvarId_1048_; 
v_fvarId_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_fvarId_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v_sizeFVar_1014_ = v_fvarId_1048_;
v___y_1015_ = v_a_963_;
v___y_1016_ = v_a_964_;
v___y_1017_ = v_a_965_;
v___y_1018_ = v_a_966_;
v___y_1019_ = v_a_967_;
v___y_1020_ = v_a_968_;
goto v___jp_1013_;
}
else
{
lean_dec(v___x_1047_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_973_;
}
}
}
v___jp_1013_:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_996_, v_sizeFVar_1014_, v___y_1018_);
lean_dec(v_sizeFVar_1014_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
if (lean_obj_tag(v_a_1022_) == 1)
{
lean_object* v_val_1023_; 
v_val_1023_ = lean_ctor_get(v_a_1022_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v_a_1022_, 1);
if (lean_obj_tag(v_val_1023_) == 0)
{
lean_object* v_value_1024_; 
v_value_1024_ = lean_ctor_get(v_val_1023_, 0);
lean_inc_ref(v_value_1024_);
lean_dec_ref_known(v_val_1023_, 1);
if (lean_obj_tag(v_value_1024_) == 0)
{
lean_object* v_val_1025_; lean_object* v___x_1026_; 
v_val_1025_ = lean_ctor_get(v_value_1024_, 0);
lean_inc(v_val_1025_);
lean_dec_ref_known(v_value_1024_, 1);
v___x_1026_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_fvarId_1007_, v_decl_961_, v_k_962_, v___x_1012_, v_val_1025_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
return v___x_1026_;
}
else
{
lean_dec_ref(v_value_1024_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_970_;
}
}
else
{
lean_dec(v_val_1023_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_970_;
}
}
else
{
lean_dec(v_a_1022_);
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_970_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec(v_fvarId_1007_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
v_a_1027_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1021_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1021_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_1005_, 2);
lean_dec_ref_known(v_declName_1004_, 2);
lean_dec_ref_known(v_value_1003_, 3);
lean_dec(v_val_1002_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_973_;
}
}
else
{
lean_dec_ref_known(v_declName_1004_, 2);
lean_dec(v_pre_1005_);
lean_dec_ref_known(v_value_1003_, 3);
lean_dec(v_val_1002_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_973_;
}
}
else
{
lean_dec(v_declName_1004_);
lean_dec_ref_known(v_value_1003_, 3);
lean_dec(v_val_1002_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_973_;
}
}
else
{
lean_dec(v_value_1003_);
lean_dec(v_val_1002_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_973_;
}
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
lean_dec(v_a_998_);
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
v___x_1049_ = lean_box(0);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1049_);
v___x_1051_ = v___x_1000_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
v_a_1054_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_997_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_997_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_976_;
}
}
}
}
}
else
{
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_976_;
}
}
else
{
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_976_;
}
}
else
{
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_976_;
}
}
else
{
lean_dec_ref(v_k_962_);
lean_dec_ref(v_decl_961_);
goto v___jp_976_;
}
v___jp_970_:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_box(0);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
v___jp_973_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_box(0);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
v___jp_976_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_box(0);
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___boxed(lean_object* v_decl_1062_, lean_object* v_k_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1062_, v_k_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
return v_res_1071_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0);
v___x_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(lean_object* v_env_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; lean_object* v_nextMacroScope_1081_; lean_object* v_ngen_1082_; lean_object* v_auxDeclNGen_1083_; lean_object* v_traceState_1084_; lean_object* v_messages_1085_; lean_object* v_infoState_1086_; lean_object* v_snapshotTasks_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1098_; 
v___x_1080_ = lean_st_ref_take(v___y_1078_);
v_nextMacroScope_1081_ = lean_ctor_get(v___x_1080_, 1);
v_ngen_1082_ = lean_ctor_get(v___x_1080_, 2);
v_auxDeclNGen_1083_ = lean_ctor_get(v___x_1080_, 3);
v_traceState_1084_ = lean_ctor_get(v___x_1080_, 4);
v_messages_1085_ = lean_ctor_get(v___x_1080_, 6);
v_infoState_1086_ = lean_ctor_get(v___x_1080_, 7);
v_snapshotTasks_1087_ = lean_ctor_get(v___x_1080_, 8);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; lean_object* v_unused_1100_; 
v_unused_1099_ = lean_ctor_get(v___x_1080_, 5);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v___x_1080_, 0);
lean_dec(v_unused_1100_);
v___x_1089_ = v___x_1080_;
v_isShared_1090_ = v_isSharedCheck_1098_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_snapshotTasks_1087_);
lean_inc(v_infoState_1086_);
lean_inc(v_messages_1085_);
lean_inc(v_traceState_1084_);
lean_inc(v_auxDeclNGen_1083_);
lean_inc(v_ngen_1082_);
lean_inc(v_nextMacroScope_1081_);
lean_dec(v___x_1080_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1098_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 5, v___x_1091_);
lean_ctor_set(v___x_1089_, 0, v_env_1077_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_env_1077_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_nextMacroScope_1081_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_ngen_1082_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_auxDeclNGen_1083_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_traceState_1084_);
lean_ctor_set(v_reuseFailAlloc_1097_, 5, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1097_, 6, v_messages_1085_);
lean_ctor_set(v_reuseFailAlloc_1097_, 7, v_infoState_1086_);
lean_ctor_set(v_reuseFailAlloc_1097_, 8, v_snapshotTasks_1087_);
v___x_1093_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = lean_st_ref_set(v___y_1078_, v___x_1093_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___boxed(lean_object* v_env_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1101_, v___y_1102_);
lean_dec(v___y_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(lean_object* v_env_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_1105_, v___y_1111_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(lean_object* v_env_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_env_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(size_t v_sz_1123_, size_t v_i_1124_, lean_object* v_bs_1125_, uint8_t v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_usize_dec_lt(v_i_1124_, v_sz_1123_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_bs_1125_);
return v___x_1134_;
}
else
{
uint8_t v___x_1135_; lean_object* v_v_1136_; lean_object* v___x_1137_; 
v___x_1135_ = 0;
v_v_1136_ = lean_array_uget_borrowed(v_bs_1125_, v_i_1124_);
lean_inc(v_v_1136_);
v___x_1137_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(v___x_1135_, v_v_1136_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; lean_object* v_bs_x27_1140_; size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = lean_unsigned_to_nat(0u);
v_bs_x27_1140_ = lean_array_uset(v_bs_1125_, v_i_1124_, v___x_1139_);
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_add(v_i_1124_, v___x_1141_);
v___x_1143_ = lean_array_uset(v_bs_x27_1140_, v_i_1124_, v_a_1138_);
v_i_1124_ = v___x_1142_;
v_bs_1125_ = v___x_1143_;
goto _start;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec_ref(v_bs_1125_);
v_a_1145_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1137_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1137_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(lean_object* v_sz_1153_, lean_object* v_i_1154_, lean_object* v_bs_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
size_t v_sz_boxed_1163_; size_t v_i_boxed_1164_; uint8_t v___y_8210__boxed_1165_; lean_object* v_res_1166_; 
v_sz_boxed_1163_ = lean_unbox_usize(v_sz_1153_);
lean_dec(v_sz_1153_);
v_i_boxed_1164_ = lean_unbox_usize(v_i_1154_);
lean_dec(v_i_1154_);
v___y_8210__boxed_1165_ = lean_unbox(v___y_1156_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_boxed_1163_, v_i_boxed_1164_, v_bs_1155_, v___y_8210__boxed_1165_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
return v_res_1166_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = lean_box(0);
v___x_1170_ = lean_unsigned_to_nat(16u);
v___x_1171_ = lean_mk_array(v___x_1170_, v___x_1169_);
return v___x_1171_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v___x_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3(void){
_start:
{
uint8_t v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = 0;
v___x_1176_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(lean_object* v_decl_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v_type_1195_; lean_object* v_value_1196_; lean_object* v___x_1197_; 
v___x_1193_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0));
v___x_1194_ = lean_st_mk_ref(v___x_1193_);
v_type_1195_ = lean_ctor_get(v_decl_1185_, 2);
lean_inc_ref(v_type_1195_);
v_value_1196_ = lean_ctor_get(v_decl_1185_, 3);
lean_inc(v_value_1196_);
v___x_1197_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(v_value_1196_, v___x_1194_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; lean_object* v_a_1208_; size_t v_sz_1290_; size_t v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref_known(v___x_1197_, 1);
v___x_1198_ = lean_st_ref_get(v___x_1194_);
lean_dec(v___x_1194_);
v___x_1199_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_1200_ = lean_st_mk_ref(v___x_1199_);
v___x_1201_ = 0;
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_decl_1185_);
v___x_1203_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3);
v___x_1204_ = l_Array_reverse___redArg(v___x_1198_);
v___x_1205_ = lean_array_push(v___x_1204_, v___x_1202_);
v___x_1206_ = 0;
v_sz_1290_ = lean_array_size(v___x_1205_);
v___x_1291_ = ((size_t)0ULL);
v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_1290_, v___x_1291_, v___x_1205_, v___x_1206_, v___x_1200_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1292_, 1);
v___x_1294_ = lean_st_ref_get(v___x_1200_);
lean_dec(v___x_1200_);
lean_dec(v___x_1294_);
v_a_1208_ = v_a_1293_;
goto v___jp_1207_;
}
else
{
lean_dec(v___x_1200_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1295_; 
v_a_1295_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1292_, 1);
v_a_1208_ = v_a_1295_;
goto v___jp_1207_;
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_type_1195_);
v_a_1296_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1292_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1292_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
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
v___jp_1207_:
{
lean_object* v___x_1209_; lean_object* v_env_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1209_ = lean_st_ref_get(v_a_1191_);
v_env_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc_ref_n(v_env_1210_, 2);
lean_dec(v___x_1209_);
v___x_1211_ = lean_array_get_size(v_a_1208_);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_sub(v___x_1211_, v___x_1212_);
v___x_1214_ = lean_array_get_borrowed(v___x_1203_, v_a_1208_, v___x_1213_);
lean_dec(v___x_1213_);
v___x_1215_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_1214_);
v___x_1216_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
v___x_1217_ = l_Lean_Compiler_LCNF_attachCodeDecls(v___x_1201_, v_a_1208_, v___x_1216_);
lean_dec_ref(v_a_1208_);
v___x_1218_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4));
lean_inc_ref(v___x_1217_);
v___x_1219_ = l_Lean_Compiler_LCNF_Code_toExpr(v___x_1201_, v___x_1217_, v___x_1218_);
v___x_1220_ = l_Lean_getClosedTermName_x3f(v_env_1210_, v___x_1219_);
if (lean_obj_tag(v___x_1220_) == 1)
{
lean_object* v_val_1221_; lean_object* v___x_1222_; 
lean_dec_ref(v___x_1219_);
lean_dec_ref(v_env_1210_);
lean_dec_ref(v_type_1195_);
v_val_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_val_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v___x_1222_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_1201_, v___x_1217_, v_a_1189_);
lean_dec_ref(v___x_1217_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v___x_1222_, 0);
lean_dec(v_unused_1230_);
v___x_1224_ = v___x_1222_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_dec(v___x_1222_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v_val_1221_);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_val_1221_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_val_1221_);
v_a_1231_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1222_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1222_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
else
{
lean_object* v___x_1239_; lean_object* v_baseName_1240_; lean_object* v_decls_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v___x_1220_);
v___x_1239_ = lean_st_ref_get(v_a_1187_);
v_baseName_1240_ = lean_ctor_get(v_a_1186_, 0);
v_decls_1241_ = lean_ctor_get(v___x_1239_, 0);
lean_inc_ref(v_decls_1241_);
lean_dec(v___x_1239_);
v___x_1242_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6));
v___x_1243_ = lean_array_get_size(v_decls_1241_);
lean_dec_ref(v_decls_1241_);
v___x_1244_ = lean_name_append_index_after(v___x_1242_, v___x_1243_);
lean_inc(v_baseName_1240_);
v___x_1245_ = l_Lean_Name_append(v_baseName_1240_, v___x_1244_);
lean_inc(v___x_1245_);
v___x_1246_ = l_Lean_cacheClosedTermName(v_env_1210_, v___x_1219_, v___x_1245_);
v___x_1247_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v___x_1246_, v_a_1191_);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v___x_1247_, 0);
lean_dec(v_unused_1289_);
v___x_1249_ = v___x_1247_;
v_isShared_1250_ = v_isSharedCheck_1288_;
goto v_resetjp_1248_;
}
else
{
lean_dec(v___x_1247_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1288_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = 1;
lean_inc(v___x_1245_);
v___x_1253_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1253_, 0, v___x_1245_);
lean_ctor_set(v___x_1253_, 1, v___x_1251_);
lean_ctor_set(v___x_1253_, 2, v_type_1195_);
lean_ctor_set(v___x_1253_, 3, v___x_1218_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*4, v___x_1252_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1217_);
v___x_1255_ = v___x_1249_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1217_);
v___x_1255_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7));
v___x_1257_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1257_, 0, v___x_1253_);
lean_ctor_set(v___x_1257_, 1, v___x_1255_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
lean_ctor_set_uint8(v___x_1257_, sizeof(void*)*3, v___x_1206_);
lean_inc_ref(v___x_1257_);
v___x_1258_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_1257_, v_a_1191_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1277_; 
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1258_, 0);
lean_dec(v_unused_1278_);
v___x_1260_ = v___x_1258_;
v_isShared_1261_ = v_isSharedCheck_1277_;
goto v_resetjp_1259_;
}
else
{
lean_dec(v___x_1258_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1277_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v_decls_1263_; lean_object* v_fvarDecisionCache_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1276_; 
v___x_1262_ = lean_st_ref_take(v_a_1187_);
v_decls_1263_ = lean_ctor_get(v___x_1262_, 0);
v_fvarDecisionCache_1264_ = lean_ctor_get(v___x_1262_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1266_ = v___x_1262_;
v_isShared_1267_ = v_isSharedCheck_1276_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_fvarDecisionCache_1264_);
lean_inc(v_decls_1263_);
lean_dec(v___x_1262_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1276_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = lean_array_push(v_decls_1263_, v___x_1257_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1268_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_fvarDecisionCache_1264_);
v___x_1270_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_st_ref_set(v_a_1187_, v___x_1270_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1245_);
v___x_1273_ = v___x_1260_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1245_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec_ref_known(v___x_1257_, 3);
lean_dec(v___x_1245_);
v_a_1279_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1258_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1258_);
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
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_type_1195_);
lean_dec(v___x_1194_);
lean_dec_ref(v_decl_1185_);
v_a_1304_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1197_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1197_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___boxed(lean_object* v_decl_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1320_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0(void){
_start:
{
uint8_t v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = 0;
v___x_1322_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(lean_object* v_msg_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0);
v___x_1325_ = lean_panic_fn_borrowed(v___x_1324_, v_msg_1323_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1329_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2));
v___x_1330_ = lean_unsigned_to_nat(9u);
v___x_1331_ = lean_unsigned_to_nat(641u);
v___x_1332_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1));
v___x_1333_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0));
v___x_1334_ = l_mkPanicMessageWithDecl(v___x_1333_, v___x_1332_, v___x_1331_, v___x_1330_, v___x_1329_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* v_code_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v___y_1346_; lean_object* v___y_1347_; uint8_t v___y_1348_; lean_object* v___y_1353_; lean_object* v___y_1354_; uint8_t v___y_1355_; lean_object* v_decl_1360_; lean_object* v_k_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1414_; lean_object* v___y_1415_; uint8_t v___y_1416_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; lean_object* v___y_1428_; lean_object* v___y_1429_; uint8_t v___y_1430_; lean_object* v___y_1435_; lean_object* v___y_1436_; uint8_t v___y_1437_; lean_object* v___y_1442_; lean_object* v___y_1443_; uint8_t v___y_1444_; 
switch(lean_obj_tag(v_code_1337_))
{
case 0:
{
lean_object* v_decl_1448_; lean_object* v_k_1449_; lean_object* v___y_1451_; uint8_t v___y_1452_; lean_object* v___y_1465_; uint8_t v___y_1466_; lean_object* v___y_1479_; uint8_t v___y_1480_; lean_object* v_value_1492_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; 
v_decl_1448_ = lean_ctor_get(v_code_1337_, 0);
v_k_1449_ = lean_ctor_get(v_code_1337_, 1);
v_value_1492_ = lean_ctor_get(v_decl_1448_, 3);
lean_inc(v_value_1492_);
if (lean_obj_tag(v_value_1492_) == 3)
{
lean_object* v_declName_1596_; 
v_declName_1596_ = lean_ctor_get(v_value_1492_, 0);
if (lean_obj_tag(v_declName_1596_) == 1)
{
lean_object* v_pre_1597_; 
v_pre_1597_ = lean_ctor_get(v_declName_1596_, 0);
if (lean_obj_tag(v_pre_1597_) == 1)
{
lean_object* v_pre_1598_; 
v_pre_1598_ = lean_ctor_get(v_pre_1597_, 0);
if (lean_obj_tag(v_pre_1598_) == 0)
{
lean_object* v_args_1599_; lean_object* v_str_1600_; lean_object* v_str_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v_sizeId_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; 
v_args_1599_ = lean_ctor_get(v_value_1492_, 2);
v_str_1600_ = lean_ctor_get(v_declName_1596_, 1);
v_str_1601_ = lean_ctor_get(v_pre_1597_, 1);
v___x_1602_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0));
v___x_1603_ = lean_string_dec_eq(v_str_1601_, v___x_1602_);
if (v___x_1603_ == 0)
{
v___y_1494_ = v_a_1338_;
v___y_1495_ = v_a_1339_;
v___y_1496_ = v_a_1340_;
v___y_1497_ = v_a_1341_;
v___y_1498_ = v_a_1342_;
v___y_1499_ = v_a_1343_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0));
v___x_1787_ = lean_string_dec_eq(v_str_1600_, v___x_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1));
v___x_1789_ = lean_string_dec_eq(v_str_1600_, v___x_1788_);
if (v___x_1789_ == 0)
{
v___y_1494_ = v_a_1338_;
v___y_1495_ = v_a_1339_;
v___y_1496_ = v_a_1340_;
v___y_1497_ = v_a_1341_;
v___y_1498_ = v_a_1342_;
v___y_1499_ = v_a_1343_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1790_ = lean_array_get_size(v_args_1599_);
v___x_1791_ = lean_unsigned_to_nat(2u);
v___x_1792_ = lean_nat_dec_eq(v___x_1790_, v___x_1791_);
if (v___x_1792_ == 0)
{
v___y_1494_ = v_a_1338_;
v___y_1495_ = v_a_1339_;
v___y_1496_ = v_a_1340_;
v___y_1497_ = v_a_1341_;
v___y_1498_ = v_a_1342_;
v___y_1499_ = v_a_1343_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_unsigned_to_nat(1u);
v___x_1794_ = lean_array_fget_borrowed(v_args_1599_, v___x_1793_);
if (lean_obj_tag(v___x_1794_) == 1)
{
lean_object* v_fvarId_1795_; 
v_fvarId_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_fvarId_1795_);
v_sizeId_1716_ = v_fvarId_1795_;
v___y_1717_ = v_a_1338_;
v___y_1718_ = v_a_1339_;
v___y_1719_ = v_a_1340_;
v___y_1720_ = v_a_1341_;
v___y_1721_ = v_a_1342_;
v___y_1722_ = v_a_1343_;
goto v___jp_1715_;
}
else
{
v___y_1494_ = v_a_1338_;
v___y_1495_ = v_a_1339_;
v___y_1496_ = v_a_1340_;
v___y_1497_ = v_a_1341_;
v___y_1498_ = v_a_1342_;
v___y_1499_ = v_a_1343_;
goto v___jp_1493_;
}
}
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1796_ = lean_array_get_size(v_args_1599_);
v___x_1797_ = lean_unsigned_to_nat(2u);
v___x_1798_ = lean_nat_dec_eq(v___x_1796_, v___x_1797_);
if (v___x_1798_ == 0)
{
v___y_1494_ = v_a_1338_;
v___y_1495_ = v_a_1339_;
v___y_1496_ = v_a_1340_;
v___y_1497_ = v_a_1341_;
v___y_1498_ = v_a_1342_;
v___y_1499_ = v_a_1343_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_unsigned_to_nat(1u);
v___x_1800_ = lean_array_fget_borrowed(v_args_1599_, v___x_1799_);
if (lean_obj_tag(v___x_1800_) == 1)
{
lean_object* v_fvarId_1801_; 
v_fvarId_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_fvarId_1801_);
v_sizeId_1716_ = v_fvarId_1801_;
v___y_1717_ = v_a_1338_;
v___y_1718_ = v_a_1339_;
v___y_1719_ = v_a_1340_;
v___y_1720_ = v_a_1341_;
v___y_1721_ = v_a_1342_;
v___y_1722_ = v_a_1343_;
goto v___jp_1715_;
}
else
{
v___y_1494_ = v_a_1338_;
v___y_1495_ = v_a_1339_;
v___y_1496_ = v_a_1340_;
v___y_1497_ = v_a_1341_;
v___y_1498_ = v_a_1342_;
v___y_1499_ = v_a_1343_;
goto v___jp_1493_;
}
}
}
}
v___jp_1604_:
{
lean_object* v___x_1611_; 
lean_inc_ref(v_k_1449_);
lean_inc_ref(v_decl_1448_);
v___x_1611_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1448_, v_k_1449_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
if (lean_obj_tag(v_a_1612_) == 1)
{
lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1653_; 
v_isSharedCheck_1653_ = !lean_is_exclusive(v_value_1492_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; 
v_unused_1654_ = lean_ctor_get(v_value_1492_, 2);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_value_1492_, 1);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_value_1492_, 0);
lean_dec(v_unused_1656_);
v___x_1614_ = v_value_1492_;
v_isShared_1615_ = v_isSharedCheck_1653_;
goto v_resetjp_1613_;
}
else
{
lean_dec(v_value_1492_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1653_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_val_1616_; lean_object* v_fst_1617_; lean_object* v_snd_1618_; lean_object* v___x_1619_; 
v_val_1616_ = lean_ctor_get(v_a_1612_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v_a_1612_, 1);
v_fst_1617_ = lean_ctor_get(v_val_1616_, 0);
lean_inc_n(v_fst_1617_, 2);
v_snd_1618_ = lean_ctor_get(v_val_1616_, 1);
lean_inc(v_snd_1618_);
lean_dec(v_val_1616_);
v___x_1619_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1617_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = 0;
v___x_1622_ = lean_box(0);
v___x_1623_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 2, v___x_1623_);
lean_ctor_set(v___x_1614_, 1, v___x_1622_);
lean_ctor_set(v___x_1614_, 0, v_a_1620_);
v___x_1625_ = v___x_1614_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1620_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1621_, v_fst_1617_, v___x_1625_, v___y_1608_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1618_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; size_t v___x_1630_; size_t v___x_1631_; uint8_t v___x_1632_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1630_ = lean_ptr_addr(v_k_1449_);
v___x_1631_ = lean_ptr_addr(v_a_1629_);
v___x_1632_ = lean_usize_dec_eq(v___x_1630_, v___x_1631_);
if (v___x_1632_ == 0)
{
v___y_1442_ = v_a_1627_;
v___y_1443_ = v_a_1629_;
v___y_1444_ = v___x_1632_;
goto v___jp_1441_;
}
else
{
size_t v___x_1633_; size_t v___x_1634_; uint8_t v___x_1635_; 
v___x_1633_ = lean_ptr_addr(v_decl_1448_);
v___x_1634_ = lean_ptr_addr(v_a_1627_);
v___x_1635_ = lean_usize_dec_eq(v___x_1633_, v___x_1634_);
v___y_1442_ = v_a_1627_;
v___y_1443_ = v_a_1629_;
v___y_1444_ = v___x_1635_;
goto v___jp_1441_;
}
}
else
{
lean_dec(v_a_1627_);
lean_dec_ref_known(v_code_1337_, 2);
return v___x_1628_;
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_snd_1618_);
lean_dec_ref_known(v_code_1337_, 2);
v_a_1636_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1626_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1626_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v_snd_1618_);
lean_dec(v_fst_1617_);
lean_del_object(v___x_1614_);
lean_dec_ref_known(v_code_1337_, 2);
v_a_1645_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1619_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1619_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
else
{
lean_object* v___x_1657_; 
lean_dec(v_a_1612_);
v___x_1657_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1603_, v_value_1492_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; uint8_t v___x_1659_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = lean_unbox(v_a_1658_);
lean_dec(v_a_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_inc_ref(v_k_1449_);
v___x_1660_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1449_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; size_t v___x_1662_; size_t v___x_1663_; uint8_t v___x_1664_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1660_, 1);
v___x_1662_ = lean_ptr_addr(v_k_1449_);
v___x_1663_ = lean_ptr_addr(v_a_1661_);
v___x_1664_ = lean_usize_dec_eq(v___x_1662_, v___x_1663_);
if (v___x_1664_ == 0)
{
v___y_1479_ = v_a_1661_;
v___y_1480_ = v___x_1664_;
goto v___jp_1478_;
}
else
{
size_t v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = lean_ptr_addr(v_decl_1448_);
v___x_1666_ = lean_usize_dec_eq(v___x_1665_, v___x_1665_);
v___y_1479_ = v_a_1661_;
v___y_1480_ = v___x_1666_;
goto v___jp_1478_;
}
}
else
{
lean_dec_ref_known(v_code_1337_, 2);
return v___x_1660_;
}
}
else
{
lean_object* v___x_1667_; 
lean_inc_ref(v_decl_1448_);
v___x_1667_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1448_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
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
lean_inc_ref(v_decl_1448_);
v___x_1673_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1669_, v_decl_1448_, v___x_1672_, v___y_1608_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
lean_inc_ref(v_k_1449_);
v___x_1675_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1449_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; size_t v___x_1677_; size_t v___x_1678_; uint8_t v___x_1679_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v___x_1677_ = lean_ptr_addr(v_k_1449_);
v___x_1678_ = lean_ptr_addr(v_a_1676_);
v___x_1679_ = lean_usize_dec_eq(v___x_1677_, v___x_1678_);
if (v___x_1679_ == 0)
{
v___y_1435_ = v_a_1676_;
v___y_1436_ = v_a_1674_;
v___y_1437_ = v___x_1679_;
goto v___jp_1434_;
}
else
{
size_t v___x_1680_; size_t v___x_1681_; uint8_t v___x_1682_; 
v___x_1680_ = lean_ptr_addr(v_decl_1448_);
v___x_1681_ = lean_ptr_addr(v_a_1674_);
v___x_1682_ = lean_usize_dec_eq(v___x_1680_, v___x_1681_);
v___y_1435_ = v_a_1676_;
v___y_1436_ = v_a_1674_;
v___y_1437_ = v___x_1682_;
goto v___jp_1434_;
}
}
else
{
lean_dec(v_a_1674_);
lean_dec_ref_known(v_code_1337_, 2);
return v___x_1675_;
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref_known(v_code_1337_, 2);
v_a_1683_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1673_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1673_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec_ref_known(v_code_1337_, 2);
v_a_1691_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1667_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1667_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
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
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec_ref_known(v_code_1337_, 2);
v_a_1699_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1657_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1657_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
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
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec_ref_known(v_value_1492_, 3);
lean_dec_ref_known(v_code_1337_, 2);
v_a_1707_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1611_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1611_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
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
v___jp_1715_:
{
uint8_t v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = 0;
v___x_1724_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(v___x_1723_, v_sizeId_1716_, v___y_1720_);
lean_dec(v_sizeId_1716_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
if (lean_obj_tag(v_a_1725_) == 1)
{
lean_object* v_val_1726_; 
v_val_1726_ = lean_ctor_get(v_a_1725_, 0);
lean_inc(v_val_1726_);
lean_dec_ref_known(v_a_1725_, 1);
if (lean_obj_tag(v_val_1726_) == 0)
{
lean_object* v_value_1727_; 
v_value_1727_ = lean_ctor_get(v_val_1726_, 0);
lean_inc_ref(v_value_1727_);
lean_dec_ref_known(v_val_1726_, 1);
if (lean_obj_tag(v_value_1727_) == 0)
{
lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1774_; 
v_isSharedCheck_1774_ = !lean_is_exclusive(v_value_1492_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; 
v_unused_1775_ = lean_ctor_get(v_value_1492_, 2);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_value_1492_, 1);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_value_1492_, 0);
lean_dec(v_unused_1777_);
v___x_1729_ = v_value_1492_;
v_isShared_1730_ = v_isSharedCheck_1774_;
goto v_resetjp_1728_;
}
else
{
lean_dec(v_value_1492_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1774_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v_val_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_val_1731_ = lean_ctor_get(v_value_1727_, 0);
lean_inc(v_val_1731_);
lean_dec_ref_known(v_value_1727_, 1);
v___x_1732_ = lean_unsigned_to_nat(0u);
v___x_1733_ = lean_nat_dec_eq(v_val_1731_, v___x_1732_);
lean_dec(v_val_1731_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_del_object(v___x_1729_);
lean_inc_ref(v_k_1449_);
v___x_1734_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1449_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; size_t v___x_1736_; size_t v___x_1737_; uint8_t v___x_1738_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = lean_ptr_addr(v_k_1449_);
v___x_1737_ = lean_ptr_addr(v_a_1735_);
v___x_1738_ = lean_usize_dec_eq(v___x_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
v___y_1465_ = v_a_1735_;
v___y_1466_ = v___x_1738_;
goto v___jp_1464_;
}
else
{
size_t v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_ptr_addr(v_decl_1448_);
v___x_1740_ = lean_usize_dec_eq(v___x_1739_, v___x_1739_);
v___y_1465_ = v_a_1735_;
v___y_1466_ = v___x_1740_;
goto v___jp_1464_;
}
}
else
{
lean_dec_ref_known(v_code_1337_, 2);
return v___x_1734_;
}
}
else
{
lean_object* v___x_1741_; 
lean_inc_ref(v_decl_1448_);
v___x_1741_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1448_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
v___x_1743_ = lean_box(0);
v___x_1744_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 2, v___x_1744_);
lean_ctor_set(v___x_1729_, 1, v___x_1743_);
lean_ctor_set(v___x_1729_, 0, v_a_1742_);
v___x_1746_ = v___x_1729_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1742_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; 
lean_inc_ref(v_decl_1448_);
v___x_1747_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1723_, v_decl_1448_, v___x_1746_, v___y_1720_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1747_, 1);
lean_inc_ref(v_k_1449_);
v___x_1749_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1449_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; size_t v___x_1751_; size_t v___x_1752_; uint8_t v___x_1753_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = lean_ptr_addr(v_k_1449_);
v___x_1752_ = lean_ptr_addr(v_a_1750_);
v___x_1753_ = lean_usize_dec_eq(v___x_1751_, v___x_1752_);
if (v___x_1753_ == 0)
{
v___y_1428_ = v_a_1748_;
v___y_1429_ = v_a_1750_;
v___y_1430_ = v___x_1753_;
goto v___jp_1427_;
}
else
{
size_t v___x_1754_; size_t v___x_1755_; uint8_t v___x_1756_; 
v___x_1754_ = lean_ptr_addr(v_decl_1448_);
v___x_1755_ = lean_ptr_addr(v_a_1748_);
v___x_1756_ = lean_usize_dec_eq(v___x_1754_, v___x_1755_);
v___y_1428_ = v_a_1748_;
v___y_1429_ = v_a_1750_;
v___y_1430_ = v___x_1756_;
goto v___jp_1427_;
}
}
else
{
lean_dec(v_a_1748_);
lean_dec_ref_known(v_code_1337_, 2);
return v___x_1749_;
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref_known(v_code_1337_, 2);
v_a_1757_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1747_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1747_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_del_object(v___x_1729_);
lean_dec_ref_known(v_code_1337_, 2);
v_a_1766_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1741_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1741_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_value_1727_);
v___y_1605_ = v___y_1717_;
v___y_1606_ = v___y_1718_;
v___y_1607_ = v___y_1719_;
v___y_1608_ = v___y_1720_;
v___y_1609_ = v___y_1721_;
v___y_1610_ = v___y_1722_;
goto v___jp_1604_;
}
}
else
{
lean_dec(v_val_1726_);
v___y_1605_ = v___y_1717_;
v___y_1606_ = v___y_1718_;
v___y_1607_ = v___y_1719_;
v___y_1608_ = v___y_1720_;
v___y_1609_ = v___y_1721_;
v___y_1610_ = v___y_1722_;
goto v___jp_1604_;
}
}
else
{
lean_dec(v_a_1725_);
v___y_1605_ = v___y_1717_;
v___y_1606_ = v___y_1718_;
v___y_1607_ = v___y_1719_;
v___y_1608_ = v___y_1720_;
v___y_1609_ = v___y_1721_;
v___y_1610_ = v___y_1722_;
goto v___jp_1604_;
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec_ref_known(v_value_1492_, 3);
lean_dec_ref_known(v_code_1337_, 2);
v_a_1778_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1724_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1724_);
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
v___y_1494_ = v_a_1338_;
v___y_1495_ = v_a_1339_;
v___y_1496_ = v_a_1340_;
v___y_1497_ = v_a_1341_;
v___y_1498_ = v_a_1342_;
v___y_1499_ = v_a_1343_;
goto v___jp_1493_;
}
}
else
{
v___y_1494_ = v_a_1338_;
v___y_1495_ = v_a_1339_;
v___y_1496_ = v_a_1340_;
v___y_1497_ = v_a_1341_;
v___y_1498_ = v_a_1342_;
v___y_1499_ = v_a_1343_;
goto v___jp_1493_;
}
}
else
{
v___y_1494_ = v_a_1338_;
v___y_1495_ = v_a_1339_;
v___y_1496_ = v_a_1340_;
v___y_1497_ = v_a_1341_;
v___y_1498_ = v_a_1342_;
v___y_1499_ = v_a_1343_;
goto v___jp_1493_;
}
}
else
{
v___y_1494_ = v_a_1338_;
v___y_1495_ = v_a_1339_;
v___y_1496_ = v_a_1340_;
v___y_1497_ = v_a_1341_;
v___y_1498_ = v_a_1342_;
v___y_1499_ = v_a_1343_;
goto v___jp_1493_;
}
v___jp_1450_:
{
if (v___y_1452_ == 0)
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1460_; 
lean_inc_ref(v_decl_1448_);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_code_1337_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; lean_object* v_unused_1462_; 
v_unused_1461_ = lean_ctor_get(v_code_1337_, 1);
lean_dec(v_unused_1461_);
v_unused_1462_ = lean_ctor_get(v_code_1337_, 0);
lean_dec(v_unused_1462_);
v___x_1454_ = v_code_1337_;
v_isShared_1455_ = v_isSharedCheck_1460_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v_code_1337_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1460_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v___y_1451_);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_decl_1448_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___y_1451_);
v___x_1457_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
}
}
else
{
lean_object* v___x_1463_; 
lean_dec_ref(v___y_1451_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_code_1337_);
return v___x_1463_;
}
}
v___jp_1464_:
{
if (v___y_1466_ == 0)
{
lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1474_; 
lean_inc_ref(v_decl_1448_);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_code_1337_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; lean_object* v_unused_1476_; 
v_unused_1475_ = lean_ctor_get(v_code_1337_, 1);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_code_1337_, 0);
lean_dec(v_unused_1476_);
v___x_1468_ = v_code_1337_;
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
else
{
lean_dec(v_code_1337_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 1, v___y_1465_);
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_decl_1448_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___y_1465_);
v___x_1471_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
}
}
else
{
lean_object* v___x_1477_; 
lean_dec_ref(v___y_1465_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_code_1337_);
return v___x_1477_;
}
}
v___jp_1478_:
{
if (v___y_1480_ == 0)
{
lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1488_; 
lean_inc_ref(v_decl_1448_);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_code_1337_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; lean_object* v_unused_1490_; 
v_unused_1489_ = lean_ctor_get(v_code_1337_, 1);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v_code_1337_, 0);
lean_dec(v_unused_1490_);
v___x_1482_ = v_code_1337_;
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
else
{
lean_dec(v_code_1337_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v___y_1479_);
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_decl_1448_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___y_1479_);
v___x_1485_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
}
else
{
lean_object* v___x_1491_; 
lean_dec_ref(v___y_1479_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_code_1337_);
return v___x_1491_;
}
}
v___jp_1493_:
{
lean_object* v___x_1500_; 
lean_inc_ref(v_k_1449_);
lean_inc_ref(v_decl_1448_);
v___x_1500_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(v_decl_1448_, v_k_1449_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
if (lean_obj_tag(v_a_1501_) == 1)
{
lean_object* v_val_1502_; lean_object* v_fst_1503_; lean_object* v_snd_1504_; lean_object* v___x_1505_; 
lean_dec(v_value_1492_);
v_val_1502_ = lean_ctor_get(v_a_1501_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v_a_1501_, 1);
v_fst_1503_ = lean_ctor_get(v_val_1502_, 0);
lean_inc_n(v_fst_1503_, 2);
v_snd_1504_ = lean_ctor_get(v_val_1502_, 1);
lean_inc(v_snd_1504_);
lean_dec(v_val_1502_);
v___x_1505_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_1503_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v___x_1507_ = 0;
v___x_1508_ = lean_box(0);
v___x_1509_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1510_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1510_, 0, v_a_1506_);
lean_ctor_set(v___x_1510_, 1, v___x_1508_);
lean_ctor_set(v___x_1510_, 2, v___x_1509_);
v___x_1511_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1507_, v_fst_1503_, v___x_1510_, v___y_1497_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1513_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_snd_1504_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; size_t v___x_1515_; size_t v___x_1516_; uint8_t v___x_1517_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = lean_ptr_addr(v_k_1449_);
v___x_1516_ = lean_ptr_addr(v_a_1514_);
v___x_1517_ = lean_usize_dec_eq(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
v___y_1421_ = v_a_1514_;
v___y_1422_ = v_a_1512_;
v___y_1423_ = v___x_1517_;
goto v___jp_1420_;
}
else
{
size_t v___x_1518_; size_t v___x_1519_; uint8_t v___x_1520_; 
v___x_1518_ = lean_ptr_addr(v_decl_1448_);
v___x_1519_ = lean_ptr_addr(v_a_1512_);
v___x_1520_ = lean_usize_dec_eq(v___x_1518_, v___x_1519_);
v___y_1421_ = v_a_1514_;
v___y_1422_ = v_a_1512_;
v___y_1423_ = v___x_1520_;
goto v___jp_1420_;
}
}
else
{
lean_dec(v_a_1512_);
lean_dec_ref_known(v_code_1337_, 2);
return v___x_1513_;
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_snd_1504_);
lean_dec_ref_known(v_code_1337_, 2);
v_a_1521_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1511_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1511_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
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
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_snd_1504_);
lean_dec(v_fst_1503_);
lean_dec_ref_known(v_code_1337_, 2);
v_a_1529_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1505_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1505_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
uint8_t v___x_1537_; lean_object* v___x_1538_; 
lean_dec(v_a_1501_);
v___x_1537_ = 1;
v___x_1538_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(v___x_1537_, v_value_1492_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; uint8_t v___x_1540_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1540_ = lean_unbox(v_a_1539_);
lean_dec(v_a_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
lean_inc_ref(v_k_1449_);
v___x_1541_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1449_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; size_t v___x_1543_; size_t v___x_1544_; uint8_t v___x_1545_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = lean_ptr_addr(v_k_1449_);
v___x_1544_ = lean_ptr_addr(v_a_1542_);
v___x_1545_ = lean_usize_dec_eq(v___x_1543_, v___x_1544_);
if (v___x_1545_ == 0)
{
v___y_1451_ = v_a_1542_;
v___y_1452_ = v___x_1545_;
goto v___jp_1450_;
}
else
{
size_t v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = lean_ptr_addr(v_decl_1448_);
v___x_1547_ = lean_usize_dec_eq(v___x_1546_, v___x_1546_);
v___y_1451_ = v_a_1542_;
v___y_1452_ = v___x_1547_;
goto v___jp_1450_;
}
}
else
{
lean_dec_ref_known(v_code_1337_, 2);
return v___x_1541_;
}
}
else
{
lean_object* v___x_1548_; 
lean_inc_ref(v_decl_1448_);
v___x_1548_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_1448_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = 0;
v___x_1551_ = lean_box(0);
v___x_1552_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4));
v___x_1553_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1553_, 0, v_a_1549_);
lean_ctor_set(v___x_1553_, 1, v___x_1551_);
lean_ctor_set(v___x_1553_, 2, v___x_1552_);
lean_inc_ref(v_decl_1448_);
v___x_1554_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(v___x_1550_, v_decl_1448_, v___x_1553_, v___y_1497_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
lean_inc_ref(v_k_1449_);
v___x_1556_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1449_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; size_t v___x_1558_; size_t v___x_1559_; uint8_t v___x_1560_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
v___x_1558_ = lean_ptr_addr(v_k_1449_);
v___x_1559_ = lean_ptr_addr(v_a_1557_);
v___x_1560_ = lean_usize_dec_eq(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
v___y_1414_ = v_a_1555_;
v___y_1415_ = v_a_1557_;
v___y_1416_ = v___x_1560_;
goto v___jp_1413_;
}
else
{
size_t v___x_1561_; size_t v___x_1562_; uint8_t v___x_1563_; 
v___x_1561_ = lean_ptr_addr(v_decl_1448_);
v___x_1562_ = lean_ptr_addr(v_a_1555_);
v___x_1563_ = lean_usize_dec_eq(v___x_1561_, v___x_1562_);
v___y_1414_ = v_a_1555_;
v___y_1415_ = v_a_1557_;
v___y_1416_ = v___x_1563_;
goto v___jp_1413_;
}
}
else
{
lean_dec(v_a_1555_);
lean_dec_ref_known(v_code_1337_, 2);
return v___x_1556_;
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref_known(v_code_1337_, 2);
v_a_1564_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1554_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1554_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
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
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref_known(v_code_1337_, 2);
v_a_1572_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1548_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1548_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref_known(v_code_1337_, 2);
v_a_1580_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1538_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1538_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
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
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec(v_value_1492_);
lean_dec_ref_known(v_code_1337_, 2);
v_a_1588_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1500_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1500_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
case 1:
{
lean_object* v_decl_1802_; lean_object* v_k_1803_; 
v_decl_1802_ = lean_ctor_get(v_code_1337_, 0);
v_k_1803_ = lean_ctor_get(v_code_1337_, 1);
lean_inc_ref(v_k_1803_);
lean_inc_ref(v_decl_1802_);
v_decl_1360_ = v_decl_1802_;
v_k_1361_ = v_k_1803_;
v___y_1362_ = v_a_1338_;
v___y_1363_ = v_a_1339_;
v___y_1364_ = v_a_1340_;
v___y_1365_ = v_a_1341_;
v___y_1366_ = v_a_1342_;
v___y_1367_ = v_a_1343_;
goto v___jp_1359_;
}
case 2:
{
lean_object* v_decl_1804_; lean_object* v_k_1805_; 
v_decl_1804_ = lean_ctor_get(v_code_1337_, 0);
v_k_1805_ = lean_ctor_get(v_code_1337_, 1);
lean_inc_ref(v_k_1805_);
lean_inc_ref(v_decl_1804_);
v_decl_1360_ = v_decl_1804_;
v_k_1361_ = v_k_1805_;
v___y_1362_ = v_a_1338_;
v___y_1363_ = v_a_1339_;
v___y_1364_ = v_a_1340_;
v___y_1365_ = v_a_1341_;
v___y_1366_ = v_a_1342_;
v___y_1367_ = v_a_1343_;
goto v___jp_1359_;
}
case 4:
{
lean_object* v_cases_1806_; lean_object* v_typeName_1807_; lean_object* v_resultType_1808_; lean_object* v_discr_1809_; lean_object* v_alts_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1849_; 
v_cases_1806_ = lean_ctor_get(v_code_1337_, 0);
lean_inc_ref(v_cases_1806_);
v_typeName_1807_ = lean_ctor_get(v_cases_1806_, 0);
v_resultType_1808_ = lean_ctor_get(v_cases_1806_, 1);
v_discr_1809_ = lean_ctor_get(v_cases_1806_, 2);
v_alts_1810_ = lean_ctor_get(v_cases_1806_, 3);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_cases_1806_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1812_ = v_cases_1806_;
v_isShared_1813_ = v_isSharedCheck_1849_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_alts_1810_);
lean_inc(v_discr_1809_);
lean_inc(v_resultType_1808_);
lean_inc(v_typeName_1807_);
lean_dec(v_cases_1806_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1849_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alts_1810_);
v___x_1815_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v___x_1814_, v_alts_1810_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1840_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1840_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1840_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
size_t v___x_1820_; size_t v___x_1821_; uint8_t v___x_1822_; 
v___x_1820_ = lean_ptr_addr(v_alts_1810_);
lean_dec_ref(v_alts_1810_);
v___x_1821_ = lean_ptr_addr(v_a_1816_);
v___x_1822_ = lean_usize_dec_eq(v___x_1820_, v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1835_; 
v_isSharedCheck_1835_ = !lean_is_exclusive(v_code_1337_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v_code_1337_, 0);
lean_dec(v_unused_1836_);
v___x_1824_ = v_code_1337_;
v_isShared_1825_ = v_isSharedCheck_1835_;
goto v_resetjp_1823_;
}
else
{
lean_dec(v_code_1337_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1835_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 3, v_a_1816_);
v___x_1827_ = v___x_1812_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_typeName_1807_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_resultType_1808_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_discr_1809_);
lean_ctor_set(v_reuseFailAlloc_1834_, 3, v_a_1816_);
v___x_1827_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1829_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1827_);
v___x_1829_ = v___x_1824_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1831_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1829_);
v___x_1831_ = v___x_1818_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
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
lean_dec(v_a_1816_);
lean_del_object(v___x_1812_);
lean_dec(v_discr_1809_);
lean_dec_ref(v_resultType_1808_);
lean_dec(v_typeName_1807_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v_code_1337_);
v___x_1838_ = v___x_1818_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_code_1337_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_del_object(v___x_1812_);
lean_dec_ref(v_alts_1810_);
lean_dec(v_discr_1809_);
lean_dec_ref(v_resultType_1808_);
lean_dec(v_typeName_1807_);
lean_dec_ref_known(v_code_1337_, 1);
v_a_1841_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1815_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1815_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
default: 
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v_code_1337_);
return v___x_1850_;
}
}
v___jp_1345_:
{
if (v___y_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec_ref(v_code_1337_);
v___x_1349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___y_1347_);
lean_ctor_set(v___x_1349_, 1, v___y_1346_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; 
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1346_);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v_code_1337_);
return v___x_1351_;
}
}
v___jp_1352_:
{
if (v___y_1355_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec_ref(v_code_1337_);
v___x_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___y_1354_);
lean_ctor_set(v___x_1356_, 1, v___y_1353_);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
else
{
lean_object* v___x_1358_; 
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___y_1353_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_code_1337_);
return v___x_1358_;
}
}
v___jp_1359_:
{
lean_object* v_params_1368_; lean_object* v_type_1369_; lean_object* v_value_1370_; lean_object* v___x_1371_; 
v_params_1368_ = lean_ctor_get(v_decl_1360_, 2);
lean_inc_ref(v_params_1368_);
v_type_1369_ = lean_ctor_get(v_decl_1360_, 3);
lean_inc_ref(v_type_1369_);
v_value_1370_ = lean_ctor_get(v_decl_1360_, 4);
lean_inc_ref(v_value_1370_);
v___x_1371_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_value_1370_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = 0;
v___x_1374_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1373_, v_decl_1360_, v_type_1369_, v_params_1368_, v_a_1372_, v___y_1365_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_k_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1376_) == 0)
{
switch(lean_obj_tag(v_code_1337_))
{
case 1:
{
lean_object* v_a_1377_; lean_object* v_decl_1378_; lean_object* v_k_1379_; size_t v___x_1380_; size_t v___x_1381_; uint8_t v___x_1382_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v_decl_1378_ = lean_ctor_get(v_code_1337_, 0);
v_k_1379_ = lean_ctor_get(v_code_1337_, 1);
v___x_1380_ = lean_ptr_addr(v_k_1379_);
v___x_1381_ = lean_ptr_addr(v_a_1377_);
v___x_1382_ = lean_usize_dec_eq(v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
v___y_1353_ = v_a_1377_;
v___y_1354_ = v_a_1375_;
v___y_1355_ = v___x_1382_;
goto v___jp_1352_;
}
else
{
size_t v___x_1383_; size_t v___x_1384_; uint8_t v___x_1385_; 
v___x_1383_ = lean_ptr_addr(v_decl_1378_);
v___x_1384_ = lean_ptr_addr(v_a_1375_);
v___x_1385_ = lean_usize_dec_eq(v___x_1383_, v___x_1384_);
v___y_1353_ = v_a_1377_;
v___y_1354_ = v_a_1375_;
v___y_1355_ = v___x_1385_;
goto v___jp_1352_;
}
}
case 2:
{
lean_object* v_a_1386_; lean_object* v_decl_1387_; lean_object* v_k_1388_; size_t v___x_1389_; size_t v___x_1390_; uint8_t v___x_1391_; 
v_a_1386_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1376_, 1);
v_decl_1387_ = lean_ctor_get(v_code_1337_, 0);
v_k_1388_ = lean_ctor_get(v_code_1337_, 1);
v___x_1389_ = lean_ptr_addr(v_k_1388_);
v___x_1390_ = lean_ptr_addr(v_a_1386_);
v___x_1391_ = lean_usize_dec_eq(v___x_1389_, v___x_1390_);
if (v___x_1391_ == 0)
{
v___y_1346_ = v_a_1386_;
v___y_1347_ = v_a_1375_;
v___y_1348_ = v___x_1391_;
goto v___jp_1345_;
}
else
{
size_t v___x_1392_; size_t v___x_1393_; uint8_t v___x_1394_; 
v___x_1392_ = lean_ptr_addr(v_decl_1387_);
v___x_1393_ = lean_ptr_addr(v_a_1375_);
v___x_1394_ = lean_usize_dec_eq(v___x_1392_, v___x_1393_);
v___y_1346_ = v_a_1386_;
v___y_1347_ = v_a_1375_;
v___y_1348_ = v___x_1394_;
goto v___jp_1345_;
}
}
default: 
{
lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_a_1375_);
lean_dec_ref(v_code_1337_);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v___x_1376_, 0);
lean_dec(v_unused_1404_);
v___x_1396_ = v___x_1376_;
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v___x_1376_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1398_ = lean_obj_once(&l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3, &l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once, _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3);
v___x_1399_ = l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(v___x_1398_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1399_);
v___x_1401_ = v___x_1396_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
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
}
else
{
lean_dec(v_a_1375_);
lean_dec_ref(v_code_1337_);
return v___x_1376_;
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v_k_1361_);
lean_dec_ref(v_code_1337_);
v_a_1405_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1374_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1374_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_dec_ref(v_type_1369_);
lean_dec_ref(v_params_1368_);
lean_dec_ref(v_k_1361_);
lean_dec_ref(v_decl_1360_);
lean_dec_ref(v_code_1337_);
return v___x_1371_;
}
}
v___jp_1413_:
{
if (v___y_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec_ref(v_code_1337_);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___y_1414_);
lean_ctor_set(v___x_1417_, 1, v___y_1415_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; 
lean_dec_ref(v___y_1415_);
lean_dec_ref(v___y_1414_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_code_1337_);
return v___x_1419_;
}
}
v___jp_1420_:
{
if (v___y_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
lean_dec_ref(v_code_1337_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___y_1422_);
lean_ctor_set(v___x_1424_, 1, v___y_1421_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; 
lean_dec_ref(v___y_1422_);
lean_dec_ref(v___y_1421_);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v_code_1337_);
return v___x_1426_;
}
}
v___jp_1427_:
{
if (v___y_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v_code_1337_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___y_1428_);
lean_ctor_set(v___x_1431_, 1, v___y_1429_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
lean_dec_ref(v___y_1429_);
lean_dec_ref(v___y_1428_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_code_1337_);
return v___x_1433_;
}
}
v___jp_1434_:
{
if (v___y_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref(v_code_1337_);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___y_1436_);
lean_ctor_set(v___x_1438_, 1, v___y_1435_);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; 
lean_dec_ref(v___y_1436_);
lean_dec_ref(v___y_1435_);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_code_1337_);
return v___x_1440_;
}
}
v___jp_1441_:
{
if (v___y_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v_code_1337_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___y_1442_);
lean_ctor_set(v___x_1445_, 1, v___y_1443_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; 
lean_dec_ref(v___y_1443_);
lean_dec_ref(v___y_1442_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_code_1337_);
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object* v_i_1851_, lean_object* v_as_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = lean_array_get_size(v_as_1852_);
v___x_1861_ = lean_nat_dec_lt(v_i_1851_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_dec(v_i_1851_);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_as_1852_);
return v___x_1862_;
}
else
{
lean_object* v_a_1863_; lean_object* v___y_1865_; 
v_a_1863_ = lean_array_fget_borrowed(v_as_1852_, v_i_1851_);
switch(lean_obj_tag(v_a_1863_))
{
case 0:
{
lean_object* v_code_1887_; 
v_code_1887_ = lean_ctor_get(v_a_1863_, 2);
lean_inc_ref(v_code_1887_);
v___y_1865_ = v_code_1887_;
goto v___jp_1864_;
}
case 1:
{
lean_object* v_code_1888_; 
v_code_1888_ = lean_ctor_get(v_a_1863_, 1);
lean_inc_ref(v_code_1888_);
v___y_1865_ = v_code_1888_;
goto v___jp_1864_;
}
default: 
{
lean_object* v_code_1889_; 
v_code_1889_ = lean_ctor_get(v_a_1863_, 0);
lean_inc_ref(v_code_1889_);
v___y_1865_ = v_code_1889_;
goto v___jp_1864_;
}
}
v___jp_1864_:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v___y_1865_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1868_; size_t v___x_1869_; size_t v___x_1870_; uint8_t v___x_1871_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 1);
lean_inc(v_a_1863_);
v___x_1868_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_1863_, v_a_1867_);
v___x_1869_ = lean_ptr_addr(v_a_1863_);
v___x_1870_ = lean_ptr_addr(v___x_1868_);
v___x_1871_ = lean_usize_dec_eq(v___x_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = lean_nat_add(v_i_1851_, v___x_1872_);
v___x_1874_ = lean_array_fset(v_as_1852_, v_i_1851_, v___x_1868_);
lean_dec(v_i_1851_);
v_i_1851_ = v___x_1873_;
v_as_1852_ = v___x_1874_;
goto _start;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref(v___x_1868_);
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = lean_nat_add(v_i_1851_, v___x_1876_);
lean_dec(v_i_1851_);
v_i_1851_ = v___x_1877_;
goto _start;
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v_as_1852_);
lean_dec(v_i_1851_);
v_a_1879_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1866_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1866_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object* v_i_1890_, lean_object* v_as_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_1890_, v_as_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object* v_code_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(v_code_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(lean_object* v_f_1909_, lean_object* v_v_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
if (lean_obj_tag(v_v_1910_) == 0)
{
lean_object* v_code_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1942_; 
v_code_1918_ = lean_ctor_get(v_v_1910_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_v_1910_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1920_ = v_v_1910_;
v_isShared_1921_ = v_isSharedCheck_1942_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_code_1918_);
lean_dec(v_v_1910_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1942_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; 
lean_inc(v___y_1916_);
lean_inc_ref(v___y_1915_);
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
v___x_1922_ = lean_apply_8(v_f_1909_, v_code_1918_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, lean_box(0));
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1933_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v_a_1923_);
v___x_1928_ = v___x_1920_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1930_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1928_);
v___x_1930_ = v___x_1925_;
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
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_del_object(v___x_1920_);
v_a_1934_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1922_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1922_);
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
lean_object* v___x_1943_; 
lean_dec_ref(v_f_1909_);
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v_v_1910_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(lean_object* v_f_1944_, lean_object* v_v_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_1944_, v_v_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(uint8_t v_pu_1954_, lean_object* v_f_1955_, lean_object* v_v_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_1955_, v_v_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(lean_object* v_pu_1965_, lean_object* v_f_1966_, lean_object* v_v_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
uint8_t v_pu_boxed_1975_; lean_object* v_res_1976_; 
v_pu_boxed_1975_ = lean_unbox(v_pu_1965_);
v_res_1976_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_boxed_1975_, v_f_1966_, v_v_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object* v_decl_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_toSignature_1986_; lean_object* v_value_1987_; uint8_t v_recursive_1988_; lean_object* v_inlineAttr_x3f_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2014_; 
v_toSignature_1986_ = lean_ctor_get(v_decl_1978_, 0);
v_value_1987_ = lean_ctor_get(v_decl_1978_, 1);
v_recursive_1988_ = lean_ctor_get_uint8(v_decl_1978_, sizeof(void*)*3);
v_inlineAttr_x3f_1989_ = lean_ctor_get(v_decl_1978_, 2);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_decl_1978_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1991_ = v_decl_1978_;
v_isShared_1992_ = v_isSharedCheck_2014_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_inlineAttr_x3f_1989_);
lean_inc(v_value_1987_);
lean_inc(v_toSignature_1986_);
lean_dec(v_decl_1978_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2014_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = ((lean_object*)(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0));
v___x_1994_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v___x_1993_, v_value_1987_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2005_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 1, v_a_1995_);
v___x_2000_ = v___x_1991_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_toSignature_1986_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_a_1995_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_inlineAttr_x3f_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2004_, sizeof(void*)*3, v_recursive_1988_);
v___x_2000_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2000_);
v___x_2002_ = v___x_1997_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_del_object(v___x_1991_);
lean_dec(v_inlineAttr_x3f_1989_);
lean_dec_ref(v_toSignature_1986_);
v_a_2006_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1994_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1994_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(lean_object* v_decl_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
return v_res_2023_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2026_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2, &l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
v___x_2027_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0));
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_2026_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* v_decl_2029_, lean_object* v_sccDecls_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v_toSignature_2039_; lean_object* v_name_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1, &l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1);
v___x_2038_ = lean_st_mk_ref(v___x_2037_);
v_toSignature_2039_ = lean_ctor_get(v_decl_2029_, 0);
v_name_2040_ = lean_ctor_get(v_toSignature_2039_, 0);
lean_inc(v_name_2040_);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v_name_2040_);
lean_ctor_set(v___x_2041_, 1, v_sccDecls_2030_);
v___x_2042_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(v_decl_2029_, v___x_2041_, v___x_2038_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
lean_dec_ref_known(v___x_2041_, 2);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2069_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2069_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2069_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v_decls_2048_; lean_object* v_decl_2050_; lean_object* v___x_2055_; uint8_t v___x_2056_; uint8_t v___x_2057_; 
v___x_2047_ = lean_st_ref_get(v___x_2038_);
lean_dec(v___x_2038_);
v_decls_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc_ref(v_decls_2048_);
lean_dec(v___x_2047_);
v___x_2055_ = lean_array_get_size(v_decls_2048_);
v___x_2056_ = lean_nat_dec_eq(v___x_2055_, v___x_2036_);
v___x_2057_ = lean_bool_not(v___x_2056_);
if (v___x_2057_ == 0)
{
v_decl_2050_ = v_a_2043_;
goto v___jp_2049_;
}
else
{
uint8_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = 0;
v___x_2059_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(v___x_2058_, v_a_2043_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2059_, 1);
v_decl_2050_ = v_a_2060_;
goto v___jp_2049_;
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref(v_decls_2048_);
lean_del_object(v___x_2045_);
v_a_2061_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2059_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2059_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
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
v___jp_2049_:
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2051_ = lean_array_push(v_decls_2048_, v_decl_2050_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2051_);
v___x_2053_ = v___x_2045_;
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
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v___x_2038_);
v_a_2070_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2042_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2042_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(lean_object* v_decl_2078_, lean_object* v_sccDecls_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v_decl_2078_, v_sccDecls_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(lean_object* v_decls_2086_, lean_object* v_as_2087_, size_t v_i_2088_, size_t v_stop_2089_, lean_object* v_b_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_a_2097_; uint8_t v___x_2101_; 
v___x_2101_ = lean_usize_dec_eq(v_i_2088_, v_stop_2089_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_array_uget_borrowed(v_as_2087_, v_i_2088_);
lean_inc_ref(v_decls_2086_);
lean_inc(v___x_2102_);
v___x_2103_ = l_Lean_Compiler_LCNF_Decl_extractClosed(v___x_2102_, v_decls_2086_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
v___x_2105_ = l_Array_append___redArg(v_b_2090_, v_a_2104_);
lean_dec(v_a_2104_);
v_a_2097_ = v___x_2105_;
goto v___jp_2096_;
}
else
{
lean_dec_ref(v_b_2090_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2106_; 
v_a_2106_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2103_, 1);
v_a_2097_ = v_a_2106_;
goto v___jp_2096_;
}
else
{
lean_dec_ref(v_decls_2086_);
return v___x_2103_;
}
}
}
else
{
lean_object* v___x_2107_; 
lean_dec_ref(v_decls_2086_);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v_b_2090_);
return v___x_2107_;
}
v___jp_2096_:
{
size_t v___x_2098_; size_t v___x_2099_; 
v___x_2098_ = ((size_t)1ULL);
v___x_2099_ = lean_usize_add(v_i_2088_, v___x_2098_);
v_i_2088_ = v___x_2099_;
v_b_2090_ = v_a_2097_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object* v_decls_2108_, lean_object* v_as_2109_, lean_object* v_i_2110_, lean_object* v_stop_2111_, lean_object* v_b_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
size_t v_i_boxed_2118_; size_t v_stop_boxed_2119_; lean_object* v_res_2120_; 
v_i_boxed_2118_ = lean_unbox_usize(v_i_2110_);
lean_dec(v_i_2110_);
v_stop_boxed_2119_ = lean_unbox_usize(v_stop_2111_);
lean_dec(v_stop_2111_);
v_res_2120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2108_, v_as_2109_, v_i_boxed_2118_, v_stop_boxed_2119_, v_b_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec_ref(v_as_2109_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* v___x_2121_, lean_object* v_decls_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_2123_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2153_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2153_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2153_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
uint8_t v_extractClosed_2133_; 
v_extractClosed_2133_ = lean_ctor_get_uint8(v_a_2129_, sizeof(void*)*4 + 1);
lean_dec(v_a_2129_);
if (v_extractClosed_2133_ == 0)
{
lean_object* v___x_2135_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v_decls_2122_);
v___x_2135_ = v___x_2131_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_decls_2122_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2137_ = lean_mk_empty_array_with_capacity(v___x_2121_);
v___x_2138_ = lean_array_get_size(v_decls_2122_);
v___x_2139_ = lean_nat_dec_lt(v___x_2121_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2141_; 
lean_dec_ref(v_decls_2122_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2137_);
v___x_2141_ = v___x_2131_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2137_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
else
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_nat_dec_le(v___x_2138_, v___x_2138_);
if (v___x_2143_ == 0)
{
if (v___x_2139_ == 0)
{
lean_object* v___x_2145_; 
lean_dec_ref(v_decls_2122_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2137_);
v___x_2145_ = v___x_2131_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2137_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
else
{
size_t v___x_2147_; size_t v___x_2148_; lean_object* v___x_2149_; 
lean_del_object(v___x_2131_);
v___x_2147_ = ((size_t)0ULL);
v___x_2148_ = lean_usize_of_nat(v___x_2138_);
lean_inc_ref(v_decls_2122_);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2122_, v_decls_2122_, v___x_2147_, v___x_2148_, v___x_2137_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec_ref(v_decls_2122_);
return v___x_2149_;
}
}
else
{
size_t v___x_2150_; size_t v___x_2151_; lean_object* v___x_2152_; 
lean_del_object(v___x_2131_);
v___x_2150_ = ((size_t)0ULL);
v___x_2151_ = lean_usize_of_nat(v___x_2138_);
lean_inc_ref(v_decls_2122_);
v___x_2152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_2122_, v_decls_2122_, v___x_2150_, v___x_2151_, v___x_2137_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec_ref(v_decls_2122_);
return v___x_2152_;
}
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_decls_2122_);
v_a_2154_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2128_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2128_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object* v___x_2162_, lean_object* v_decls_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(v___x_2162_, v_decls_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___x_2162_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2252_; uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2252_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2253_ = 1;
v___x_2254_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_));
v___x_2255_ = l_Lean_registerTraceClass(v___x_2252_, v___x_2253_, v___x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
return v_res_2257_;
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
