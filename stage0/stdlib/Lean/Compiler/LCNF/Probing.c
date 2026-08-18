// Lean compiler output
// Module: Lean.Compiler.LCNF.Probing
// Imports: public import Lean.Compiler.LCNF.PhaseExt
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_size(uint8_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__0_value),((lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__1_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__3_value),((lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__4_value),((lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Probe_getJps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_getJps___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_getJps___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3;
static const lean_string_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "probe"};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 226, 36, 16, 11, 213, 189, 181)}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(60, 150, 55, 23, 179, 120, 143, 48)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Probing"};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 176, 148, 85, 84, 103, 135, 80)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(22, 95, 52, 82, 201, 93, 155, 160)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 135, 77, 48, 10, 193, 107, 167)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 243, 178, 155, 207, 21, 86, 75)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 32, 97, 236, 167, 177, 209, 200)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Probe"};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(221, 220, 56, 107, 178, 130, 195, 235)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 198, 238, 95, 73, 174, 204, 216)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 160, 124, 63, 130, 135, 193, 8)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 79, 181, 134, 106, 79, 240, 31)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 80, 58, 113, 74, 134, 55, 21)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 102, 91, 152, 148, 12, 32, 152)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 195, 87, 22, 184, 160, 76, 111)}};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO(lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__0);
v___x_3_ = l_StateRefT_x27_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg(lean_object* v_f_8_, lean_object* v_data_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_15_; lean_object* v_toApplicative_16_; lean_object* v_toFunctor_17_; lean_object* v_toSeq_18_; lean_object* v_toSeqLeft_19_; lean_object* v_toSeqRight_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___x_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v_toApplicative_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_63_; 
v___x_15_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_16_ = lean_ctor_get(v___x_15_, 0);
v_toFunctor_17_ = lean_ctor_get(v_toApplicative_16_, 0);
v_toSeq_18_ = lean_ctor_get(v_toApplicative_16_, 2);
v_toSeqLeft_19_ = lean_ctor_get(v_toApplicative_16_, 3);
v_toSeqRight_20_ = lean_ctor_get(v_toApplicative_16_, 4);
v___f_21_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_22_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_17_, 2);
v___f_23_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_23_, 0, v_toFunctor_17_);
v___f_24_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_24_, 0, v_toFunctor_17_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___f_23_);
lean_ctor_set(v___x_25_, 1, v___f_24_);
lean_inc(v_toSeqRight_20_);
v___f_26_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_26_, 0, v_toSeqRight_20_);
lean_inc(v_toSeqLeft_19_);
v___f_27_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_27_, 0, v_toSeqLeft_19_);
lean_inc(v_toSeq_18_);
v___f_28_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_28_, 0, v_toSeq_18_);
v___x_29_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_29_, 0, v___x_25_);
lean_ctor_set(v___x_29_, 1, v___f_21_);
lean_ctor_set(v___x_29_, 2, v___f_28_);
lean_ctor_set(v___x_29_, 3, v___f_27_);
lean_ctor_set(v___x_29_, 4, v___f_26_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___f_22_);
v___x_31_ = l_StateRefT_x27_instMonad___redArg(v___x_30_);
v_toApplicative_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_63_ == 0)
{
lean_object* v_unused_64_; 
v_unused_64_ = lean_ctor_get(v___x_31_, 1);
lean_dec(v_unused_64_);
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_63_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_toApplicative_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_63_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v_toFunctor_36_; lean_object* v_toSeq_37_; lean_object* v_toSeqLeft_38_; lean_object* v_toSeqRight_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_61_; 
v_toFunctor_36_ = lean_ctor_get(v_toApplicative_32_, 0);
v_toSeq_37_ = lean_ctor_get(v_toApplicative_32_, 2);
v_toSeqLeft_38_ = lean_ctor_get(v_toApplicative_32_, 3);
v_toSeqRight_39_ = lean_ctor_get(v_toApplicative_32_, 4);
v_isSharedCheck_61_ = !lean_is_exclusive(v_toApplicative_32_);
if (v_isSharedCheck_61_ == 0)
{
lean_object* v_unused_62_; 
v_unused_62_ = lean_ctor_get(v_toApplicative_32_, 1);
lean_dec(v_unused_62_);
v___x_41_ = v_toApplicative_32_;
v_isShared_42_ = v_isSharedCheck_61_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_toSeqRight_39_);
lean_inc(v_toSeqLeft_38_);
lean_inc(v_toSeq_37_);
lean_inc(v_toFunctor_36_);
lean_dec(v_toApplicative_32_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_61_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___f_43_; lean_object* v___f_44_; lean_object* v___f_45_; lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___f_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___x_52_; 
v___f_43_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_44_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_36_);
v___f_45_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_45_, 0, v_toFunctor_36_);
v___f_46_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_46_, 0, v_toFunctor_36_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___f_45_);
lean_ctor_set(v___x_47_, 1, v___f_46_);
v___f_48_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_48_, 0, v_toSeqRight_39_);
v___f_49_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_49_, 0, v_toSeqLeft_38_);
v___f_50_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_50_, 0, v_toSeq_37_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 4, v___f_48_);
lean_ctor_set(v___x_41_, 3, v___f_49_);
lean_ctor_set(v___x_41_, 2, v___f_50_);
lean_ctor_set(v___x_41_, 1, v___f_43_);
lean_ctor_set(v___x_41_, 0, v___x_47_);
v___x_52_ = v___x_41_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___f_43_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v___f_50_);
lean_ctor_set(v_reuseFailAlloc_60_, 3, v___f_49_);
lean_ctor_set(v_reuseFailAlloc_60_, 4, v___f_48_);
v___x_52_ = v_reuseFailAlloc_60_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_54_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 1, v___f_44_);
lean_ctor_set(v___x_34_, 0, v___x_52_);
v___x_54_ = v___x_34_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_52_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v___f_44_);
v___x_54_ = v_reuseFailAlloc_59_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
size_t v_sz_55_; size_t v___x_56_; lean_object* v___x_7__overap_57_; lean_object* v___x_58_; 
v_sz_55_ = lean_array_size(v_data_9_);
v___x_56_ = ((size_t)0ULL);
v___x_7__overap_57_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_54_, v_f_8_, v_sz_55_, v___x_56_, v_data_9_);
lean_inc(v_a_13_);
lean_inc_ref(v_a_12_);
lean_inc(v_a_11_);
lean_inc_ref(v_a_10_);
v___x_58_ = lean_apply_5(v___x_7__overap_57_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, lean_box(0));
return v___x_58_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg___boxed(lean_object* v_f_65_, lean_object* v_data_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Compiler_LCNF_Probe_map___redArg(v_f_65_, v_data_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map(lean_object* v_00_u03b1_73_, lean_object* v_00_u03b2_74_, lean_object* v_f_75_, lean_object* v_data_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_toApplicative_83_; lean_object* v_toFunctor_84_; lean_object* v_toSeq_85_; lean_object* v_toSeqLeft_86_; lean_object* v_toSeqRight_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v_toApplicative_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_130_; 
v___x_82_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_83_ = lean_ctor_get(v___x_82_, 0);
v_toFunctor_84_ = lean_ctor_get(v_toApplicative_83_, 0);
v_toSeq_85_ = lean_ctor_get(v_toApplicative_83_, 2);
v_toSeqLeft_86_ = lean_ctor_get(v_toApplicative_83_, 3);
v_toSeqRight_87_ = lean_ctor_get(v_toApplicative_83_, 4);
v___f_88_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_89_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_84_, 2);
v___f_90_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_90_, 0, v_toFunctor_84_);
v___f_91_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_91_, 0, v_toFunctor_84_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___f_90_);
lean_ctor_set(v___x_92_, 1, v___f_91_);
lean_inc(v_toSeqRight_87_);
v___f_93_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_93_, 0, v_toSeqRight_87_);
lean_inc(v_toSeqLeft_86_);
v___f_94_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_94_, 0, v_toSeqLeft_86_);
lean_inc(v_toSeq_85_);
v___f_95_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_95_, 0, v_toSeq_85_);
v___x_96_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_96_, 0, v___x_92_);
lean_ctor_set(v___x_96_, 1, v___f_88_);
lean_ctor_set(v___x_96_, 2, v___f_95_);
lean_ctor_set(v___x_96_, 3, v___f_94_);
lean_ctor_set(v___x_96_, 4, v___f_93_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___f_89_);
v___x_98_ = l_StateRefT_x27_instMonad___redArg(v___x_97_);
v_toApplicative_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; 
v_unused_131_ = lean_ctor_get(v___x_98_, 1);
lean_dec(v_unused_131_);
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_130_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_toApplicative_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_130_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_toFunctor_103_; lean_object* v_toSeq_104_; lean_object* v_toSeqLeft_105_; lean_object* v_toSeqRight_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_128_; 
v_toFunctor_103_ = lean_ctor_get(v_toApplicative_99_, 0);
v_toSeq_104_ = lean_ctor_get(v_toApplicative_99_, 2);
v_toSeqLeft_105_ = lean_ctor_get(v_toApplicative_99_, 3);
v_toSeqRight_106_ = lean_ctor_get(v_toApplicative_99_, 4);
v_isSharedCheck_128_ = !lean_is_exclusive(v_toApplicative_99_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v_toApplicative_99_, 1);
lean_dec(v_unused_129_);
v___x_108_ = v_toApplicative_99_;
v_isShared_109_ = v_isSharedCheck_128_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_toSeqRight_106_);
lean_inc(v_toSeqLeft_105_);
lean_inc(v_toSeq_104_);
lean_inc(v_toFunctor_103_);
lean_dec(v_toApplicative_99_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_128_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___f_115_; lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___x_119_; 
v___f_110_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_111_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_103_);
v___f_112_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_112_, 0, v_toFunctor_103_);
v___f_113_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_113_, 0, v_toFunctor_103_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___f_112_);
lean_ctor_set(v___x_114_, 1, v___f_113_);
v___f_115_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_115_, 0, v_toSeqRight_106_);
v___f_116_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_116_, 0, v_toSeqLeft_105_);
v___f_117_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_117_, 0, v_toSeq_104_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 4, v___f_115_);
lean_ctor_set(v___x_108_, 3, v___f_116_);
lean_ctor_set(v___x_108_, 2, v___f_117_);
lean_ctor_set(v___x_108_, 1, v___f_110_);
lean_ctor_set(v___x_108_, 0, v___x_114_);
v___x_119_ = v___x_108_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___f_110_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v___f_117_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v___f_116_);
lean_ctor_set(v_reuseFailAlloc_127_, 4, v___f_115_);
v___x_119_ = v_reuseFailAlloc_127_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_121_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___f_111_);
lean_ctor_set(v___x_101_, 0, v___x_119_);
v___x_121_ = v___x_101_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v___f_111_);
v___x_121_ = v_reuseFailAlloc_126_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
size_t v_sz_122_; size_t v___x_123_; lean_object* v___x_57__overap_124_; lean_object* v___x_125_; 
v_sz_122_ = lean_array_size(v_data_76_);
v___x_123_ = ((size_t)0ULL);
v___x_57__overap_124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_121_, v_f_75_, v_sz_122_, v___x_123_, v_data_76_);
lean_inc(v_a_80_);
lean_inc_ref(v_a_79_);
lean_inc(v_a_78_);
lean_inc_ref(v_a_77_);
v___x_125_ = lean_apply_5(v___x_57__overap_124_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, lean_box(0));
return v___x_125_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map___boxed(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_f_134_, lean_object* v_data_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Compiler_LCNF_Probe_map(v_00_u03b1_132_, v_00_u03b2_133_, v_f_134_, v_data_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0(lean_object* v_f_142_, lean_object* v_acc_143_, lean_object* v_a_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; 
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
lean_inc_ref(v___y_145_);
lean_inc(v_a_144_);
v___x_150_ = lean_apply_6(v_f_142_, v_a_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, lean_box(0));
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_163_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_163_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_163_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_163_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint8_t v___x_155_; 
v___x_155_ = lean_unbox(v_a_151_);
lean_dec(v_a_151_);
if (v___x_155_ == 0)
{
lean_object* v___x_157_; 
lean_dec(v_a_144_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v_acc_143_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_acc_143_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
else
{
lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_159_ = lean_array_push(v_acc_143_, v_a_144_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_159_);
v___x_161_ = v___x_153_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec(v_a_144_);
lean_dec_ref(v_acc_143_);
v_a_164_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_150_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_150_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed(lean_object* v_f_172_, lean_object* v_acc_173_, lean_object* v_a_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0(v_f_172_, v_acc_173_, v_a_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg(lean_object* v_f_183_, lean_object* v_data_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_190_; lean_object* v_toApplicative_191_; lean_object* v_toFunctor_192_; lean_object* v_toSeq_193_; lean_object* v_toSeqLeft_194_; lean_object* v_toSeqRight_195_; lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___f_198_; lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___f_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_toApplicative_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_250_; 
v___x_190_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_191_ = lean_ctor_get(v___x_190_, 0);
v_toFunctor_192_ = lean_ctor_get(v_toApplicative_191_, 0);
v_toSeq_193_ = lean_ctor_get(v_toApplicative_191_, 2);
v_toSeqLeft_194_ = lean_ctor_get(v_toApplicative_191_, 3);
v_toSeqRight_195_ = lean_ctor_get(v_toApplicative_191_, 4);
v___f_196_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_197_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_192_, 2);
v___f_198_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_198_, 0, v_toFunctor_192_);
v___f_199_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_199_, 0, v_toFunctor_192_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v___f_198_);
lean_ctor_set(v___x_200_, 1, v___f_199_);
lean_inc(v_toSeqRight_195_);
v___f_201_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_201_, 0, v_toSeqRight_195_);
lean_inc(v_toSeqLeft_194_);
v___f_202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_202_, 0, v_toSeqLeft_194_);
lean_inc(v_toSeq_193_);
v___f_203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_203_, 0, v_toSeq_193_);
v___x_204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_204_, 0, v___x_200_);
lean_ctor_set(v___x_204_, 1, v___f_196_);
lean_ctor_set(v___x_204_, 2, v___f_203_);
lean_ctor_set(v___x_204_, 3, v___f_202_);
lean_ctor_set(v___x_204_, 4, v___f_201_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___f_197_);
v___x_206_ = l_StateRefT_x27_instMonad___redArg(v___x_205_);
v_toApplicative_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v___x_206_, 1);
lean_dec(v_unused_251_);
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_250_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_toApplicative_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_250_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_toFunctor_211_; lean_object* v_toSeq_212_; lean_object* v_toSeqLeft_213_; lean_object* v_toSeqRight_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_248_; 
v_toFunctor_211_ = lean_ctor_get(v_toApplicative_207_, 0);
v_toSeq_212_ = lean_ctor_get(v_toApplicative_207_, 2);
v_toSeqLeft_213_ = lean_ctor_get(v_toApplicative_207_, 3);
v_toSeqRight_214_ = lean_ctor_get(v_toApplicative_207_, 4);
v_isSharedCheck_248_ = !lean_is_exclusive(v_toApplicative_207_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_toApplicative_207_, 1);
lean_dec(v_unused_249_);
v___x_216_ = v_toApplicative_207_;
v_isShared_217_ = v_isSharedCheck_248_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_toSeqRight_214_);
lean_inc(v_toSeqLeft_213_);
lean_inc(v_toSeq_212_);
lean_inc(v_toFunctor_211_);
lean_dec(v_toApplicative_207_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_248_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___f_218_; lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___f_225_; lean_object* v___x_227_; 
v___f_218_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_219_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_211_);
v___f_220_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_220_, 0, v_toFunctor_211_);
v___f_221_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_221_, 0, v_toFunctor_211_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___f_220_);
lean_ctor_set(v___x_222_, 1, v___f_221_);
v___f_223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_223_, 0, v_toSeqRight_214_);
v___f_224_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_224_, 0, v_toSeqLeft_213_);
v___f_225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_225_, 0, v_toSeq_212_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 4, v___f_223_);
lean_ctor_set(v___x_216_, 3, v___f_224_);
lean_ctor_set(v___x_216_, 2, v___f_225_);
lean_ctor_set(v___x_216_, 1, v___f_218_);
lean_ctor_set(v___x_216_, 0, v___x_222_);
v___x_227_ = v___x_216_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___f_218_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v___f_225_);
lean_ctor_set(v_reuseFailAlloc_247_, 3, v___f_224_);
lean_ctor_set(v_reuseFailAlloc_247_, 4, v___f_223_);
v___x_227_ = v_reuseFailAlloc_247_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; 
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v___f_219_);
lean_ctor_set(v___x_209_, 0, v___x_227_);
v___x_229_ = v___x_209_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v___f_219_);
v___x_229_ = v_reuseFailAlloc_246_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_array_get_size(v_data_184_);
v___x_232_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0));
v___x_233_ = lean_nat_dec_lt(v___x_230_, v___x_231_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
lean_dec_ref(v___x_229_);
lean_dec_ref(v_data_184_);
lean_dec_ref(v_f_183_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
return v___x_234_;
}
else
{
lean_object* v___f_235_; uint8_t v___x_236_; 
v___f_235_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_235_, 0, v_f_183_);
v___x_236_ = lean_nat_dec_le(v___x_231_, v___x_231_);
if (v___x_236_ == 0)
{
if (v___x_233_ == 0)
{
lean_object* v___x_237_; 
lean_dec_ref(v___f_235_);
lean_dec_ref(v___x_229_);
lean_dec_ref(v_data_184_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_232_);
return v___x_237_;
}
else
{
size_t v___x_238_; size_t v___x_239_; lean_object* v___x_359__overap_240_; lean_object* v___x_241_; 
v___x_238_ = ((size_t)0ULL);
v___x_239_ = lean_usize_of_nat(v___x_231_);
v___x_359__overap_240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_229_, v___f_235_, v_data_184_, v___x_238_, v___x_239_, v___x_232_);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
v___x_241_ = lean_apply_5(v___x_359__overap_240_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, lean_box(0));
return v___x_241_;
}
}
else
{
size_t v___x_242_; size_t v___x_243_; lean_object* v___x_364__overap_244_; lean_object* v___x_245_; 
v___x_242_ = ((size_t)0ULL);
v___x_243_ = lean_usize_of_nat(v___x_231_);
v___x_364__overap_244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_229_, v___f_235_, v_data_184_, v___x_242_, v___x_243_, v___x_232_);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
v___x_245_ = lean_apply_5(v___x_364__overap_244_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, lean_box(0));
return v___x_245_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___boxed(lean_object* v_f_252_, lean_object* v_data_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Compiler_LCNF_Probe_filter___redArg(v_f_252_, v_data_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
lean_dec(v_a_257_);
lean_dec_ref(v_a_256_);
lean_dec(v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter(lean_object* v_00_u03b1_260_, lean_object* v_f_261_, lean_object* v_data_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_){
_start:
{
lean_object* v___x_268_; lean_object* v_toApplicative_269_; lean_object* v_toFunctor_270_; lean_object* v_toSeq_271_; lean_object* v_toSeqLeft_272_; lean_object* v_toSeqRight_273_; lean_object* v___f_274_; lean_object* v___f_275_; lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___x_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v_toApplicative_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_328_; 
v___x_268_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_269_ = lean_ctor_get(v___x_268_, 0);
v_toFunctor_270_ = lean_ctor_get(v_toApplicative_269_, 0);
v_toSeq_271_ = lean_ctor_get(v_toApplicative_269_, 2);
v_toSeqLeft_272_ = lean_ctor_get(v_toApplicative_269_, 3);
v_toSeqRight_273_ = lean_ctor_get(v_toApplicative_269_, 4);
v___f_274_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_275_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_270_, 2);
v___f_276_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_276_, 0, v_toFunctor_270_);
v___f_277_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_277_, 0, v_toFunctor_270_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___f_276_);
lean_ctor_set(v___x_278_, 1, v___f_277_);
lean_inc(v_toSeqRight_273_);
v___f_279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_279_, 0, v_toSeqRight_273_);
lean_inc(v_toSeqLeft_272_);
v___f_280_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_280_, 0, v_toSeqLeft_272_);
lean_inc(v_toSeq_271_);
v___f_281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_281_, 0, v_toSeq_271_);
v___x_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_282_, 0, v___x_278_);
lean_ctor_set(v___x_282_, 1, v___f_274_);
lean_ctor_set(v___x_282_, 2, v___f_281_);
lean_ctor_set(v___x_282_, 3, v___f_280_);
lean_ctor_set(v___x_282_, 4, v___f_279_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___f_275_);
v___x_284_ = l_StateRefT_x27_instMonad___redArg(v___x_283_);
v_toApplicative_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v___x_284_, 1);
lean_dec(v_unused_329_);
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_328_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_toApplicative_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_328_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_toFunctor_289_; lean_object* v_toSeq_290_; lean_object* v_toSeqLeft_291_; lean_object* v_toSeqRight_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_326_; 
v_toFunctor_289_ = lean_ctor_get(v_toApplicative_285_, 0);
v_toSeq_290_ = lean_ctor_get(v_toApplicative_285_, 2);
v_toSeqLeft_291_ = lean_ctor_get(v_toApplicative_285_, 3);
v_toSeqRight_292_ = lean_ctor_get(v_toApplicative_285_, 4);
v_isSharedCheck_326_ = !lean_is_exclusive(v_toApplicative_285_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v_toApplicative_285_, 1);
lean_dec(v_unused_327_);
v___x_294_ = v_toApplicative_285_;
v_isShared_295_ = v_isSharedCheck_326_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_toSeqRight_292_);
lean_inc(v_toSeqLeft_291_);
lean_inc(v_toSeq_290_);
lean_inc(v_toFunctor_289_);
lean_dec(v_toApplicative_285_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_326_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___f_296_; lean_object* v___f_297_; lean_object* v___f_298_; lean_object* v___f_299_; lean_object* v___x_300_; lean_object* v___f_301_; lean_object* v___f_302_; lean_object* v___f_303_; lean_object* v___x_305_; 
v___f_296_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_297_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_289_);
v___f_298_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_298_, 0, v_toFunctor_289_);
v___f_299_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_299_, 0, v_toFunctor_289_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___f_298_);
lean_ctor_set(v___x_300_, 1, v___f_299_);
v___f_301_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_301_, 0, v_toSeqRight_292_);
v___f_302_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_302_, 0, v_toSeqLeft_291_);
v___f_303_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_303_, 0, v_toSeq_290_);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 4, v___f_301_);
lean_ctor_set(v___x_294_, 3, v___f_302_);
lean_ctor_set(v___x_294_, 2, v___f_303_);
lean_ctor_set(v___x_294_, 1, v___f_296_);
lean_ctor_set(v___x_294_, 0, v___x_300_);
v___x_305_ = v___x_294_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___f_296_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v___f_303_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v___f_302_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v___f_301_);
v___x_305_ = v_reuseFailAlloc_325_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___f_297_);
lean_ctor_set(v___x_287_, 0, v___x_305_);
v___x_307_ = v___x_287_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___f_297_);
v___x_307_ = v_reuseFailAlloc_324_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_array_get_size(v_data_262_);
v___x_310_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0));
v___x_311_ = lean_nat_dec_lt(v___x_308_, v___x_309_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
lean_dec_ref(v___x_307_);
lean_dec_ref(v_data_262_);
lean_dec_ref(v_f_261_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
return v___x_312_;
}
else
{
lean_object* v___f_313_; uint8_t v___x_314_; 
v___f_313_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_313_, 0, v_f_261_);
v___x_314_ = lean_nat_dec_le(v___x_309_, v___x_309_);
if (v___x_314_ == 0)
{
if (v___x_311_ == 0)
{
lean_object* v___x_315_; 
lean_dec_ref(v___f_313_);
lean_dec_ref(v___x_307_);
lean_dec_ref(v_data_262_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_310_);
return v___x_315_;
}
else
{
size_t v___x_316_; size_t v___x_317_; lean_object* v___x_448__overap_318_; lean_object* v___x_319_; 
v___x_316_ = ((size_t)0ULL);
v___x_317_ = lean_usize_of_nat(v___x_309_);
v___x_448__overap_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_307_, v___f_313_, v_data_262_, v___x_316_, v___x_317_, v___x_310_);
lean_inc(v_a_266_);
lean_inc_ref(v_a_265_);
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
v___x_319_ = lean_apply_5(v___x_448__overap_318_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, lean_box(0));
return v___x_319_;
}
}
else
{
size_t v___x_320_; size_t v___x_321_; lean_object* v___x_451__overap_322_; lean_object* v___x_323_; 
v___x_320_ = ((size_t)0ULL);
v___x_321_ = lean_usize_of_nat(v___x_309_);
v___x_451__overap_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_307_, v___f_313_, v_data_262_, v___x_320_, v___x_321_, v___x_310_);
lean_inc(v_a_266_);
lean_inc_ref(v_a_265_);
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
v___x_323_ = lean_apply_5(v___x_451__overap_322_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, lean_box(0));
return v___x_323_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___boxed(lean_object* v_00_u03b1_330_, lean_object* v_f_331_, lean_object* v_data_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Compiler_LCNF_Probe_filter(v_00_u03b1_330_, v_f_331_, v_data_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_338_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(lean_object* v_inst_339_, lean_object* v_x1_340_, lean_object* v_x2_341_){
_start:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_apply_2(v_inst_339_, v_x1_340_, v_x2_341_);
v___x_343_ = lean_unbox(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed(lean_object* v_inst_344_, lean_object* v_x1_345_, lean_object* v_x2_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(v_inst_344_, v_x1_345_, v_x2_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg(lean_object* v_inst_349_, lean_object* v_data_350_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_352_ = lean_array_get_size(v_data_350_);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_nat_dec_eq(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___f_355_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___y_364_; uint8_t v___x_366_; 
v___f_355_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_355_, 0, v_inst_349_);
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = lean_nat_sub(v___x_352_, v___x_361_);
v___x_366_ = lean_nat_dec_le(v___x_353_, v___x_362_);
if (v___x_366_ == 0)
{
lean_inc(v___x_362_);
v___y_364_ = v___x_362_;
goto v___jp_363_;
}
else
{
v___y_364_ = v___x_353_;
goto v___jp_363_;
}
v___jp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_355_, v___x_352_, v_data_350_, v___y_357_, v___y_358_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_358_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
v___jp_363_:
{
uint8_t v___x_365_; 
v___x_365_ = lean_nat_dec_le(v___y_364_, v___x_362_);
if (v___x_365_ == 0)
{
lean_dec(v___x_362_);
lean_inc(v___y_364_);
v___y_357_ = v___y_364_;
v___y_358_ = v___y_364_;
goto v___jp_356_;
}
else
{
v___y_357_ = v___y_364_;
v___y_358_ = v___x_362_;
goto v___jp_356_;
}
}
}
else
{
lean_object* v___x_367_; 
lean_dec_ref(v_inst_349_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_data_350_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg___boxed(lean_object* v_inst_368_, lean_object* v_data_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg(v_inst_368_, v_data_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted(lean_object* v_00_u03b1_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_data_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_382_ = lean_array_get_size(v_data_376_);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_nat_dec_eq(v___x_382_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___f_385_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___y_394_; uint8_t v___x_396_; 
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_385_, 0, v_inst_375_);
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = lean_nat_sub(v___x_382_, v___x_391_);
v___x_396_ = lean_nat_dec_le(v___x_383_, v___x_392_);
if (v___x_396_ == 0)
{
lean_inc(v___x_392_);
v___y_394_ = v___x_392_;
goto v___jp_393_;
}
else
{
v___y_394_ = v___x_383_;
goto v___jp_393_;
}
v___jp_386_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_385_, v___x_382_, v_data_376_, v___y_387_, v___y_388_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_388_);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
v___jp_393_:
{
uint8_t v___x_395_; 
v___x_395_ = lean_nat_dec_le(v___y_394_, v___x_392_);
if (v___x_395_ == 0)
{
lean_dec(v___x_392_);
lean_inc(v___y_394_);
v___y_387_ = v___y_394_;
v___y_388_ = v___y_394_;
goto v___jp_386_;
}
else
{
v___y_387_ = v___y_394_;
v___y_388_ = v___x_392_;
goto v___jp_386_;
}
}
}
else
{
lean_object* v___x_397_; 
lean_dec_ref(v_inst_375_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v_data_376_);
return v___x_397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___boxed(lean_object* v_00_u03b1_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_data_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Compiler_LCNF_Probe_sorted(v_00_u03b1_398_, v_inst_399_, v_inst_400_, v_inst_401_, v_data_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_inst_399_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(uint8_t v_pu_409_, lean_object* v_x_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = l_Lean_Compiler_LCNF_Decl_size(v_pu_409_, v_x_410_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_x_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed(lean_object* v_pu_413_, lean_object* v_x_414_){
_start:
{
uint8_t v_pu_boxed_415_; lean_object* v_res_416_; 
v_pu_boxed_415_ = lean_unbox(v_pu_413_);
v_res_416_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(v_pu_boxed_415_, v_x_414_);
return v_res_416_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_fst_419_; lean_object* v_snd_420_; lean_object* v_fst_421_; lean_object* v_snd_422_; uint8_t v___x_423_; 
v_fst_419_ = lean_ctor_get(v_x_417_, 0);
v_snd_420_ = lean_ctor_get(v_x_417_, 1);
v_fst_421_ = lean_ctor_get(v_x_418_, 0);
v_snd_422_ = lean_ctor_get(v_x_418_, 1);
v___x_423_ = lean_nat_dec_eq(v_fst_419_, v_fst_421_);
if (v___x_423_ == 0)
{
uint8_t v___x_424_; 
v___x_424_ = lean_nat_dec_lt(v_fst_419_, v_fst_421_);
return v___x_424_;
}
else
{
lean_object* v_toSignature_425_; lean_object* v_toSignature_426_; lean_object* v_name_427_; lean_object* v_name_428_; uint8_t v___x_429_; 
v_toSignature_425_ = lean_ctor_get(v_snd_420_, 0);
v_toSignature_426_ = lean_ctor_get(v_snd_422_, 0);
v_name_427_ = lean_ctor_get(v_toSignature_425_, 0);
v_name_428_ = lean_ctor_get(v_toSignature_426_, 0);
v___x_429_ = l_Lean_Name_lt(v_name_427_, v_name_428_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1___boxed(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(v_x_430_, v_x_431_);
lean_dec_ref(v_x_431_);
lean_dec_ref(v_x_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(uint8_t v_pu_454_, lean_object* v_decls_455_){
_start:
{
lean_object* v___x_457_; lean_object* v___f_458_; lean_object* v___x_459_; size_t v_sz_460_; size_t v___x_461_; lean_object* v_decls_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_457_ = lean_box(v_pu_454_);
v___f_458_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_458_, 0, v___x_457_);
v___x_459_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v_sz_460_ = lean_array_size(v_decls_455_);
v___x_461_ = ((size_t)0ULL);
v_decls_462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_459_, v___f_458_, v_sz_460_, v___x_461_, v_decls_455_);
v___x_463_ = lean_array_get_size(v_decls_462_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_nat_dec_eq(v___x_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___f_466_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___y_475_; uint8_t v___x_477_; 
v___f_466_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10));
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_sub(v___x_463_, v___x_472_);
v___x_477_ = lean_nat_dec_le(v___x_464_, v___x_473_);
if (v___x_477_ == 0)
{
lean_inc(v___x_473_);
v___y_475_ = v___x_473_;
goto v___jp_474_;
}
else
{
v___y_475_ = v___x_464_;
goto v___jp_474_;
}
v___jp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_466_, v___x_463_, v_decls_462_, v___y_468_, v___y_469_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
v___jp_474_:
{
uint8_t v___x_476_; 
v___x_476_ = lean_nat_dec_le(v___y_475_, v___x_473_);
if (v___x_476_ == 0)
{
lean_dec(v___x_473_);
lean_inc(v___y_475_);
v___y_468_ = v___y_475_;
v___y_469_ = v___y_475_;
goto v___jp_467_;
}
else
{
v___y_468_ = v___y_475_;
v___y_469_ = v___x_473_;
goto v___jp_467_;
}
}
}
else
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_decls_462_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___boxed(lean_object* v_pu_479_, lean_object* v_decls_480_, lean_object* v_a_481_){
_start:
{
uint8_t v_pu_boxed_482_; lean_object* v_res_483_; 
v_pu_boxed_482_ = lean_unbox(v_pu_479_);
v_res_483_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(v_pu_boxed_482_, v_decls_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize(uint8_t v_pu_484_, lean_object* v_decls_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___x_491_; lean_object* v___f_492_; lean_object* v___x_493_; size_t v_sz_494_; size_t v___x_495_; lean_object* v_decls_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_491_ = lean_box(v_pu_484_);
v___f_492_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_492_, 0, v___x_491_);
v___x_493_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v_sz_494_ = lean_array_size(v_decls_485_);
v___x_495_ = ((size_t)0ULL);
v_decls_496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_493_, v___f_492_, v_sz_494_, v___x_495_, v_decls_485_);
v___x_497_ = lean_array_get_size(v_decls_496_);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_nat_dec_eq(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___f_500_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___y_509_; uint8_t v___x_511_; 
v___f_500_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10));
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_sub(v___x_497_, v___x_506_);
v___x_511_ = lean_nat_dec_le(v___x_498_, v___x_507_);
if (v___x_511_ == 0)
{
lean_inc(v___x_507_);
v___y_509_ = v___x_507_;
goto v___jp_508_;
}
else
{
v___y_509_ = v___x_498_;
goto v___jp_508_;
}
v___jp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_500_, v___x_497_, v_decls_496_, v___y_502_, v___y_503_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_503_);
v___x_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
return v___x_505_;
}
v___jp_508_:
{
uint8_t v___x_510_; 
v___x_510_ = lean_nat_dec_le(v___y_509_, v___x_507_);
if (v___x_510_ == 0)
{
lean_dec(v___x_507_);
lean_inc(v___y_509_);
v___y_502_ = v___y_509_;
v___y_503_ = v___y_509_;
goto v___jp_501_;
}
else
{
v___y_502_ = v___y_509_;
v___y_503_ = v___x_507_;
goto v___jp_501_;
}
}
}
else
{
lean_object* v___x_512_; 
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v_decls_496_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___boxed(lean_object* v_pu_513_, lean_object* v_decls_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
uint8_t v_pu_boxed_520_; lean_object* v_res_521_; 
v_pu_boxed_520_ = lean_unbox(v_pu_513_);
v_res_521_ = l_Lean_Compiler_LCNF_Probe_sortedBySize(v_pu_boxed_520_, v_decls_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_a_524_, lean_object* v_x_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___y_533_; lean_object* v___y_537_; lean_object* v___x_540_; 
lean_inc(v_a_524_);
lean_inc_ref(v_inst_523_);
lean_inc_ref(v_inst_522_);
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_522_, v_inst_523_, v___y_526_, v_a_524_);
if (lean_obj_tag(v___x_540_) == 1)
{
lean_object* v_val_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___y_545_; lean_object* v_i_546_; lean_object* v___y_551_; lean_object* v___y_561_; lean_object* v_i_562_; lean_object* v___x_576_; 
v_val_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_val_541_, v___x_542_);
lean_dec(v_val_541_);
lean_inc(v_a_524_);
lean_inc_ref(v_inst_523_);
lean_inc_ref(v_inst_522_);
v___x_576_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_522_, v_inst_523_, v___y_526_, v_a_524_);
switch(lean_obj_tag(v___x_576_))
{
case 0:
{
lean_object* v_index_577_; lean_object* v_size_578_; lean_object* v___x_579_; 
lean_dec_ref(v_inst_523_);
lean_dec_ref(v_inst_522_);
v_index_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_index_577_);
lean_dec_ref_known(v___x_576_, 3);
v_size_578_ = lean_ctor_get(v___y_526_, 0);
lean_inc(v_size_578_);
v___x_579_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_526_, v_size_578_, v_index_577_, v_a_524_, v___x_543_);
lean_dec(v_index_577_);
v___y_537_ = v___x_579_;
goto v___jp_536_;
}
case 1:
{
lean_object* v_index_580_; lean_object* v_size_581_; lean_object* v_keyArray_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_index_580_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_index_580_);
lean_dec_ref_known(v___x_576_, 1);
v_size_581_ = lean_ctor_get(v___y_526_, 0);
v_keyArray_582_ = lean_ctor_get(v___y_526_, 1);
v___x_583_ = lean_nat_add(v_size_581_, v___x_542_);
v___x_584_ = lean_array_get_size(v_keyArray_582_);
v___x_585_ = lean_nat_dec_lt(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec(v___x_583_);
lean_dec(v_index_580_);
goto v___jp_566_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_586_ = lean_unsigned_to_nat(4u);
v___x_587_ = lean_nat_mul(v___x_583_, v___x_586_);
v___x_588_ = lean_unsigned_to_nat(3u);
v___x_589_ = lean_nat_mul(v___x_584_, v___x_588_);
v___x_590_ = lean_nat_dec_le(v___x_587_, v___x_589_);
lean_dec(v___x_589_);
lean_dec(v___x_587_);
if (v___x_590_ == 0)
{
lean_dec(v___x_583_);
lean_dec(v_index_580_);
goto v___jp_566_;
}
else
{
lean_object* v___x_591_; 
lean_dec_ref(v_inst_523_);
lean_dec_ref(v_inst_522_);
v___x_591_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_526_, v___x_583_, v_index_580_, v_a_524_, v___x_543_);
lean_dec(v_index_580_);
v___y_537_ = v___x_591_;
goto v___jp_536_;
}
}
}
default: 
{
lean_object* v_size_592_; lean_object* v_keyArray_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_size_592_ = lean_ctor_get(v___y_526_, 0);
v_keyArray_593_ = lean_ctor_get(v___y_526_, 1);
v___x_594_ = lean_nat_add(v_size_592_, v___x_542_);
v___x_595_ = lean_array_get_size(v_keyArray_593_);
v___x_596_ = lean_nat_dec_lt(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; 
lean_dec(v___x_594_);
lean_inc_ref(v_inst_523_);
lean_inc_ref(v_inst_522_);
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_522_, v_inst_523_, v___y_526_);
v___y_551_ = v___x_597_;
goto v___jp_550_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_598_ = lean_unsigned_to_nat(4u);
v___x_599_ = lean_nat_mul(v___x_594_, v___x_598_);
lean_dec(v___x_594_);
v___x_600_ = lean_unsigned_to_nat(3u);
v___x_601_ = lean_nat_mul(v___x_595_, v___x_600_);
v___x_602_ = lean_nat_dec_le(v___x_599_, v___x_601_);
lean_dec(v___x_601_);
lean_dec(v___x_599_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
lean_inc_ref(v_inst_523_);
lean_inc_ref(v_inst_522_);
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_522_, v_inst_523_, v___y_526_);
v___y_551_ = v___x_603_;
goto v___jp_550_;
}
else
{
v___y_551_ = v___y_526_;
goto v___jp_550_;
}
}
}
}
v___jp_544_:
{
lean_object* v_size_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_size_547_ = lean_ctor_get(v___y_545_, 0);
v___x_548_ = lean_nat_add(v_size_547_, v___x_542_);
v___x_549_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_545_, v___x_548_, v_i_546_, v_a_524_, v___x_543_);
lean_dec(v_i_546_);
v___y_537_ = v___x_549_;
goto v___jp_536_;
}
v___jp_550_:
{
lean_object* v___x_552_; 
lean_inc(v_a_524_);
v___x_552_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_522_, v_inst_523_, v___y_551_, v_a_524_);
switch(lean_obj_tag(v___x_552_))
{
case 0:
{
lean_object* v_index_553_; lean_object* v_size_554_; lean_object* v___x_555_; 
v_index_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_index_553_);
lean_dec_ref_known(v___x_552_, 3);
v_size_554_ = lean_ctor_get(v___y_551_, 0);
lean_inc(v_size_554_);
v___x_555_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_551_, v_size_554_, v_index_553_, v_a_524_, v___x_543_);
lean_dec(v_index_553_);
v___y_537_ = v___x_555_;
goto v___jp_536_;
}
case 1:
{
lean_object* v_index_556_; 
v_index_556_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_index_556_);
lean_dec_ref_known(v___x_552_, 1);
v___y_545_ = v___y_551_;
v_i_546_ = v_index_556_;
goto v___jp_544_;
}
default: 
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_551_, v___x_557_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_index_559_; 
v_index_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_index_559_);
lean_dec_ref_known(v___x_558_, 1);
v___y_545_ = v___y_551_;
v_i_546_ = v_index_559_;
goto v___jp_544_;
}
else
{
lean_dec(v___x_543_);
lean_dec(v_a_524_);
v___y_537_ = v___y_551_;
goto v___jp_536_;
}
}
}
}
v___jp_560_:
{
lean_object* v_size_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_size_563_ = lean_ctor_get(v___y_561_, 0);
v___x_564_ = lean_nat_add(v_size_563_, v___x_542_);
v___x_565_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_561_, v___x_564_, v_i_562_, v_a_524_, v___x_543_);
lean_dec(v_i_562_);
v___y_537_ = v___x_565_;
goto v___jp_536_;
}
v___jp_566_:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_inc_ref(v_inst_523_);
lean_inc_ref(v_inst_522_);
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_522_, v_inst_523_, v___y_526_);
lean_inc(v_a_524_);
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_522_, v_inst_523_, v___x_567_, v_a_524_);
switch(lean_obj_tag(v___x_568_))
{
case 0:
{
lean_object* v_index_569_; lean_object* v_size_570_; lean_object* v___x_571_; 
v_index_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_index_569_);
lean_dec_ref_known(v___x_568_, 3);
v_size_570_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_size_570_);
v___x_571_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_567_, v_size_570_, v_index_569_, v_a_524_, v___x_543_);
lean_dec(v_index_569_);
v___y_537_ = v___x_571_;
goto v___jp_536_;
}
case 1:
{
lean_object* v_index_572_; 
v_index_572_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_index_572_);
lean_dec_ref_known(v___x_568_, 1);
v___y_561_ = v___x_567_;
v_i_562_ = v_index_572_;
goto v___jp_560_;
}
default: 
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_567_, v___x_573_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_index_575_; 
v_index_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_index_575_);
lean_dec_ref_known(v___x_574_, 1);
v___y_561_ = v___x_567_;
v_i_562_ = v_index_575_;
goto v___jp_560_;
}
else
{
lean_dec(v___x_543_);
lean_dec(v_a_524_);
v___y_537_ = v___x_567_;
goto v___jp_536_;
}
}
}
}
}
else
{
lean_object* v___x_604_; lean_object* v___y_606_; lean_object* v_i_607_; lean_object* v___y_612_; lean_object* v___y_622_; lean_object* v_i_623_; lean_object* v___x_637_; 
lean_dec(v___x_540_);
v___x_604_ = lean_unsigned_to_nat(1u);
lean_inc(v_a_524_);
lean_inc_ref(v_inst_523_);
lean_inc_ref(v_inst_522_);
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_522_, v_inst_523_, v___y_526_, v_a_524_);
switch(lean_obj_tag(v___x_637_))
{
case 0:
{
lean_object* v_index_638_; lean_object* v_size_639_; lean_object* v___x_640_; 
lean_dec_ref(v_inst_523_);
lean_dec_ref(v_inst_522_);
v_index_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_index_638_);
lean_dec_ref_known(v___x_637_, 3);
v_size_639_ = lean_ctor_get(v___y_526_, 0);
lean_inc(v_size_639_);
v___x_640_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_526_, v_size_639_, v_index_638_, v_a_524_, v___x_604_);
lean_dec(v_index_638_);
v___y_533_ = v___x_640_;
goto v___jp_532_;
}
case 1:
{
lean_object* v_index_641_; lean_object* v_size_642_; lean_object* v_keyArray_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_index_641_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_index_641_);
lean_dec_ref_known(v___x_637_, 1);
v_size_642_ = lean_ctor_get(v___y_526_, 0);
v_keyArray_643_ = lean_ctor_get(v___y_526_, 1);
v___x_644_ = lean_nat_add(v_size_642_, v___x_604_);
v___x_645_ = lean_array_get_size(v_keyArray_643_);
v___x_646_ = lean_nat_dec_lt(v___x_644_, v___x_645_);
if (v___x_646_ == 0)
{
lean_dec(v___x_644_);
lean_dec(v_index_641_);
goto v___jp_627_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_647_ = lean_unsigned_to_nat(4u);
v___x_648_ = lean_nat_mul(v___x_644_, v___x_647_);
v___x_649_ = lean_unsigned_to_nat(3u);
v___x_650_ = lean_nat_mul(v___x_645_, v___x_649_);
v___x_651_ = lean_nat_dec_le(v___x_648_, v___x_650_);
lean_dec(v___x_650_);
lean_dec(v___x_648_);
if (v___x_651_ == 0)
{
lean_dec(v___x_644_);
lean_dec(v_index_641_);
goto v___jp_627_;
}
else
{
lean_object* v___x_652_; 
lean_dec_ref(v_inst_523_);
lean_dec_ref(v_inst_522_);
v___x_652_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_526_, v___x_644_, v_index_641_, v_a_524_, v___x_604_);
lean_dec(v_index_641_);
v___y_533_ = v___x_652_;
goto v___jp_532_;
}
}
}
default: 
{
lean_object* v_size_653_; lean_object* v_keyArray_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_size_653_ = lean_ctor_get(v___y_526_, 0);
v_keyArray_654_ = lean_ctor_get(v___y_526_, 1);
v___x_655_ = lean_nat_add(v_size_653_, v___x_604_);
v___x_656_ = lean_array_get_size(v_keyArray_654_);
v___x_657_ = lean_nat_dec_lt(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec(v___x_655_);
lean_inc_ref(v_inst_523_);
lean_inc_ref(v_inst_522_);
v___x_658_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_522_, v_inst_523_, v___y_526_);
v___y_612_ = v___x_658_;
goto v___jp_611_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_659_ = lean_unsigned_to_nat(4u);
v___x_660_ = lean_nat_mul(v___x_655_, v___x_659_);
lean_dec(v___x_655_);
v___x_661_ = lean_unsigned_to_nat(3u);
v___x_662_ = lean_nat_mul(v___x_656_, v___x_661_);
v___x_663_ = lean_nat_dec_le(v___x_660_, v___x_662_);
lean_dec(v___x_662_);
lean_dec(v___x_660_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_inc_ref(v_inst_523_);
lean_inc_ref(v_inst_522_);
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_522_, v_inst_523_, v___y_526_);
v___y_612_ = v___x_664_;
goto v___jp_611_;
}
else
{
v___y_612_ = v___y_526_;
goto v___jp_611_;
}
}
}
}
v___jp_605_:
{
lean_object* v_size_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_size_608_ = lean_ctor_get(v___y_606_, 0);
v___x_609_ = lean_nat_add(v_size_608_, v___x_604_);
v___x_610_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_606_, v___x_609_, v_i_607_, v_a_524_, v___x_604_);
lean_dec(v_i_607_);
v___y_533_ = v___x_610_;
goto v___jp_532_;
}
v___jp_611_:
{
lean_object* v___x_613_; 
lean_inc(v_a_524_);
v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_522_, v_inst_523_, v___y_612_, v_a_524_);
switch(lean_obj_tag(v___x_613_))
{
case 0:
{
lean_object* v_index_614_; lean_object* v_size_615_; lean_object* v___x_616_; 
v_index_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_index_614_);
lean_dec_ref_known(v___x_613_, 3);
v_size_615_ = lean_ctor_get(v___y_612_, 0);
lean_inc(v_size_615_);
v___x_616_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_612_, v_size_615_, v_index_614_, v_a_524_, v___x_604_);
lean_dec(v_index_614_);
v___y_533_ = v___x_616_;
goto v___jp_532_;
}
case 1:
{
lean_object* v_index_617_; 
v_index_617_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_index_617_);
lean_dec_ref_known(v___x_613_, 1);
v___y_606_ = v___y_612_;
v_i_607_ = v_index_617_;
goto v___jp_605_;
}
default: 
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_612_, v___x_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_index_620_; 
v_index_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_index_620_);
lean_dec_ref_known(v___x_619_, 1);
v___y_606_ = v___y_612_;
v_i_607_ = v_index_620_;
goto v___jp_605_;
}
else
{
lean_dec(v_a_524_);
v___y_533_ = v___y_612_;
goto v___jp_532_;
}
}
}
}
v___jp_621_:
{
lean_object* v_size_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_size_624_ = lean_ctor_get(v___y_622_, 0);
v___x_625_ = lean_nat_add(v_size_624_, v___x_604_);
v___x_626_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_622_, v___x_625_, v_i_623_, v_a_524_, v___x_604_);
lean_dec(v_i_623_);
v___y_533_ = v___x_626_;
goto v___jp_532_;
}
v___jp_627_:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_inc_ref(v_inst_523_);
lean_inc_ref(v_inst_522_);
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_522_, v_inst_523_, v___y_526_);
lean_inc(v_a_524_);
v___x_629_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_522_, v_inst_523_, v___x_628_, v_a_524_);
switch(lean_obj_tag(v___x_629_))
{
case 0:
{
lean_object* v_index_630_; lean_object* v_size_631_; lean_object* v___x_632_; 
v_index_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_index_630_);
lean_dec_ref_known(v___x_629_, 3);
v_size_631_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_size_631_);
v___x_632_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_628_, v_size_631_, v_index_630_, v_a_524_, v___x_604_);
lean_dec(v_index_630_);
v___y_533_ = v___x_632_;
goto v___jp_532_;
}
case 1:
{
lean_object* v_index_633_; 
v_index_633_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_index_633_);
lean_dec_ref_known(v___x_629_, 1);
v___y_622_ = v___x_628_;
v_i_623_ = v_index_633_;
goto v___jp_621_;
}
default: 
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_628_, v___x_634_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_index_636_; 
v_index_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_index_636_);
lean_dec_ref_known(v___x_635_, 1);
v___y_622_ = v___x_628_;
v_i_623_ = v_index_636_;
goto v___jp_621_;
}
else
{
lean_dec(v_a_524_);
v___y_533_ = v___x_628_;
goto v___jp_532_;
}
}
}
}
}
v___jp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v___y_533_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
v___jp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___y_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed(lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_a_667_, lean_object* v_x_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(v_inst_665_, v_inst_666_, v_a_667_, v_x_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__1(lean_object* v_x1_676_, lean_object* v_x2_677_, lean_object* v_x3_678_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_x2_677_);
lean_ctor_set(v___x_679_, 1, v_x3_678_);
v___x_680_ = lean_array_push(v_x1_676_, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg(lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_data_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; lean_object* v_toApplicative_691_; lean_object* v_toFunctor_692_; lean_object* v_toSeq_693_; lean_object* v_toSeqLeft_694_; lean_object* v_toSeqRight_695_; lean_object* v___f_696_; lean_object* v___f_697_; lean_object* v___f_698_; lean_object* v___f_699_; lean_object* v___x_700_; lean_object* v___f_701_; lean_object* v___f_702_; lean_object* v___f_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_toApplicative_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_772_; 
v___x_690_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_691_ = lean_ctor_get(v___x_690_, 0);
v_toFunctor_692_ = lean_ctor_get(v_toApplicative_691_, 0);
v_toSeq_693_ = lean_ctor_get(v_toApplicative_691_, 2);
v_toSeqLeft_694_ = lean_ctor_get(v_toApplicative_691_, 3);
v_toSeqRight_695_ = lean_ctor_get(v_toApplicative_691_, 4);
v___f_696_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_697_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_692_, 2);
v___f_698_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_698_, 0, v_toFunctor_692_);
v___f_699_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_699_, 0, v_toFunctor_692_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___f_698_);
lean_ctor_set(v___x_700_, 1, v___f_699_);
lean_inc(v_toSeqRight_695_);
v___f_701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_701_, 0, v_toSeqRight_695_);
lean_inc(v_toSeqLeft_694_);
v___f_702_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_702_, 0, v_toSeqLeft_694_);
lean_inc(v_toSeq_693_);
v___f_703_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_703_, 0, v_toSeq_693_);
v___x_704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_704_, 0, v___x_700_);
lean_ctor_set(v___x_704_, 1, v___f_696_);
lean_ctor_set(v___x_704_, 2, v___f_703_);
lean_ctor_set(v___x_704_, 3, v___f_702_);
lean_ctor_set(v___x_704_, 4, v___f_701_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v___f_697_);
v___x_706_ = l_StateRefT_x27_instMonad___redArg(v___x_705_);
v_toApplicative_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v___x_706_, 1);
lean_dec(v_unused_773_);
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_772_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_toApplicative_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_772_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_toFunctor_711_; lean_object* v_toSeq_712_; lean_object* v_toSeqLeft_713_; lean_object* v_toSeqRight_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_770_; 
v_toFunctor_711_ = lean_ctor_get(v_toApplicative_707_, 0);
v_toSeq_712_ = lean_ctor_get(v_toApplicative_707_, 2);
v_toSeqLeft_713_ = lean_ctor_get(v_toApplicative_707_, 3);
v_toSeqRight_714_ = lean_ctor_get(v_toApplicative_707_, 4);
v_isSharedCheck_770_ = !lean_is_exclusive(v_toApplicative_707_);
if (v_isSharedCheck_770_ == 0)
{
lean_object* v_unused_771_; 
v_unused_771_ = lean_ctor_get(v_toApplicative_707_, 1);
lean_dec(v_unused_771_);
v___x_716_ = v_toApplicative_707_;
v_isShared_717_ = v_isSharedCheck_770_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_toSeqRight_714_);
lean_inc(v_toSeqLeft_713_);
lean_inc(v_toSeq_712_);
lean_inc(v_toFunctor_711_);
lean_dec(v_toApplicative_707_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_770_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___f_720_; lean_object* v___f_721_; lean_object* v___f_722_; lean_object* v___x_723_; lean_object* v___f_724_; lean_object* v___f_725_; lean_object* v___f_726_; lean_object* v___x_728_; 
v___f_718_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_718_, 0, v_inst_682_);
lean_closure_set(v___f_718_, 1, v_inst_683_);
v___f_719_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_720_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_711_);
v___f_721_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_721_, 0, v_toFunctor_711_);
v___f_722_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_722_, 0, v_toFunctor_711_);
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v___f_721_);
lean_ctor_set(v___x_723_, 1, v___f_722_);
v___f_724_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_724_, 0, v_toSeqRight_714_);
v___f_725_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_725_, 0, v_toSeqLeft_713_);
v___f_726_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_726_, 0, v_toSeq_712_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 4, v___f_724_);
lean_ctor_set(v___x_716_, 3, v___f_725_);
lean_ctor_set(v___x_716_, 2, v___f_726_);
lean_ctor_set(v___x_716_, 1, v___f_719_);
lean_ctor_set(v___x_716_, 0, v___x_723_);
v___x_728_ = v___x_716_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___f_719_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v___f_726_);
lean_ctor_set(v_reuseFailAlloc_769_, 3, v___f_725_);
lean_ctor_set(v_reuseFailAlloc_769_, 4, v___f_724_);
v___x_728_ = v_reuseFailAlloc_769_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 1, v___f_720_);
lean_ctor_set(v___x_709_, 0, v___x_728_);
v___x_730_ = v___x_709_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___f_720_);
v___x_730_ = v_reuseFailAlloc_768_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_cellCount_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v_map_742_; size_t v_sz_743_; size_t v___x_744_; lean_object* v___x_1483__overap_745_; lean_object* v___x_746_; 
v___x_731_ = lean_array_get_size(v_data_684_);
v___x_732_ = lean_unsigned_to_nat(4u);
v___x_733_ = lean_nat_mul(v___x_731_, v___x_732_);
v___x_734_ = lean_unsigned_to_nat(2u);
v___x_735_ = lean_nat_add(v___x_733_, v___x_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_unsigned_to_nat(3u);
v___x_737_ = lean_nat_div(v___x_735_, v___x_736_);
lean_dec(v___x_735_);
v_cellCount_738_ = l_Nat_nextPowerOfTwo(v___x_737_);
lean_dec(v___x_737_);
v___x_739_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_738_);
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_738_);
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_738_);
v_map_742_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_map_742_, 0, v___x_739_);
lean_ctor_set(v_map_742_, 1, v___x_740_);
lean_ctor_set(v_map_742_, 2, v___x_741_);
v_sz_743_ = lean_array_size(v_data_684_);
v___x_744_ = ((size_t)0ULL);
v___x_1483__overap_745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_730_, v_data_684_, v___f_718_, v_sz_743_, v___x_744_, v_map_742_);
lean_inc(v_a_688_);
lean_inc_ref(v_a_687_);
lean_inc(v_a_686_);
lean_inc_ref(v_a_685_);
v___x_746_ = lean_apply_5(v___x_1483__overap_745_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, lean_box(0));
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_759_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_759_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_759_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_759_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_size_751_; lean_object* v___f_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v_size_751_ = lean_ctor_get(v_a_747_, 0);
v___f_752_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0));
v___x_753_ = lean_mk_empty_array_with_capacity(v_size_751_);
v___x_754_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_755_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_754_, v___f_752_, v___x_753_, v_a_747_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_755_);
v___x_757_ = v___x_749_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_760_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_746_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_746_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___boxed(lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_data_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_774_, v_inst_775_, v_data_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique(lean_object* v_00_u03b1_783_, lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_data_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_785_, v_inst_786_, v_data_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___boxed(lean_object* v_00_u03b1_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_data_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Compiler_LCNF_Probe_countUnique(v_00_u03b1_794_, v_inst_795_, v_inst_796_, v_inst_797_, v_data_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec_ref(v_inst_795_);
return v_res_804_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(lean_object* v_l_805_, lean_object* v_r_806_){
_start:
{
lean_object* v_snd_807_; lean_object* v_snd_808_; uint8_t v___x_809_; 
v_snd_807_ = lean_ctor_get(v_l_805_, 1);
v_snd_808_ = lean_ctor_get(v_r_806_, 1);
v___x_809_ = lean_nat_dec_lt(v_snd_807_, v_snd_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0___boxed(lean_object* v_l_810_, lean_object* v_r_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(v_l_810_, v_r_811_);
lean_dec_ref(v_r_811_);
lean_dec_ref(v_l_810_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_815_, v_inst_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
v___x_825_ = lean_array_get_size(v_a_824_);
v___x_826_ = lean_unsigned_to_nat(0u);
v___x_827_ = lean_nat_dec_eq(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_845_; 
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v___x_823_, 0);
lean_dec(v_unused_846_);
v___x_829_ = v___x_823_;
v_isShared_830_ = v_isSharedCheck_845_;
goto v_resetjp_828_;
}
else
{
lean_dec(v___x_823_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_845_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___f_831_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___y_842_; uint8_t v___x_844_; 
v___f_831_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_839_ = lean_unsigned_to_nat(1u);
v___x_840_ = lean_nat_sub(v___x_825_, v___x_839_);
v___x_844_ = lean_nat_dec_le(v___x_826_, v___x_840_);
if (v___x_844_ == 0)
{
lean_inc(v___x_840_);
v___y_842_ = v___x_840_;
goto v___jp_841_;
}
else
{
v___y_842_ = v___x_826_;
goto v___jp_841_;
}
v___jp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_831_, v___x_825_, v_a_824_, v___y_833_, v___y_834_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_834_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_835_);
v___x_837_ = v___x_829_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
v___jp_841_:
{
uint8_t v___x_843_; 
v___x_843_ = lean_nat_dec_le(v___y_842_, v___x_840_);
if (v___x_843_ == 0)
{
lean_dec(v___x_840_);
lean_inc(v___y_842_);
v___y_833_ = v___y_842_;
v___y_834_ = v___y_842_;
goto v___jp_832_;
}
else
{
v___y_833_ = v___y_842_;
v___y_834_ = v___x_840_;
goto v___jp_832_;
}
}
}
}
else
{
lean_dec(v_a_824_);
return v___x_823_;
}
}
else
{
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___boxed(lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(v_inst_847_, v_inst_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted(lean_object* v_00_u03b1_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_858_, v_inst_859_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
v___x_869_ = lean_array_get_size(v_a_868_);
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = lean_nat_dec_eq(v___x_869_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_889_; 
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v___x_867_, 0);
lean_dec(v_unused_890_);
v___x_873_ = v___x_867_;
v_isShared_874_ = v_isSharedCheck_889_;
goto v_resetjp_872_;
}
else
{
lean_dec(v___x_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_889_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___f_875_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___y_886_; uint8_t v___x_888_; 
v___f_875_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_883_ = lean_unsigned_to_nat(1u);
v___x_884_ = lean_nat_sub(v___x_869_, v___x_883_);
v___x_888_ = lean_nat_dec_le(v___x_870_, v___x_884_);
if (v___x_888_ == 0)
{
lean_inc(v___x_884_);
v___y_886_ = v___x_884_;
goto v___jp_885_;
}
else
{
v___y_886_ = v___x_870_;
goto v___jp_885_;
}
v___jp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_875_, v___x_869_, v_a_868_, v___y_877_, v___y_878_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_878_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_879_);
v___x_881_ = v___x_873_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
v___jp_885_:
{
uint8_t v___x_887_; 
v___x_887_ = lean_nat_dec_le(v___y_886_, v___x_884_);
if (v___x_887_ == 0)
{
lean_dec(v___x_884_);
lean_inc(v___y_886_);
v___y_877_ = v___y_886_;
v___y_878_ = v___y_886_;
goto v___jp_876_;
}
else
{
v___y_877_ = v___y_886_;
v___y_878_ = v___x_884_;
goto v___jp_876_;
}
}
}
}
else
{
lean_dec(v_a_868_);
return v___x_867_;
}
}
else
{
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___boxed(lean_object* v_00_u03b1_891_, lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_inst_894_, lean_object* v_inst_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted(v_00_u03b1_891_, v_inst_892_, v_inst_893_, v_inst_894_, v_inst_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_inst_895_);
lean_dec_ref(v_inst_892_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(uint8_t v_pu_903_, lean_object* v_c_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
switch(lean_obj_tag(v_c_904_))
{
case 0:
{
lean_object* v_decl_911_; lean_object* v_k_912_; lean_object* v___x_913_; lean_object* v_value_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_decl_911_ = lean_ctor_get(v_c_904_, 0);
lean_inc_ref(v_decl_911_);
v_k_912_ = lean_ctor_get(v_c_904_, 1);
lean_inc_ref(v_k_912_);
lean_dec_ref_known(v_c_904_, 2);
v___x_913_ = lean_st_ref_take(v_a_905_);
v_value_914_ = lean_ctor_get(v_decl_911_, 3);
lean_inc(v_value_914_);
lean_dec_ref(v_decl_911_);
v___x_915_ = lean_array_push(v___x_913_, v_value_914_);
v___x_916_ = lean_st_ref_put(v_a_905_, v___x_915_);
v_c_904_ = v_k_912_;
goto _start;
}
case 1:
{
lean_object* v_decl_918_; lean_object* v_k_919_; lean_object* v_value_920_; lean_object* v___x_921_; 
v_decl_918_ = lean_ctor_get(v_c_904_, 0);
lean_inc_ref(v_decl_918_);
v_k_919_ = lean_ctor_get(v_c_904_, 1);
lean_inc_ref(v_k_919_);
lean_dec_ref_known(v_c_904_, 2);
v_value_920_ = lean_ctor_get(v_decl_918_, 4);
lean_inc_ref(v_value_920_);
lean_dec_ref(v_decl_918_);
v___x_921_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_903_, v_value_920_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_dec_ref_known(v___x_921_, 1);
v_c_904_ = v_k_919_;
goto _start;
}
else
{
lean_dec_ref(v_k_919_);
return v___x_921_;
}
}
case 2:
{
lean_object* v_decl_923_; lean_object* v_k_924_; lean_object* v_value_925_; lean_object* v___x_926_; 
v_decl_923_ = lean_ctor_get(v_c_904_, 0);
lean_inc_ref(v_decl_923_);
v_k_924_ = lean_ctor_get(v_c_904_, 1);
lean_inc_ref(v_k_924_);
lean_dec_ref_known(v_c_904_, 2);
v_value_925_ = lean_ctor_get(v_decl_923_, 4);
lean_inc_ref(v_value_925_);
lean_dec_ref(v_decl_923_);
v___x_926_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_903_, v_value_925_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_dec_ref_known(v___x_926_, 1);
v_c_904_ = v_k_924_;
goto _start;
}
else
{
lean_dec_ref(v_k_924_);
return v___x_926_;
}
}
case 4:
{
lean_object* v_cases_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_950_; 
v_cases_928_ = lean_ctor_get(v_c_904_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_c_904_);
if (v_isSharedCheck_950_ == 0)
{
v___x_930_ = v_c_904_;
v_isShared_931_ = v_isSharedCheck_950_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_cases_928_);
lean_dec(v_c_904_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_950_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_alts_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_alts_932_ = lean_ctor_get(v_cases_928_, 3);
lean_inc_ref(v_alts_932_);
lean_dec_ref(v_cases_928_);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_array_get_size(v_alts_932_);
v___x_935_ = lean_box(0);
v___x_936_ = lean_nat_dec_lt(v___x_933_, v___x_934_);
if (v___x_936_ == 0)
{
lean_object* v___x_938_; 
lean_dec_ref(v_alts_932_);
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 0);
lean_ctor_set(v___x_930_, 0, v___x_935_);
v___x_938_ = v___x_930_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_935_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
uint8_t v___x_940_; 
v___x_940_ = lean_nat_dec_le(v___x_934_, v___x_934_);
if (v___x_940_ == 0)
{
if (v___x_936_ == 0)
{
lean_object* v___x_942_; 
lean_dec_ref(v_alts_932_);
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 0);
lean_ctor_set(v___x_930_, 0, v___x_935_);
v___x_942_ = v___x_930_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_935_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
else
{
size_t v___x_944_; size_t v___x_945_; lean_object* v___x_946_; 
lean_del_object(v___x_930_);
v___x_944_ = ((size_t)0ULL);
v___x_945_ = lean_usize_of_nat(v___x_934_);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_903_, v_alts_932_, v___x_944_, v___x_945_, v___x_935_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec_ref(v_alts_932_);
return v___x_946_;
}
}
else
{
size_t v___x_947_; size_t v___x_948_; lean_object* v___x_949_; 
lean_del_object(v___x_930_);
v___x_947_ = ((size_t)0ULL);
v___x_948_ = lean_usize_of_nat(v___x_934_);
v___x_949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_903_, v_alts_932_, v___x_947_, v___x_948_, v___x_935_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec_ref(v_alts_932_);
return v___x_949_;
}
}
}
}
case 7:
{
lean_object* v_k_951_; 
v_k_951_ = lean_ctor_get(v_c_904_, 3);
lean_inc_ref(v_k_951_);
lean_dec_ref_known(v_c_904_, 4);
v_c_904_ = v_k_951_;
goto _start;
}
case 8:
{
lean_object* v_k_953_; 
v_k_953_ = lean_ctor_get(v_c_904_, 3);
lean_inc_ref(v_k_953_);
lean_dec_ref_known(v_c_904_, 4);
v_c_904_ = v_k_953_;
goto _start;
}
case 9:
{
lean_object* v_k_955_; 
v_k_955_ = lean_ctor_get(v_c_904_, 5);
lean_inc_ref(v_k_955_);
lean_dec_ref_known(v_c_904_, 6);
v_c_904_ = v_k_955_;
goto _start;
}
case 10:
{
lean_object* v_k_957_; 
v_k_957_ = lean_ctor_get(v_c_904_, 2);
lean_inc_ref(v_k_957_);
lean_dec_ref_known(v_c_904_, 3);
v_c_904_ = v_k_957_;
goto _start;
}
case 11:
{
lean_object* v_k_959_; 
v_k_959_ = lean_ctor_get(v_c_904_, 2);
lean_inc_ref(v_k_959_);
lean_dec_ref_known(v_c_904_, 3);
v_c_904_ = v_k_959_;
goto _start;
}
case 12:
{
lean_object* v_k_961_; 
v_k_961_ = lean_ctor_get(v_c_904_, 3);
lean_inc_ref(v_k_961_);
lean_dec_ref_known(v_c_904_, 4);
v_c_904_ = v_k_961_;
goto _start;
}
case 13:
{
lean_object* v_k_963_; 
v_k_963_ = lean_ctor_get(v_c_904_, 1);
lean_inc_ref(v_k_963_);
lean_dec_ref_known(v_c_904_, 2);
v_c_904_ = v_k_963_;
goto _start;
}
default: 
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec_ref(v_c_904_);
v___x_965_ = lean_box(0);
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(uint8_t v_pu_967_, lean_object* v_as_968_, size_t v_i_969_, size_t v_stop_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___y_979_; uint8_t v___x_985_; 
v___x_985_ = lean_usize_dec_eq(v_i_969_, v_stop_970_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
v___x_986_ = lean_array_uget_borrowed(v_as_968_, v_i_969_);
switch(lean_obj_tag(v___x_986_))
{
case 0:
{
lean_object* v_code_987_; 
v_code_987_ = lean_ctor_get(v___x_986_, 2);
lean_inc_ref(v_code_987_);
v___y_979_ = v_code_987_;
goto v___jp_978_;
}
case 1:
{
lean_object* v_code_988_; 
v_code_988_ = lean_ctor_get(v___x_986_, 1);
lean_inc_ref(v_code_988_);
v___y_979_ = v_code_988_;
goto v___jp_978_;
}
default: 
{
lean_object* v_code_989_; 
v_code_989_ = lean_ctor_get(v___x_986_, 0);
lean_inc_ref(v_code_989_);
v___y_979_ = v_code_989_;
goto v___jp_978_;
}
}
}
else
{
lean_object* v___x_990_; 
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v_b_971_);
return v___x_990_;
}
v___jp_978_:
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_967_, v___y_979_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; size_t v___x_982_; size_t v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_add(v_i_969_, v___x_982_);
v_i_969_ = v___x_983_;
v_b_971_ = v_a_981_;
goto _start;
}
else
{
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0___boxed(lean_object* v_pu_991_, lean_object* v_as_992_, lean_object* v_i_993_, lean_object* v_stop_994_, lean_object* v_b_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v_pu_boxed_1002_; size_t v_i_boxed_1003_; size_t v_stop_boxed_1004_; lean_object* v_res_1005_; 
v_pu_boxed_1002_ = lean_unbox(v_pu_991_);
v_i_boxed_1003_ = lean_unbox_usize(v_i_993_);
lean_dec(v_i_993_);
v_stop_boxed_1004_ = lean_unbox_usize(v_stop_994_);
lean_dec(v_stop_994_);
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_boxed_1002_, v_as_992_, v_i_boxed_1003_, v_stop_boxed_1004_, v_b_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v_as_992_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed(lean_object* v_pu_1006_, lean_object* v_c_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
uint8_t v_pu_boxed_1014_; lean_object* v_res_1015_; 
v_pu_boxed_1014_ = lean_unbox(v_pu_1006_);
v_res_1015_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_boxed_1014_, v_c_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(lean_object* v_f_1016_, lean_object* v_v_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
if (lean_obj_tag(v_v_1017_) == 0)
{
lean_object* v_code_1024_; lean_object* v___x_1025_; 
v_code_1024_ = lean_ctor_get(v_v_1017_, 0);
lean_inc_ref(v_code_1024_);
lean_dec_ref_known(v_v_1017_, 1);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
v___x_1025_ = lean_apply_7(v_f_1016_, v_code_1024_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
return v___x_1025_;
}
else
{
lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref(v_f_1016_);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_v_1017_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v_v_1017_, 0);
lean_dec(v_unused_1034_);
v___x_1027_ = v_v_1017_;
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
else
{
lean_dec(v_v_1017_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1033_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_box(0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1029_);
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg___boxed(lean_object* v_f_1035_, lean_object* v_v_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_1035_, v_v_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(uint8_t v_pu_1044_, lean_object* v_f_1045_, lean_object* v_v_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_1045_, v_v_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___boxed(lean_object* v_pu_1054_, lean_object* v_f_1055_, lean_object* v_v_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
uint8_t v_pu_boxed_1063_; lean_object* v_res_1064_; 
v_pu_boxed_1063_ = lean_unbox(v_pu_1054_);
v_res_1064_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(v_pu_boxed_1063_, v_f_1055_, v_v_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(uint8_t v_pu_1065_, lean_object* v_as_1066_, size_t v_i_1067_, size_t v_stop_1068_, lean_object* v_b_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_usize_dec_eq(v_i_1067_, v_stop_1068_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v_value_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1077_ = lean_array_uget_borrowed(v_as_1066_, v_i_1067_);
v_value_1078_ = lean_ctor_get(v___x_1077_, 1);
v___x_1079_ = lean_box(v_pu_1065_);
v___x_1080_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed), 8, 1);
lean_closure_set(v___x_1080_, 0, v___x_1079_);
lean_inc_ref(v_value_1078_);
v___x_1081_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v___x_1080_, v_value_1078_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; size_t v___x_1083_; size_t v___x_1084_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1067_, v___x_1083_);
v_i_1067_ = v___x_1084_;
v_b_1069_ = v_a_1082_;
goto _start;
}
else
{
return v___x_1081_;
}
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_b_1069_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1___boxed(lean_object* v_pu_1087_, lean_object* v_as_1088_, lean_object* v_i_1089_, lean_object* v_stop_1090_, lean_object* v_b_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v_pu_boxed_1098_; size_t v_i_boxed_1099_; size_t v_stop_boxed_1100_; lean_object* v_res_1101_; 
v_pu_boxed_1098_ = lean_unbox(v_pu_1087_);
v_i_boxed_1099_ = lean_unbox_usize(v_i_1089_);
lean_dec(v_i_1089_);
v_stop_boxed_1100_ = lean_unbox_usize(v_stop_1090_);
lean_dec(v_stop_1090_);
v_res_1101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_boxed_1098_, v_as_1088_, v_i_boxed_1099_, v_stop_boxed_1100_, v_b_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v_as_1088_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(uint8_t v_pu_1102_, lean_object* v_decls_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = lean_array_get_size(v_decls_1103_);
v___x_1112_ = lean_box(0);
v___x_1113_ = lean_nat_dec_lt(v___x_1110_, v___x_1111_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
return v___x_1114_;
}
else
{
uint8_t v___x_1115_; 
v___x_1115_ = lean_nat_dec_le(v___x_1111_, v___x_1111_);
if (v___x_1115_ == 0)
{
if (v___x_1113_ == 0)
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1112_);
return v___x_1116_;
}
else
{
size_t v___x_1117_; size_t v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = ((size_t)0ULL);
v___x_1118_ = lean_usize_of_nat(v___x_1111_);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_1102_, v_decls_1103_, v___x_1117_, v___x_1118_, v___x_1112_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1119_;
}
}
else
{
size_t v___x_1120_; size_t v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = lean_usize_of_nat(v___x_1111_);
v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_1102_, v_decls_1103_, v___x_1120_, v___x_1121_, v___x_1112_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start___boxed(lean_object* v_pu_1123_, lean_object* v_decls_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
uint8_t v_pu_boxed_1131_; lean_object* v_res_1132_; 
v_pu_boxed_1131_ = lean_unbox(v_pu_1123_);
v_res_1132_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_boxed_1131_, v_decls_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_decls_1124_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues(uint8_t v_pu_1135_, lean_object* v_decls_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0));
v___x_1143_ = lean_st_mk_ref(v___x_1142_);
v___x_1144_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_1135_, v_decls_1136_, v___x_1143_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1152_; 
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v___x_1144_, 0);
lean_dec(v_unused_1153_);
v___x_1146_ = v___x_1144_;
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
else
{
lean_dec(v___x_1144_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1152_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_st_ref_get(v___x_1143_);
lean_dec(v___x_1143_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1148_);
v___x_1150_ = v___x_1146_;
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
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v___x_1143_);
v_a_1154_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1144_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1144_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues___boxed(lean_object* v_pu_1162_, lean_object* v_decls_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
uint8_t v_pu_boxed_1169_; lean_object* v_res_1170_; 
v_pu_boxed_1169_ = lean_unbox(v_pu_1162_);
v_res_1170_ = l_Lean_Compiler_LCNF_Probe_getLetValues(v_pu_boxed_1169_, v_decls_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec_ref(v_decls_1163_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(uint8_t v_pu_1171_, lean_object* v_code_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
switch(lean_obj_tag(v_code_1172_))
{
case 0:
{
lean_object* v_k_1179_; 
v_k_1179_ = lean_ctor_get(v_code_1172_, 1);
lean_inc_ref(v_k_1179_);
lean_dec_ref_known(v_code_1172_, 2);
v_code_1172_ = v_k_1179_;
goto _start;
}
case 1:
{
lean_object* v_decl_1181_; lean_object* v_k_1182_; lean_object* v_value_1183_; lean_object* v___x_1184_; 
v_decl_1181_ = lean_ctor_get(v_code_1172_, 0);
lean_inc_ref(v_decl_1181_);
v_k_1182_ = lean_ctor_get(v_code_1172_, 1);
lean_inc_ref(v_k_1182_);
lean_dec_ref_known(v_code_1172_, 2);
v_value_1183_ = lean_ctor_get(v_decl_1181_, 4);
lean_inc_ref(v_value_1183_);
lean_dec_ref(v_decl_1181_);
v___x_1184_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1171_, v_value_1183_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_dec_ref_known(v___x_1184_, 1);
v_code_1172_ = v_k_1182_;
goto _start;
}
else
{
lean_dec_ref(v_k_1182_);
return v___x_1184_;
}
}
case 2:
{
lean_object* v_decl_1186_; lean_object* v_k_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_value_1191_; lean_object* v___x_1192_; 
v_decl_1186_ = lean_ctor_get(v_code_1172_, 0);
lean_inc_ref_n(v_decl_1186_, 2);
v_k_1187_ = lean_ctor_get(v_code_1172_, 1);
lean_inc_ref(v_k_1187_);
lean_dec_ref_known(v_code_1172_, 2);
v___x_1188_ = lean_st_ref_take(v_a_1173_);
v___x_1189_ = lean_array_push(v___x_1188_, v_decl_1186_);
v___x_1190_ = lean_st_ref_put(v_a_1173_, v___x_1189_);
v_value_1191_ = lean_ctor_get(v_decl_1186_, 4);
lean_inc_ref(v_value_1191_);
lean_dec_ref(v_decl_1186_);
v___x_1192_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1171_, v_value_1191_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_dec_ref_known(v___x_1192_, 1);
v_code_1172_ = v_k_1187_;
goto _start;
}
else
{
lean_dec_ref(v_k_1187_);
return v___x_1192_;
}
}
case 4:
{
lean_object* v_cases_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1216_; 
v_cases_1194_ = lean_ctor_get(v_code_1172_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_code_1172_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1196_ = v_code_1172_;
v_isShared_1197_ = v_isSharedCheck_1216_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_cases_1194_);
lean_dec(v_code_1172_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1216_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_alts_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_alts_1198_ = lean_ctor_get(v_cases_1194_, 3);
lean_inc_ref(v_alts_1198_);
lean_dec_ref(v_cases_1194_);
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = lean_array_get_size(v_alts_1198_);
v___x_1201_ = lean_box(0);
v___x_1202_ = lean_nat_dec_lt(v___x_1199_, v___x_1200_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1204_; 
lean_dec_ref(v_alts_1198_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set_tag(v___x_1196_, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1201_);
v___x_1204_ = v___x_1196_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1201_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
else
{
uint8_t v___x_1206_; 
v___x_1206_ = lean_nat_dec_le(v___x_1200_, v___x_1200_);
if (v___x_1206_ == 0)
{
if (v___x_1202_ == 0)
{
lean_object* v___x_1208_; 
lean_dec_ref(v_alts_1198_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set_tag(v___x_1196_, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1201_);
v___x_1208_ = v___x_1196_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1201_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
else
{
size_t v___x_1210_; size_t v___x_1211_; lean_object* v___x_1212_; 
lean_del_object(v___x_1196_);
v___x_1210_ = ((size_t)0ULL);
v___x_1211_ = lean_usize_of_nat(v___x_1200_);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1171_, v_alts_1198_, v___x_1210_, v___x_1211_, v___x_1201_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec_ref(v_alts_1198_);
return v___x_1212_;
}
}
else
{
size_t v___x_1213_; size_t v___x_1214_; lean_object* v___x_1215_; 
lean_del_object(v___x_1196_);
v___x_1213_ = ((size_t)0ULL);
v___x_1214_ = lean_usize_of_nat(v___x_1200_);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1171_, v_alts_1198_, v___x_1213_, v___x_1214_, v___x_1201_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec_ref(v_alts_1198_);
return v___x_1215_;
}
}
}
}
case 7:
{
lean_object* v_k_1217_; 
v_k_1217_ = lean_ctor_get(v_code_1172_, 3);
lean_inc_ref(v_k_1217_);
lean_dec_ref_known(v_code_1172_, 4);
v_code_1172_ = v_k_1217_;
goto _start;
}
case 8:
{
lean_object* v_k_1219_; 
v_k_1219_ = lean_ctor_get(v_code_1172_, 3);
lean_inc_ref(v_k_1219_);
lean_dec_ref_known(v_code_1172_, 4);
v_code_1172_ = v_k_1219_;
goto _start;
}
case 9:
{
lean_object* v_k_1221_; 
v_k_1221_ = lean_ctor_get(v_code_1172_, 5);
lean_inc_ref(v_k_1221_);
lean_dec_ref_known(v_code_1172_, 6);
v_code_1172_ = v_k_1221_;
goto _start;
}
case 10:
{
lean_object* v_k_1223_; 
v_k_1223_ = lean_ctor_get(v_code_1172_, 2);
lean_inc_ref(v_k_1223_);
lean_dec_ref_known(v_code_1172_, 3);
v_code_1172_ = v_k_1223_;
goto _start;
}
case 11:
{
lean_object* v_k_1225_; 
v_k_1225_ = lean_ctor_get(v_code_1172_, 2);
lean_inc_ref(v_k_1225_);
lean_dec_ref_known(v_code_1172_, 3);
v_code_1172_ = v_k_1225_;
goto _start;
}
case 12:
{
lean_object* v_k_1227_; 
v_k_1227_ = lean_ctor_get(v_code_1172_, 3);
lean_inc_ref(v_k_1227_);
lean_dec_ref_known(v_code_1172_, 4);
v_code_1172_ = v_k_1227_;
goto _start;
}
case 13:
{
lean_object* v_k_1229_; 
v_k_1229_ = lean_ctor_get(v_code_1172_, 1);
lean_inc_ref(v_k_1229_);
lean_dec_ref_known(v_code_1172_, 2);
v_code_1172_ = v_k_1229_;
goto _start;
}
default: 
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec_ref(v_code_1172_);
v___x_1231_ = lean_box(0);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(uint8_t v_pu_1233_, lean_object* v_as_1234_, size_t v_i_1235_, size_t v_stop_1236_, lean_object* v_b_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___y_1245_; uint8_t v___x_1251_; 
v___x_1251_ = lean_usize_dec_eq(v_i_1235_, v_stop_1236_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_array_uget_borrowed(v_as_1234_, v_i_1235_);
switch(lean_obj_tag(v___x_1252_))
{
case 0:
{
lean_object* v_code_1253_; 
v_code_1253_ = lean_ctor_get(v___x_1252_, 2);
lean_inc_ref(v_code_1253_);
v___y_1245_ = v_code_1253_;
goto v___jp_1244_;
}
case 1:
{
lean_object* v_code_1254_; 
v_code_1254_ = lean_ctor_get(v___x_1252_, 1);
lean_inc_ref(v_code_1254_);
v___y_1245_ = v_code_1254_;
goto v___jp_1244_;
}
default: 
{
lean_object* v_code_1255_; 
v_code_1255_ = lean_ctor_get(v___x_1252_, 0);
lean_inc_ref(v_code_1255_);
v___y_1245_ = v_code_1255_;
goto v___jp_1244_;
}
}
}
else
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_b_1237_);
return v___x_1256_;
}
v___jp_1244_:
{
lean_object* v___x_1246_; 
v___x_1246_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1233_, v___y_1245_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; size_t v___x_1248_; size_t v___x_1249_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = ((size_t)1ULL);
v___x_1249_ = lean_usize_add(v_i_1235_, v___x_1248_);
v_i_1235_ = v___x_1249_;
v_b_1237_ = v_a_1247_;
goto _start;
}
else
{
return v___x_1246_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0___boxed(lean_object* v_pu_1257_, lean_object* v_as_1258_, lean_object* v_i_1259_, lean_object* v_stop_1260_, lean_object* v_b_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
uint8_t v_pu_boxed_1268_; size_t v_i_boxed_1269_; size_t v_stop_boxed_1270_; lean_object* v_res_1271_; 
v_pu_boxed_1268_ = lean_unbox(v_pu_1257_);
v_i_boxed_1269_ = lean_unbox_usize(v_i_1259_);
lean_dec(v_i_1259_);
v_stop_boxed_1270_ = lean_unbox_usize(v_stop_1260_);
lean_dec(v_stop_1260_);
v_res_1271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_boxed_1268_, v_as_1258_, v_i_boxed_1269_, v_stop_boxed_1270_, v_b_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v_as_1258_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed(lean_object* v_pu_1272_, lean_object* v_code_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
uint8_t v_pu_boxed_1280_; lean_object* v_res_1281_; 
v_pu_boxed_1280_ = lean_unbox(v_pu_1272_);
v_res_1281_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_boxed_1280_, v_code_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(lean_object* v_f_1282_, lean_object* v_v_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
if (lean_obj_tag(v_v_1283_) == 0)
{
lean_object* v_code_1290_; lean_object* v___x_1291_; 
v_code_1290_ = lean_ctor_get(v_v_1283_, 0);
lean_inc_ref(v_code_1290_);
lean_dec_ref_known(v_v_1283_, 1);
lean_inc(v___y_1288_);
lean_inc_ref(v___y_1287_);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
v___x_1291_ = lean_apply_7(v_f_1282_, v_code_1290_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, lean_box(0));
return v___x_1291_;
}
else
{
lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_f_1282_);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_v_1283_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v_v_1283_, 0);
lean_dec(v_unused_1300_);
v___x_1293_ = v_v_1283_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_dec(v_v_1283_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = lean_box(0);
if (v_isShared_1294_ == 0)
{
lean_ctor_set_tag(v___x_1293_, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg___boxed(lean_object* v_f_1301_, lean_object* v_v_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1301_, v_v_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(uint8_t v_pu_1310_, lean_object* v_f_1311_, lean_object* v_v_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1311_, v_v_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___boxed(lean_object* v_pu_1320_, lean_object* v_f_1321_, lean_object* v_v_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
uint8_t v_pu_boxed_1329_; lean_object* v_res_1330_; 
v_pu_boxed_1329_ = lean_unbox(v_pu_1320_);
v_res_1330_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(v_pu_boxed_1329_, v_f_1321_, v_v_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(uint8_t v_pu_1331_, lean_object* v_as_1332_, size_t v_i_1333_, size_t v_stop_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_eq(v_i_1333_, v_stop_1334_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v_value_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1343_ = lean_array_uget_borrowed(v_as_1332_, v_i_1333_);
v_value_1344_ = lean_ctor_get(v___x_1343_, 1);
v___x_1345_ = lean_box(v_pu_1331_);
v___x_1346_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed), 8, 1);
lean_closure_set(v___x_1346_, 0, v___x_1345_);
lean_inc_ref(v_value_1344_);
v___x_1347_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v___x_1346_, v_value_1344_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; size_t v___x_1349_; size_t v___x_1350_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = ((size_t)1ULL);
v___x_1350_ = lean_usize_add(v_i_1333_, v___x_1349_);
v_i_1333_ = v___x_1350_;
v_b_1335_ = v_a_1348_;
goto _start;
}
else
{
return v___x_1347_;
}
}
else
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v_b_1335_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1___boxed(lean_object* v_pu_1353_, lean_object* v_as_1354_, lean_object* v_i_1355_, lean_object* v_stop_1356_, lean_object* v_b_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
uint8_t v_pu_boxed_1364_; size_t v_i_boxed_1365_; size_t v_stop_boxed_1366_; lean_object* v_res_1367_; 
v_pu_boxed_1364_ = lean_unbox(v_pu_1353_);
v_i_boxed_1365_ = lean_unbox_usize(v_i_1355_);
lean_dec(v_i_1355_);
v_stop_boxed_1366_ = lean_unbox_usize(v_stop_1356_);
lean_dec(v_stop_1356_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_boxed_1364_, v_as_1354_, v_i_boxed_1365_, v_stop_boxed_1366_, v_b_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v_as_1354_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(uint8_t v_pu_1368_, lean_object* v_decls_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = lean_array_get_size(v_decls_1369_);
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_nat_dec_lt(v___x_1376_, v___x_1377_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
return v___x_1380_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_nat_dec_le(v___x_1377_, v___x_1377_);
if (v___x_1381_ == 0)
{
if (v___x_1379_ == 0)
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1378_);
return v___x_1382_;
}
else
{
size_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = lean_usize_of_nat(v___x_1377_);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1368_, v_decls_1369_, v___x_1383_, v___x_1384_, v___x_1378_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
return v___x_1385_;
}
}
else
{
size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = ((size_t)0ULL);
v___x_1387_ = lean_usize_of_nat(v___x_1377_);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1368_, v_decls_1369_, v___x_1386_, v___x_1387_, v___x_1378_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
return v___x_1388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start___boxed(lean_object* v_pu_1389_, lean_object* v_decls_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
uint8_t v_pu_boxed_1397_; lean_object* v_res_1398_; 
v_pu_boxed_1397_ = lean_unbox(v_pu_1389_);
v_res_1398_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_boxed_1397_, v_decls_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_decls_1390_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps(uint8_t v_pu_1401_, lean_object* v_decls_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getJps___closed__0));
v___x_1409_ = lean_st_mk_ref(v___x_1408_);
v___x_1410_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_1401_, v_decls_1402_, v___x_1409_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1418_; 
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; 
v_unused_1419_ = lean_ctor_get(v___x_1410_, 0);
lean_dec(v_unused_1419_);
v___x_1412_ = v___x_1410_;
v_isShared_1413_ = v_isSharedCheck_1418_;
goto v_resetjp_1411_;
}
else
{
lean_dec(v___x_1410_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1418_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_st_ref_get(v___x_1409_);
lean_dec(v___x_1409_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1414_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v___x_1409_);
v_a_1420_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1410_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1410_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps___boxed(lean_object* v_pu_1428_, lean_object* v_decls_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
uint8_t v_pu_boxed_1435_; lean_object* v_res_1436_; 
v_pu_boxed_1435_ = lean_unbox(v_pu_1428_);
v_res_1436_ = l_Lean_Compiler_LCNF_Probe_getJps(v_pu_boxed_1435_, v_decls_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec(v_a_1431_);
lean_dec_ref(v_a_1430_);
lean_dec_ref(v_decls_1429_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(uint8_t v_pu_1437_, lean_object* v_f_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
switch(lean_obj_tag(v_a_1439_))
{
case 0:
{
lean_object* v_decl_1445_; lean_object* v_k_1446_; lean_object* v___x_1447_; 
v_decl_1445_ = lean_ctor_get(v_a_1439_, 0);
lean_inc_ref(v_decl_1445_);
v_k_1446_ = lean_ctor_get(v_a_1439_, 1);
lean_inc_ref(v_k_1446_);
lean_dec_ref_known(v_a_1439_, 2);
lean_inc_ref(v_f_1438_);
lean_inc(v_a_1443_);
lean_inc_ref(v_a_1442_);
lean_inc(v_a_1441_);
lean_inc_ref(v_a_1440_);
v___x_1447_ = lean_apply_6(v_f_1438_, v_decl_1445_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, lean_box(0));
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; uint8_t v___x_1449_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
v___x_1449_ = lean_unbox(v_a_1448_);
lean_dec(v_a_1448_);
if (v___x_1449_ == 0)
{
lean_dec_ref_known(v___x_1447_, 1);
v_a_1439_ = v_k_1446_;
goto _start;
}
else
{
lean_dec_ref(v_k_1446_);
lean_dec_ref(v_f_1438_);
return v___x_1447_;
}
}
else
{
lean_dec_ref(v_k_1446_);
lean_dec_ref(v_f_1438_);
return v___x_1447_;
}
}
case 1:
{
lean_object* v_decl_1451_; lean_object* v_k_1452_; lean_object* v_value_1453_; lean_object* v___x_1454_; 
v_decl_1451_ = lean_ctor_get(v_a_1439_, 0);
lean_inc_ref(v_decl_1451_);
v_k_1452_ = lean_ctor_get(v_a_1439_, 1);
lean_inc_ref(v_k_1452_);
lean_dec_ref_known(v_a_1439_, 2);
v_value_1453_ = lean_ctor_get(v_decl_1451_, 4);
lean_inc_ref(v_value_1453_);
lean_dec_ref(v_decl_1451_);
lean_inc_ref(v_f_1438_);
v___x_1454_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1437_, v_f_1438_, v_value_1453_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; uint8_t v___x_1456_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
v___x_1456_ = lean_unbox(v_a_1455_);
lean_dec(v_a_1455_);
if (v___x_1456_ == 0)
{
lean_dec_ref_known(v___x_1454_, 1);
v_a_1439_ = v_k_1452_;
goto _start;
}
else
{
lean_dec_ref(v_k_1452_);
lean_dec_ref(v_f_1438_);
return v___x_1454_;
}
}
else
{
lean_dec_ref(v_k_1452_);
lean_dec_ref(v_f_1438_);
return v___x_1454_;
}
}
case 2:
{
lean_object* v_decl_1458_; lean_object* v_k_1459_; lean_object* v_value_1460_; lean_object* v___x_1461_; 
v_decl_1458_ = lean_ctor_get(v_a_1439_, 0);
lean_inc_ref(v_decl_1458_);
v_k_1459_ = lean_ctor_get(v_a_1439_, 1);
lean_inc_ref(v_k_1459_);
lean_dec_ref_known(v_a_1439_, 2);
v_value_1460_ = lean_ctor_get(v_decl_1458_, 4);
lean_inc_ref(v_value_1460_);
lean_dec_ref(v_decl_1458_);
lean_inc_ref(v_f_1438_);
v___x_1461_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1437_, v_f_1438_, v_value_1460_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; uint8_t v___x_1463_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
v___x_1463_ = lean_unbox(v_a_1462_);
lean_dec(v_a_1462_);
if (v___x_1463_ == 0)
{
lean_dec_ref_known(v___x_1461_, 1);
v_a_1439_ = v_k_1459_;
goto _start;
}
else
{
lean_dec_ref(v_k_1459_);
lean_dec_ref(v_f_1438_);
return v___x_1461_;
}
}
else
{
lean_dec_ref(v_k_1459_);
lean_dec_ref(v_f_1438_);
return v___x_1461_;
}
}
case 4:
{
lean_object* v_cases_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1484_; 
v_cases_1465_ = lean_ctor_get(v_a_1439_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_a_1439_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1467_ = v_a_1439_;
v_isShared_1468_ = v_isSharedCheck_1484_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_cases_1465_);
lean_dec(v_a_1439_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1484_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_alts_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v_alts_1469_ = lean_ctor_get(v_cases_1465_, 3);
lean_inc_ref(v_alts_1469_);
lean_dec_ref(v_cases_1465_);
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = lean_array_get_size(v_alts_1469_);
v___x_1472_ = lean_nat_dec_lt(v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
lean_dec_ref(v_alts_1469_);
lean_dec_ref(v_f_1438_);
v___x_1473_ = lean_box(v___x_1472_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1473_);
v___x_1475_ = v___x_1467_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
else
{
if (v___x_1472_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_dec_ref(v_alts_1469_);
lean_dec_ref(v_f_1438_);
v___x_1477_ = lean_box(v___x_1472_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1477_);
v___x_1479_ = v___x_1467_;
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
else
{
size_t v___x_1481_; size_t v___x_1482_; lean_object* v___x_1483_; 
lean_del_object(v___x_1467_);
v___x_1481_ = ((size_t)0ULL);
v___x_1482_ = lean_usize_of_nat(v___x_1471_);
v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_1437_, v_f_1438_, v_alts_1469_, v___x_1481_, v___x_1482_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
lean_dec_ref(v_alts_1469_);
return v___x_1483_;
}
}
}
}
case 7:
{
lean_object* v_k_1485_; 
v_k_1485_ = lean_ctor_get(v_a_1439_, 3);
lean_inc_ref(v_k_1485_);
lean_dec_ref_known(v_a_1439_, 4);
v_a_1439_ = v_k_1485_;
goto _start;
}
case 8:
{
lean_object* v_k_1487_; 
v_k_1487_ = lean_ctor_get(v_a_1439_, 3);
lean_inc_ref(v_k_1487_);
lean_dec_ref_known(v_a_1439_, 4);
v_a_1439_ = v_k_1487_;
goto _start;
}
case 9:
{
lean_object* v_k_1489_; 
v_k_1489_ = lean_ctor_get(v_a_1439_, 5);
lean_inc_ref(v_k_1489_);
lean_dec_ref_known(v_a_1439_, 6);
v_a_1439_ = v_k_1489_;
goto _start;
}
case 10:
{
lean_object* v_k_1491_; 
v_k_1491_ = lean_ctor_get(v_a_1439_, 2);
lean_inc_ref(v_k_1491_);
lean_dec_ref_known(v_a_1439_, 3);
v_a_1439_ = v_k_1491_;
goto _start;
}
case 11:
{
lean_object* v_k_1493_; 
v_k_1493_ = lean_ctor_get(v_a_1439_, 2);
lean_inc_ref(v_k_1493_);
lean_dec_ref_known(v_a_1439_, 3);
v_a_1439_ = v_k_1493_;
goto _start;
}
case 12:
{
lean_object* v_k_1495_; 
v_k_1495_ = lean_ctor_get(v_a_1439_, 3);
lean_inc_ref(v_k_1495_);
lean_dec_ref_known(v_a_1439_, 4);
v_a_1439_ = v_k_1495_;
goto _start;
}
case 13:
{
lean_object* v_k_1497_; 
v_k_1497_ = lean_ctor_get(v_a_1439_, 1);
lean_inc_ref(v_k_1497_);
lean_dec_ref_known(v_a_1439_, 2);
v_a_1439_ = v_k_1497_;
goto _start;
}
default: 
{
uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec_ref(v_a_1439_);
lean_dec_ref(v_f_1438_);
v___x_1499_ = 0;
v___x_1500_ = lean_box(v___x_1499_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(uint8_t v_pu_1502_, lean_object* v_f_1503_, lean_object* v_as_1504_, size_t v_i_1505_, size_t v_stop_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_usize_dec_eq(v_i_1505_, v_stop_1506_);
if (v___x_1512_ == 0)
{
uint8_t v___x_1513_; lean_object* v___y_1515_; lean_object* v___x_1530_; 
v___x_1513_ = 1;
v___x_1530_ = lean_array_uget_borrowed(v_as_1504_, v_i_1505_);
switch(lean_obj_tag(v___x_1530_))
{
case 0:
{
lean_object* v_code_1531_; 
v_code_1531_ = lean_ctor_get(v___x_1530_, 2);
lean_inc_ref(v_code_1531_);
v___y_1515_ = v_code_1531_;
goto v___jp_1514_;
}
case 1:
{
lean_object* v_code_1532_; 
v_code_1532_ = lean_ctor_get(v___x_1530_, 1);
lean_inc_ref(v_code_1532_);
v___y_1515_ = v_code_1532_;
goto v___jp_1514_;
}
default: 
{
lean_object* v_code_1533_; 
v_code_1533_ = lean_ctor_get(v___x_1530_, 0);
lean_inc_ref(v_code_1533_);
v___y_1515_ = v_code_1533_;
goto v___jp_1514_;
}
}
v___jp_1514_:
{
lean_object* v___x_1516_; 
lean_inc_ref(v_f_1503_);
v___x_1516_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1502_, v_f_1503_, v___y_1515_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1529_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1529_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1529_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_unbox(v_a_1517_);
lean_dec(v_a_1517_);
if (v___x_1521_ == 0)
{
size_t v___x_1522_; size_t v___x_1523_; 
lean_del_object(v___x_1519_);
v___x_1522_ = ((size_t)1ULL);
v___x_1523_ = lean_usize_add(v_i_1505_, v___x_1522_);
v_i_1505_ = v___x_1523_;
goto _start;
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1527_; 
lean_dec_ref(v_f_1503_);
v___x_1525_ = lean_box(v___x_1513_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1525_);
v___x_1527_ = v___x_1519_;
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
else
{
lean_dec_ref(v_f_1503_);
return v___x_1516_;
}
}
}
else
{
uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec_ref(v_f_1503_);
v___x_1534_ = 0;
v___x_1535_ = lean_box(v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0___boxed(lean_object* v_pu_1537_, lean_object* v_f_1538_, lean_object* v_as_1539_, lean_object* v_i_1540_, lean_object* v_stop_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
uint8_t v_pu_boxed_1547_; size_t v_i_boxed_1548_; size_t v_stop_boxed_1549_; lean_object* v_res_1550_; 
v_pu_boxed_1547_ = lean_unbox(v_pu_1537_);
v_i_boxed_1548_ = lean_unbox_usize(v_i_1540_);
lean_dec(v_i_1540_);
v_stop_boxed_1549_ = lean_unbox_usize(v_stop_1541_);
lean_dec(v_stop_1541_);
v_res_1550_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_boxed_1547_, v_f_1538_, v_as_1539_, v_i_boxed_1548_, v_stop_boxed_1549_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec_ref(v_as_1539_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed(lean_object* v_pu_1551_, lean_object* v_f_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
uint8_t v_pu_boxed_1559_; lean_object* v_res_1560_; 
v_pu_boxed_1559_ = lean_unbox(v_pu_1551_);
v_res_1560_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_boxed_1559_, v_f_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(lean_object* v_v_1561_, lean_object* v_f_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
if (lean_obj_tag(v_v_1561_) == 0)
{
lean_object* v_code_1568_; lean_object* v___x_1569_; 
v_code_1568_ = lean_ctor_get(v_v_1561_, 0);
lean_inc_ref(v_code_1568_);
lean_dec_ref_known(v_v_1561_, 1);
lean_inc(v___y_1566_);
lean_inc_ref(v___y_1565_);
lean_inc(v___y_1564_);
lean_inc_ref(v___y_1563_);
v___x_1569_ = lean_apply_6(v_f_1562_, v_code_1568_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, lean_box(0));
return v___x_1569_;
}
else
{
lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v_f_1562_);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_v_1561_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v_v_1561_, 0);
lean_dec(v_unused_1579_);
v___x_1571_ = v_v_1561_;
v_isShared_1572_ = v_isSharedCheck_1578_;
goto v_resetjp_1570_;
}
else
{
lean_dec(v_v_1561_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1578_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1573_ = 0;
v___x_1574_ = lean_box(v___x_1573_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1574_);
v___x_1576_ = v___x_1571_;
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg___boxed(lean_object* v_v_1580_, lean_object* v_f_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1580_, v_f_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(uint8_t v_pu_1588_, lean_object* v_v_1589_, lean_object* v_f_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1589_, v_f_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___boxed(lean_object* v_pu_1597_, lean_object* v_v_1598_, lean_object* v_f_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
uint8_t v_pu_boxed_1605_; lean_object* v_res_1606_; 
v_pu_boxed_1605_ = lean_unbox(v_pu_1597_);
v_res_1606_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(v_pu_boxed_1605_, v_v_1598_, v_f_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(uint8_t v_pu_1607_, lean_object* v_f_1608_, lean_object* v_as_1609_, size_t v_i_1610_, size_t v_stop_1611_, lean_object* v_b_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_usize_dec_eq(v_i_1610_, v_stop_1611_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v_value_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1619_ = lean_array_uget_borrowed(v_as_1609_, v_i_1610_);
v_value_1620_ = lean_ctor_get(v___x_1619_, 1);
v___x_1621_ = lean_box(v_pu_1607_);
lean_inc_ref(v_f_1608_);
v___x_1622_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed), 8, 2);
lean_closure_set(v___x_1622_, 0, v___x_1621_);
lean_closure_set(v___x_1622_, 1, v_f_1608_);
lean_inc_ref(v_value_1620_);
v___x_1623_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1620_, v___x_1622_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v_a_1626_; uint8_t v___x_1630_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___x_1630_ = lean_unbox(v_a_1624_);
lean_dec(v_a_1624_);
if (v___x_1630_ == 0)
{
v_a_1626_ = v_b_1612_;
goto v___jp_1625_;
}
else
{
lean_object* v___x_1631_; 
lean_inc(v___x_1619_);
v___x_1631_ = lean_array_push(v_b_1612_, v___x_1619_);
v_a_1626_ = v___x_1631_;
goto v___jp_1625_;
}
v___jp_1625_:
{
size_t v___x_1627_; size_t v___x_1628_; 
v___x_1627_ = ((size_t)1ULL);
v___x_1628_ = lean_usize_add(v_i_1610_, v___x_1627_);
v_i_1610_ = v___x_1628_;
v_b_1612_ = v_a_1626_;
goto _start;
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v_b_1612_);
lean_dec_ref(v_f_1608_);
v_a_1632_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1623_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1623_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
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
lean_object* v___x_1640_; 
lean_dec_ref(v_f_1608_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_b_1612_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1___boxed(lean_object* v_pu_1641_, lean_object* v_f_1642_, lean_object* v_as_1643_, lean_object* v_i_1644_, lean_object* v_stop_1645_, lean_object* v_b_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
uint8_t v_pu_boxed_1652_; size_t v_i_boxed_1653_; size_t v_stop_boxed_1654_; lean_object* v_res_1655_; 
v_pu_boxed_1652_ = lean_unbox(v_pu_1641_);
v_i_boxed_1653_ = lean_unbox_usize(v_i_1644_);
lean_dec(v_i_1644_);
v_stop_boxed_1654_ = lean_unbox_usize(v_stop_1645_);
lean_dec(v_stop_1645_);
v_res_1655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_boxed_1652_, v_f_1642_, v_as_1643_, v_i_boxed_1653_, v_stop_boxed_1654_, v_b_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec_ref(v_as_1643_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet(uint8_t v_pu_1658_, lean_object* v_f_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
v___x_1667_ = lean_array_get_size(v_a_1660_);
v___x_1668_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1669_ = lean_nat_dec_lt(v___x_1666_, v___x_1667_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
lean_dec_ref(v_f_1659_);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
return v___x_1670_;
}
else
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_nat_dec_le(v___x_1667_, v___x_1667_);
if (v___x_1671_ == 0)
{
if (v___x_1669_ == 0)
{
lean_object* v___x_1672_; 
lean_dec_ref(v_f_1659_);
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1668_);
return v___x_1672_;
}
else
{
size_t v___x_1673_; size_t v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = ((size_t)0ULL);
v___x_1674_ = lean_usize_of_nat(v___x_1667_);
v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1658_, v_f_1659_, v_a_1660_, v___x_1673_, v___x_1674_, v___x_1668_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
return v___x_1675_;
}
}
else
{
size_t v___x_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = ((size_t)0ULL);
v___x_1677_ = lean_usize_of_nat(v___x_1667_);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1658_, v_f_1659_, v_a_1660_, v___x_1676_, v___x_1677_, v___x_1668_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet___boxed(lean_object* v_pu_1679_, lean_object* v_f_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
uint8_t v_pu_boxed_1687_; lean_object* v_res_1688_; 
v_pu_boxed_1687_ = lean_unbox(v_pu_1679_);
v_res_1688_ = l_Lean_Compiler_LCNF_Probe_filterByLet(v_pu_boxed_1687_, v_f_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec_ref(v_a_1681_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(uint8_t v_pu_1689_, lean_object* v_f_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
switch(lean_obj_tag(v_a_1691_))
{
case 0:
{
lean_object* v_k_1697_; 
v_k_1697_ = lean_ctor_get(v_a_1691_, 1);
lean_inc_ref(v_k_1697_);
lean_dec_ref_known(v_a_1691_, 2);
v_a_1691_ = v_k_1697_;
goto _start;
}
case 1:
{
lean_object* v_decl_1699_; lean_object* v_k_1700_; lean_object* v___x_1701_; 
v_decl_1699_ = lean_ctor_get(v_a_1691_, 0);
lean_inc_ref_n(v_decl_1699_, 2);
v_k_1700_ = lean_ctor_get(v_a_1691_, 1);
lean_inc_ref(v_k_1700_);
lean_dec_ref_known(v_a_1691_, 2);
lean_inc_ref(v_f_1690_);
lean_inc(v_a_1695_);
lean_inc_ref(v_a_1694_);
lean_inc(v_a_1693_);
lean_inc_ref(v_a_1692_);
v___x_1701_ = lean_apply_6(v_f_1690_, v_decl_1699_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, lean_box(0));
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; uint8_t v___x_1703_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
v___x_1703_ = lean_unbox(v_a_1702_);
lean_dec(v_a_1702_);
if (v___x_1703_ == 0)
{
lean_object* v_value_1704_; lean_object* v___x_1705_; 
lean_dec_ref_known(v___x_1701_, 1);
v_value_1704_ = lean_ctor_get(v_decl_1699_, 4);
lean_inc_ref(v_value_1704_);
lean_dec_ref(v_decl_1699_);
lean_inc_ref(v_f_1690_);
v___x_1705_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1689_, v_f_1690_, v_value_1704_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; uint8_t v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
v___x_1707_ = lean_unbox(v_a_1706_);
lean_dec(v_a_1706_);
if (v___x_1707_ == 0)
{
lean_dec_ref_known(v___x_1705_, 1);
v_a_1691_ = v_k_1700_;
goto _start;
}
else
{
lean_dec_ref(v_k_1700_);
lean_dec_ref(v_f_1690_);
return v___x_1705_;
}
}
else
{
lean_dec_ref(v_k_1700_);
lean_dec_ref(v_f_1690_);
return v___x_1705_;
}
}
else
{
lean_dec_ref(v_k_1700_);
lean_dec_ref(v_decl_1699_);
lean_dec_ref(v_f_1690_);
return v___x_1701_;
}
}
else
{
lean_dec_ref(v_k_1700_);
lean_dec_ref(v_decl_1699_);
lean_dec_ref(v_f_1690_);
return v___x_1701_;
}
}
case 2:
{
lean_object* v_k_1709_; 
v_k_1709_ = lean_ctor_get(v_a_1691_, 1);
lean_inc_ref(v_k_1709_);
lean_dec_ref_known(v_a_1691_, 2);
v_a_1691_ = v_k_1709_;
goto _start;
}
case 4:
{
lean_object* v_cases_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1730_; 
v_cases_1711_ = lean_ctor_get(v_a_1691_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_a_1691_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1713_ = v_a_1691_;
v_isShared_1714_ = v_isSharedCheck_1730_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_cases_1711_);
lean_dec(v_a_1691_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1730_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_alts_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v_alts_1715_ = lean_ctor_get(v_cases_1711_, 3);
lean_inc_ref(v_alts_1715_);
lean_dec_ref(v_cases_1711_);
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = lean_array_get_size(v_alts_1715_);
v___x_1718_ = lean_nat_dec_lt(v___x_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
lean_dec_ref(v_alts_1715_);
lean_dec_ref(v_f_1690_);
v___x_1719_ = lean_box(v___x_1718_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1719_);
v___x_1721_ = v___x_1713_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
else
{
if (v___x_1718_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1725_; 
lean_dec_ref(v_alts_1715_);
lean_dec_ref(v_f_1690_);
v___x_1723_ = lean_box(v___x_1718_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set_tag(v___x_1713_, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1723_);
v___x_1725_ = v___x_1713_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
else
{
size_t v___x_1727_; size_t v___x_1728_; lean_object* v___x_1729_; 
lean_del_object(v___x_1713_);
v___x_1727_ = ((size_t)0ULL);
v___x_1728_ = lean_usize_of_nat(v___x_1717_);
v___x_1729_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_1689_, v_f_1690_, v_alts_1715_, v___x_1727_, v___x_1728_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec_ref(v_alts_1715_);
return v___x_1729_;
}
}
}
}
case 7:
{
lean_object* v_k_1731_; 
v_k_1731_ = lean_ctor_get(v_a_1691_, 3);
lean_inc_ref(v_k_1731_);
lean_dec_ref_known(v_a_1691_, 4);
v_a_1691_ = v_k_1731_;
goto _start;
}
case 8:
{
lean_object* v_k_1733_; 
v_k_1733_ = lean_ctor_get(v_a_1691_, 3);
lean_inc_ref(v_k_1733_);
lean_dec_ref_known(v_a_1691_, 4);
v_a_1691_ = v_k_1733_;
goto _start;
}
case 9:
{
lean_object* v_k_1735_; 
v_k_1735_ = lean_ctor_get(v_a_1691_, 5);
lean_inc_ref(v_k_1735_);
lean_dec_ref_known(v_a_1691_, 6);
v_a_1691_ = v_k_1735_;
goto _start;
}
case 10:
{
lean_object* v_k_1737_; 
v_k_1737_ = lean_ctor_get(v_a_1691_, 2);
lean_inc_ref(v_k_1737_);
lean_dec_ref_known(v_a_1691_, 3);
v_a_1691_ = v_k_1737_;
goto _start;
}
case 11:
{
lean_object* v_k_1739_; 
v_k_1739_ = lean_ctor_get(v_a_1691_, 2);
lean_inc_ref(v_k_1739_);
lean_dec_ref_known(v_a_1691_, 3);
v_a_1691_ = v_k_1739_;
goto _start;
}
case 12:
{
lean_object* v_k_1741_; 
v_k_1741_ = lean_ctor_get(v_a_1691_, 3);
lean_inc_ref(v_k_1741_);
lean_dec_ref_known(v_a_1691_, 4);
v_a_1691_ = v_k_1741_;
goto _start;
}
case 13:
{
lean_object* v_k_1743_; 
v_k_1743_ = lean_ctor_get(v_a_1691_, 1);
lean_inc_ref(v_k_1743_);
lean_dec_ref_known(v_a_1691_, 2);
v_a_1691_ = v_k_1743_;
goto _start;
}
default: 
{
uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref(v_a_1691_);
lean_dec_ref(v_f_1690_);
v___x_1745_ = 0;
v___x_1746_ = lean_box(v___x_1745_);
v___x_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
return v___x_1747_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(uint8_t v_pu_1748_, lean_object* v_f_1749_, lean_object* v_as_1750_, size_t v_i_1751_, size_t v_stop_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_usize_dec_eq(v_i_1751_, v_stop_1752_);
if (v___x_1758_ == 0)
{
uint8_t v___x_1759_; lean_object* v___y_1761_; lean_object* v___x_1776_; 
v___x_1759_ = 1;
v___x_1776_ = lean_array_uget_borrowed(v_as_1750_, v_i_1751_);
switch(lean_obj_tag(v___x_1776_))
{
case 0:
{
lean_object* v_code_1777_; 
v_code_1777_ = lean_ctor_get(v___x_1776_, 2);
lean_inc_ref(v_code_1777_);
v___y_1761_ = v_code_1777_;
goto v___jp_1760_;
}
case 1:
{
lean_object* v_code_1778_; 
v_code_1778_ = lean_ctor_get(v___x_1776_, 1);
lean_inc_ref(v_code_1778_);
v___y_1761_ = v_code_1778_;
goto v___jp_1760_;
}
default: 
{
lean_object* v_code_1779_; 
v_code_1779_ = lean_ctor_get(v___x_1776_, 0);
lean_inc_ref(v_code_1779_);
v___y_1761_ = v_code_1779_;
goto v___jp_1760_;
}
}
v___jp_1760_:
{
lean_object* v___x_1762_; 
lean_inc_ref(v_f_1749_);
v___x_1762_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1748_, v_f_1749_, v___y_1761_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1775_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1775_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1775_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_unbox(v_a_1763_);
lean_dec(v_a_1763_);
if (v___x_1767_ == 0)
{
size_t v___x_1768_; size_t v___x_1769_; 
lean_del_object(v___x_1765_);
v___x_1768_ = ((size_t)1ULL);
v___x_1769_ = lean_usize_add(v_i_1751_, v___x_1768_);
v_i_1751_ = v___x_1769_;
goto _start;
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
lean_dec_ref(v_f_1749_);
v___x_1771_ = lean_box(v___x_1759_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1771_);
v___x_1773_ = v___x_1765_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
else
{
lean_dec_ref(v_f_1749_);
return v___x_1762_;
}
}
}
else
{
uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec_ref(v_f_1749_);
v___x_1780_ = 0;
v___x_1781_ = lean_box(v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0___boxed(lean_object* v_pu_1783_, lean_object* v_f_1784_, lean_object* v_as_1785_, lean_object* v_i_1786_, lean_object* v_stop_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
uint8_t v_pu_boxed_1793_; size_t v_i_boxed_1794_; size_t v_stop_boxed_1795_; lean_object* v_res_1796_; 
v_pu_boxed_1793_ = lean_unbox(v_pu_1783_);
v_i_boxed_1794_ = lean_unbox_usize(v_i_1786_);
lean_dec(v_i_1786_);
v_stop_boxed_1795_ = lean_unbox_usize(v_stop_1787_);
lean_dec(v_stop_1787_);
v_res_1796_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_boxed_1793_, v_f_1784_, v_as_1785_, v_i_boxed_1794_, v_stop_boxed_1795_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec_ref(v_as_1785_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed(lean_object* v_pu_1797_, lean_object* v_f_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
uint8_t v_pu_boxed_1805_; lean_object* v_res_1806_; 
v_pu_boxed_1805_ = lean_unbox(v_pu_1797_);
v_res_1806_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_boxed_1805_, v_f_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(uint8_t v_pu_1807_, lean_object* v_f_1808_, lean_object* v_as_1809_, size_t v_i_1810_, size_t v_stop_1811_, lean_object* v_b_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v___x_1818_; 
v___x_1818_ = lean_usize_dec_eq(v_i_1810_, v_stop_1811_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v_value_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1819_ = lean_array_uget_borrowed(v_as_1809_, v_i_1810_);
v_value_1820_ = lean_ctor_get(v___x_1819_, 1);
v___x_1821_ = lean_box(v_pu_1807_);
lean_inc_ref(v_f_1808_);
v___x_1822_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed), 8, 2);
lean_closure_set(v___x_1822_, 0, v___x_1821_);
lean_closure_set(v___x_1822_, 1, v_f_1808_);
lean_inc_ref(v_value_1820_);
v___x_1823_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1820_, v___x_1822_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v_a_1826_; uint8_t v___x_1830_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1823_, 1);
v___x_1830_ = lean_unbox(v_a_1824_);
lean_dec(v_a_1824_);
if (v___x_1830_ == 0)
{
v_a_1826_ = v_b_1812_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1831_; 
lean_inc(v___x_1819_);
v___x_1831_ = lean_array_push(v_b_1812_, v___x_1819_);
v_a_1826_ = v___x_1831_;
goto v___jp_1825_;
}
v___jp_1825_:
{
size_t v___x_1827_; size_t v___x_1828_; 
v___x_1827_ = ((size_t)1ULL);
v___x_1828_ = lean_usize_add(v_i_1810_, v___x_1827_);
v_i_1810_ = v___x_1828_;
v_b_1812_ = v_a_1826_;
goto _start;
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v_b_1812_);
lean_dec_ref(v_f_1808_);
v_a_1832_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1823_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1823_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v___x_1840_; 
lean_dec_ref(v_f_1808_);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_b_1812_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0___boxed(lean_object* v_pu_1841_, lean_object* v_f_1842_, lean_object* v_as_1843_, lean_object* v_i_1844_, lean_object* v_stop_1845_, lean_object* v_b_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
uint8_t v_pu_boxed_1852_; size_t v_i_boxed_1853_; size_t v_stop_boxed_1854_; lean_object* v_res_1855_; 
v_pu_boxed_1852_ = lean_unbox(v_pu_1841_);
v_i_boxed_1853_ = lean_unbox_usize(v_i_1844_);
lean_dec(v_i_1844_);
v_stop_boxed_1854_ = lean_unbox_usize(v_stop_1845_);
lean_dec(v_stop_1845_);
v_res_1855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_boxed_1852_, v_f_1842_, v_as_1843_, v_i_boxed_1853_, v_stop_boxed_1854_, v_b_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec_ref(v_as_1843_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun(uint8_t v_pu_1856_, lean_object* v_f_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = lean_array_get_size(v_a_1858_);
v___x_1866_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1867_ = lean_nat_dec_lt(v___x_1864_, v___x_1865_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v_f_1857_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
return v___x_1868_;
}
else
{
uint8_t v___x_1869_; 
v___x_1869_ = lean_nat_dec_le(v___x_1865_, v___x_1865_);
if (v___x_1869_ == 0)
{
if (v___x_1867_ == 0)
{
lean_object* v___x_1870_; 
lean_dec_ref(v_f_1857_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1866_);
return v___x_1870_;
}
else
{
size_t v___x_1871_; size_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = ((size_t)0ULL);
v___x_1872_ = lean_usize_of_nat(v___x_1865_);
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1856_, v_f_1857_, v_a_1858_, v___x_1871_, v___x_1872_, v___x_1866_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
return v___x_1873_;
}
}
else
{
size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = lean_usize_of_nat(v___x_1865_);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1856_, v_f_1857_, v_a_1858_, v___x_1874_, v___x_1875_, v___x_1866_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun___boxed(lean_object* v_pu_1877_, lean_object* v_f_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
uint8_t v_pu_boxed_1885_; lean_object* v_res_1886_; 
v_pu_boxed_1885_ = lean_unbox(v_pu_1877_);
v_res_1886_ = l_Lean_Compiler_LCNF_Probe_filterByFun(v_pu_boxed_1885_, v_f_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec_ref(v_a_1879_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(uint8_t v_pu_1887_, lean_object* v_f_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
switch(lean_obj_tag(v_a_1889_))
{
case 0:
{
lean_object* v_k_1895_; 
v_k_1895_ = lean_ctor_get(v_a_1889_, 1);
lean_inc_ref(v_k_1895_);
lean_dec_ref_known(v_a_1889_, 2);
v_a_1889_ = v_k_1895_;
goto _start;
}
case 1:
{
lean_object* v_decl_1897_; lean_object* v_k_1898_; lean_object* v_value_1899_; lean_object* v___x_1900_; 
v_decl_1897_ = lean_ctor_get(v_a_1889_, 0);
lean_inc_ref(v_decl_1897_);
v_k_1898_ = lean_ctor_get(v_a_1889_, 1);
lean_inc_ref(v_k_1898_);
lean_dec_ref_known(v_a_1889_, 2);
v_value_1899_ = lean_ctor_get(v_decl_1897_, 4);
lean_inc_ref(v_value_1899_);
lean_dec_ref(v_decl_1897_);
lean_inc_ref(v_f_1888_);
v___x_1900_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1887_, v_f_1888_, v_value_1899_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; uint8_t v___x_1902_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
v___x_1902_ = lean_unbox(v_a_1901_);
lean_dec(v_a_1901_);
if (v___x_1902_ == 0)
{
lean_dec_ref_known(v___x_1900_, 1);
v_a_1889_ = v_k_1898_;
goto _start;
}
else
{
lean_dec_ref(v_k_1898_);
lean_dec_ref(v_f_1888_);
return v___x_1900_;
}
}
else
{
lean_dec_ref(v_k_1898_);
lean_dec_ref(v_f_1888_);
return v___x_1900_;
}
}
case 2:
{
lean_object* v_decl_1904_; lean_object* v_k_1905_; lean_object* v___x_1906_; 
v_decl_1904_ = lean_ctor_get(v_a_1889_, 0);
lean_inc_ref_n(v_decl_1904_, 2);
v_k_1905_ = lean_ctor_get(v_a_1889_, 1);
lean_inc_ref(v_k_1905_);
lean_dec_ref_known(v_a_1889_, 2);
lean_inc_ref(v_f_1888_);
lean_inc(v_a_1893_);
lean_inc_ref(v_a_1892_);
lean_inc(v_a_1891_);
lean_inc_ref(v_a_1890_);
v___x_1906_ = lean_apply_6(v_f_1888_, v_decl_1904_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, lean_box(0));
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; uint8_t v___x_1908_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
v___x_1908_ = lean_unbox(v_a_1907_);
lean_dec(v_a_1907_);
if (v___x_1908_ == 0)
{
lean_object* v_value_1909_; lean_object* v___x_1910_; 
lean_dec_ref_known(v___x_1906_, 1);
v_value_1909_ = lean_ctor_get(v_decl_1904_, 4);
lean_inc_ref(v_value_1909_);
lean_dec_ref(v_decl_1904_);
lean_inc_ref(v_f_1888_);
v___x_1910_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1887_, v_f_1888_, v_value_1909_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; uint8_t v___x_1912_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
v___x_1912_ = lean_unbox(v_a_1911_);
lean_dec(v_a_1911_);
if (v___x_1912_ == 0)
{
lean_dec_ref_known(v___x_1910_, 1);
v_a_1889_ = v_k_1905_;
goto _start;
}
else
{
lean_dec_ref(v_k_1905_);
lean_dec_ref(v_f_1888_);
return v___x_1910_;
}
}
else
{
lean_dec_ref(v_k_1905_);
lean_dec_ref(v_f_1888_);
return v___x_1910_;
}
}
else
{
lean_dec_ref(v_k_1905_);
lean_dec_ref(v_decl_1904_);
lean_dec_ref(v_f_1888_);
return v___x_1906_;
}
}
else
{
lean_dec_ref(v_k_1905_);
lean_dec_ref(v_decl_1904_);
lean_dec_ref(v_f_1888_);
return v___x_1906_;
}
}
case 4:
{
lean_object* v_cases_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1933_; 
v_cases_1914_ = lean_ctor_get(v_a_1889_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_a_1889_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1916_ = v_a_1889_;
v_isShared_1917_ = v_isSharedCheck_1933_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_cases_1914_);
lean_dec(v_a_1889_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1933_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_alts_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v_alts_1918_ = lean_ctor_get(v_cases_1914_, 3);
lean_inc_ref(v_alts_1918_);
lean_dec_ref(v_cases_1914_);
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = lean_array_get_size(v_alts_1918_);
v___x_1921_ = lean_nat_dec_lt(v___x_1919_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
lean_dec_ref(v_alts_1918_);
lean_dec_ref(v_f_1888_);
v___x_1922_ = lean_box(v___x_1921_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1922_);
v___x_1924_ = v___x_1916_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
else
{
if (v___x_1921_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
lean_dec_ref(v_alts_1918_);
lean_dec_ref(v_f_1888_);
v___x_1926_ = lean_box(v___x_1921_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1926_);
v___x_1928_ = v___x_1916_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
else
{
size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
lean_del_object(v___x_1916_);
v___x_1930_ = ((size_t)0ULL);
v___x_1931_ = lean_usize_of_nat(v___x_1920_);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_1887_, v_f_1888_, v_alts_1918_, v___x_1930_, v___x_1931_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
lean_dec_ref(v_alts_1918_);
return v___x_1932_;
}
}
}
}
case 7:
{
lean_object* v_k_1934_; 
v_k_1934_ = lean_ctor_get(v_a_1889_, 3);
lean_inc_ref(v_k_1934_);
lean_dec_ref_known(v_a_1889_, 4);
v_a_1889_ = v_k_1934_;
goto _start;
}
case 8:
{
lean_object* v_k_1936_; 
v_k_1936_ = lean_ctor_get(v_a_1889_, 3);
lean_inc_ref(v_k_1936_);
lean_dec_ref_known(v_a_1889_, 4);
v_a_1889_ = v_k_1936_;
goto _start;
}
case 9:
{
lean_object* v_k_1938_; 
v_k_1938_ = lean_ctor_get(v_a_1889_, 5);
lean_inc_ref(v_k_1938_);
lean_dec_ref_known(v_a_1889_, 6);
v_a_1889_ = v_k_1938_;
goto _start;
}
case 10:
{
lean_object* v_k_1940_; 
v_k_1940_ = lean_ctor_get(v_a_1889_, 2);
lean_inc_ref(v_k_1940_);
lean_dec_ref_known(v_a_1889_, 3);
v_a_1889_ = v_k_1940_;
goto _start;
}
case 11:
{
lean_object* v_k_1942_; 
v_k_1942_ = lean_ctor_get(v_a_1889_, 2);
lean_inc_ref(v_k_1942_);
lean_dec_ref_known(v_a_1889_, 3);
v_a_1889_ = v_k_1942_;
goto _start;
}
case 12:
{
lean_object* v_k_1944_; 
v_k_1944_ = lean_ctor_get(v_a_1889_, 3);
lean_inc_ref(v_k_1944_);
lean_dec_ref_known(v_a_1889_, 4);
v_a_1889_ = v_k_1944_;
goto _start;
}
case 13:
{
lean_object* v_k_1946_; 
v_k_1946_ = lean_ctor_get(v_a_1889_, 1);
lean_inc_ref(v_k_1946_);
lean_dec_ref_known(v_a_1889_, 2);
v_a_1889_ = v_k_1946_;
goto _start;
}
default: 
{
uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
lean_dec_ref(v_a_1889_);
lean_dec_ref(v_f_1888_);
v___x_1948_ = 0;
v___x_1949_ = lean_box(v___x_1948_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
return v___x_1950_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(uint8_t v_pu_1951_, lean_object* v_f_1952_, lean_object* v_as_1953_, size_t v_i_1954_, size_t v_stop_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_usize_dec_eq(v_i_1954_, v_stop_1955_);
if (v___x_1961_ == 0)
{
uint8_t v___x_1962_; lean_object* v___y_1964_; lean_object* v___x_1979_; 
v___x_1962_ = 1;
v___x_1979_ = lean_array_uget_borrowed(v_as_1953_, v_i_1954_);
switch(lean_obj_tag(v___x_1979_))
{
case 0:
{
lean_object* v_code_1980_; 
v_code_1980_ = lean_ctor_get(v___x_1979_, 2);
lean_inc_ref(v_code_1980_);
v___y_1964_ = v_code_1980_;
goto v___jp_1963_;
}
case 1:
{
lean_object* v_code_1981_; 
v_code_1981_ = lean_ctor_get(v___x_1979_, 1);
lean_inc_ref(v_code_1981_);
v___y_1964_ = v_code_1981_;
goto v___jp_1963_;
}
default: 
{
lean_object* v_code_1982_; 
v_code_1982_ = lean_ctor_get(v___x_1979_, 0);
lean_inc_ref(v_code_1982_);
v___y_1964_ = v_code_1982_;
goto v___jp_1963_;
}
}
v___jp_1963_:
{
lean_object* v___x_1965_; 
lean_inc_ref(v_f_1952_);
v___x_1965_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1951_, v_f_1952_, v___y_1964_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1978_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1978_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1978_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_unbox(v_a_1966_);
lean_dec(v_a_1966_);
if (v___x_1970_ == 0)
{
size_t v___x_1971_; size_t v___x_1972_; 
lean_del_object(v___x_1968_);
v___x_1971_ = ((size_t)1ULL);
v___x_1972_ = lean_usize_add(v_i_1954_, v___x_1971_);
v_i_1954_ = v___x_1972_;
goto _start;
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
lean_dec_ref(v_f_1952_);
v___x_1974_ = lean_box(v___x_1962_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1974_);
v___x_1976_ = v___x_1968_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
else
{
lean_dec_ref(v_f_1952_);
return v___x_1965_;
}
}
}
else
{
uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec_ref(v_f_1952_);
v___x_1983_ = 0;
v___x_1984_ = lean_box(v___x_1983_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0___boxed(lean_object* v_pu_1986_, lean_object* v_f_1987_, lean_object* v_as_1988_, lean_object* v_i_1989_, lean_object* v_stop_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
uint8_t v_pu_boxed_1996_; size_t v_i_boxed_1997_; size_t v_stop_boxed_1998_; lean_object* v_res_1999_; 
v_pu_boxed_1996_ = lean_unbox(v_pu_1986_);
v_i_boxed_1997_ = lean_unbox_usize(v_i_1989_);
lean_dec(v_i_1989_);
v_stop_boxed_1998_ = lean_unbox_usize(v_stop_1990_);
lean_dec(v_stop_1990_);
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_boxed_1996_, v_f_1987_, v_as_1988_, v_i_boxed_1997_, v_stop_boxed_1998_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec_ref(v_as_1988_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed(lean_object* v_pu_2000_, lean_object* v_f_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
uint8_t v_pu_boxed_2008_; lean_object* v_res_2009_; 
v_pu_boxed_2008_ = lean_unbox(v_pu_2000_);
v_res_2009_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_boxed_2008_, v_f_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(uint8_t v_pu_2010_, lean_object* v_f_2011_, lean_object* v_as_2012_, size_t v_i_2013_, size_t v_stop_2014_, lean_object* v_b_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_usize_dec_eq(v_i_2013_, v_stop_2014_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v_value_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2022_ = lean_array_uget_borrowed(v_as_2012_, v_i_2013_);
v_value_2023_ = lean_ctor_get(v___x_2022_, 1);
v___x_2024_ = lean_box(v_pu_2010_);
lean_inc_ref(v_f_2011_);
v___x_2025_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed), 8, 2);
lean_closure_set(v___x_2025_, 0, v___x_2024_);
lean_closure_set(v___x_2025_, 1, v_f_2011_);
lean_inc_ref(v_value_2023_);
v___x_2026_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2023_, v___x_2025_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v_a_2029_; uint8_t v___x_2033_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2033_ = lean_unbox(v_a_2027_);
lean_dec(v_a_2027_);
if (v___x_2033_ == 0)
{
v_a_2029_ = v_b_2015_;
goto v___jp_2028_;
}
else
{
lean_object* v___x_2034_; 
lean_inc(v___x_2022_);
v___x_2034_ = lean_array_push(v_b_2015_, v___x_2022_);
v_a_2029_ = v___x_2034_;
goto v___jp_2028_;
}
v___jp_2028_:
{
size_t v___x_2030_; size_t v___x_2031_; 
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = lean_usize_add(v_i_2013_, v___x_2030_);
v_i_2013_ = v___x_2031_;
v_b_2015_ = v_a_2029_;
goto _start;
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_b_2015_);
lean_dec_ref(v_f_2011_);
v_a_2035_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2026_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2026_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v___x_2043_; 
lean_dec_ref(v_f_2011_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_b_2015_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0___boxed(lean_object* v_pu_2044_, lean_object* v_f_2045_, lean_object* v_as_2046_, lean_object* v_i_2047_, lean_object* v_stop_2048_, lean_object* v_b_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
uint8_t v_pu_boxed_2055_; size_t v_i_boxed_2056_; size_t v_stop_boxed_2057_; lean_object* v_res_2058_; 
v_pu_boxed_2055_ = lean_unbox(v_pu_2044_);
v_i_boxed_2056_ = lean_unbox_usize(v_i_2047_);
lean_dec(v_i_2047_);
v_stop_boxed_2057_ = lean_unbox_usize(v_stop_2048_);
lean_dec(v_stop_2048_);
v_res_2058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_boxed_2055_, v_f_2045_, v_as_2046_, v_i_boxed_2056_, v_stop_boxed_2057_, v_b_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec_ref(v_as_2046_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp(uint8_t v_pu_2059_, lean_object* v_f_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = lean_array_get_size(v_a_2061_);
v___x_2069_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2070_ = lean_nat_dec_lt(v___x_2067_, v___x_2068_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
lean_dec_ref(v_f_2060_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
return v___x_2071_;
}
else
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_nat_dec_le(v___x_2068_, v___x_2068_);
if (v___x_2072_ == 0)
{
if (v___x_2070_ == 0)
{
lean_object* v___x_2073_; 
lean_dec_ref(v_f_2060_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2069_);
return v___x_2073_;
}
else
{
size_t v___x_2074_; size_t v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = ((size_t)0ULL);
v___x_2075_ = lean_usize_of_nat(v___x_2068_);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_2059_, v_f_2060_, v_a_2061_, v___x_2074_, v___x_2075_, v___x_2069_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
return v___x_2076_;
}
}
else
{
size_t v___x_2077_; size_t v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = ((size_t)0ULL);
v___x_2078_ = lean_usize_of_nat(v___x_2068_);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_2059_, v_f_2060_, v_a_2061_, v___x_2077_, v___x_2078_, v___x_2069_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
return v___x_2079_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp___boxed(lean_object* v_pu_2080_, lean_object* v_f_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
uint8_t v_pu_boxed_2088_; lean_object* v_res_2089_; 
v_pu_boxed_2088_ = lean_unbox(v_pu_2080_);
v_res_2089_ = l_Lean_Compiler_LCNF_Probe_filterByJp(v_pu_boxed_2088_, v_f_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(uint8_t v_pu_2090_, lean_object* v_f_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
switch(lean_obj_tag(v_a_2092_))
{
case 0:
{
lean_object* v_k_2098_; 
v_k_2098_ = lean_ctor_get(v_a_2092_, 1);
lean_inc_ref(v_k_2098_);
lean_dec_ref_known(v_a_2092_, 2);
v_a_2092_ = v_k_2098_;
goto _start;
}
case 1:
{
lean_object* v_decl_2100_; lean_object* v_k_2101_; lean_object* v___x_2102_; 
v_decl_2100_ = lean_ctor_get(v_a_2092_, 0);
lean_inc_ref_n(v_decl_2100_, 2);
v_k_2101_ = lean_ctor_get(v_a_2092_, 1);
lean_inc_ref(v_k_2101_);
lean_dec_ref_known(v_a_2092_, 2);
lean_inc_ref(v_f_2091_);
lean_inc(v_a_2096_);
lean_inc_ref(v_a_2095_);
lean_inc(v_a_2094_);
lean_inc_ref(v_a_2093_);
v___x_2102_ = lean_apply_6(v_f_2091_, v_decl_2100_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, lean_box(0));
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; uint8_t v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
v___x_2104_ = lean_unbox(v_a_2103_);
lean_dec(v_a_2103_);
if (v___x_2104_ == 0)
{
lean_object* v_value_2105_; lean_object* v___x_2106_; 
lean_dec_ref_known(v___x_2102_, 1);
v_value_2105_ = lean_ctor_get(v_decl_2100_, 4);
lean_inc_ref(v_value_2105_);
lean_dec_ref(v_decl_2100_);
lean_inc_ref(v_f_2091_);
v___x_2106_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2090_, v_f_2091_, v_value_2105_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; uint8_t v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
v___x_2108_ = lean_unbox(v_a_2107_);
lean_dec(v_a_2107_);
if (v___x_2108_ == 0)
{
lean_dec_ref_known(v___x_2106_, 1);
v_a_2092_ = v_k_2101_;
goto _start;
}
else
{
lean_dec_ref(v_k_2101_);
lean_dec_ref(v_f_2091_);
return v___x_2106_;
}
}
else
{
lean_dec_ref(v_k_2101_);
lean_dec_ref(v_f_2091_);
return v___x_2106_;
}
}
else
{
lean_dec_ref(v_k_2101_);
lean_dec_ref(v_decl_2100_);
lean_dec_ref(v_f_2091_);
return v___x_2102_;
}
}
else
{
lean_dec_ref(v_k_2101_);
lean_dec_ref(v_decl_2100_);
lean_dec_ref(v_f_2091_);
return v___x_2102_;
}
}
case 2:
{
lean_object* v_decl_2110_; lean_object* v_k_2111_; lean_object* v___x_2112_; 
v_decl_2110_ = lean_ctor_get(v_a_2092_, 0);
lean_inc_ref_n(v_decl_2110_, 2);
v_k_2111_ = lean_ctor_get(v_a_2092_, 1);
lean_inc_ref(v_k_2111_);
lean_dec_ref_known(v_a_2092_, 2);
lean_inc_ref(v_f_2091_);
lean_inc(v_a_2096_);
lean_inc_ref(v_a_2095_);
lean_inc(v_a_2094_);
lean_inc_ref(v_a_2093_);
v___x_2112_ = lean_apply_6(v_f_2091_, v_decl_2110_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, lean_box(0));
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; uint8_t v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
v___x_2114_ = lean_unbox(v_a_2113_);
lean_dec(v_a_2113_);
if (v___x_2114_ == 0)
{
lean_object* v_value_2115_; lean_object* v___x_2116_; 
lean_dec_ref_known(v___x_2112_, 1);
v_value_2115_ = lean_ctor_get(v_decl_2110_, 4);
lean_inc_ref(v_value_2115_);
lean_dec_ref(v_decl_2110_);
lean_inc_ref(v_f_2091_);
v___x_2116_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2090_, v_f_2091_, v_value_2115_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; uint8_t v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
v___x_2118_ = lean_unbox(v_a_2117_);
lean_dec(v_a_2117_);
if (v___x_2118_ == 0)
{
lean_dec_ref_known(v___x_2116_, 1);
v_a_2092_ = v_k_2111_;
goto _start;
}
else
{
lean_dec_ref(v_k_2111_);
lean_dec_ref(v_f_2091_);
return v___x_2116_;
}
}
else
{
lean_dec_ref(v_k_2111_);
lean_dec_ref(v_f_2091_);
return v___x_2116_;
}
}
else
{
lean_dec_ref(v_k_2111_);
lean_dec_ref(v_decl_2110_);
lean_dec_ref(v_f_2091_);
return v___x_2112_;
}
}
else
{
lean_dec_ref(v_k_2111_);
lean_dec_ref(v_decl_2110_);
lean_dec_ref(v_f_2091_);
return v___x_2112_;
}
}
case 4:
{
lean_object* v_cases_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2139_; 
v_cases_2120_ = lean_ctor_get(v_a_2092_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_a_2092_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2122_ = v_a_2092_;
v_isShared_2123_ = v_isSharedCheck_2139_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_cases_2120_);
lean_dec(v_a_2092_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2139_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v_alts_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v_alts_2124_ = lean_ctor_get(v_cases_2120_, 3);
lean_inc_ref(v_alts_2124_);
lean_dec_ref(v_cases_2120_);
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = lean_array_get_size(v_alts_2124_);
v___x_2127_ = lean_nat_dec_lt(v___x_2125_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
lean_dec_ref(v_alts_2124_);
lean_dec_ref(v_f_2091_);
v___x_2128_ = lean_box(v___x_2127_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set_tag(v___x_2122_, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2128_);
v___x_2130_ = v___x_2122_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
else
{
if (v___x_2127_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
lean_dec_ref(v_alts_2124_);
lean_dec_ref(v_f_2091_);
v___x_2132_ = lean_box(v___x_2127_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set_tag(v___x_2122_, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2132_);
v___x_2134_ = v___x_2122_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
else
{
size_t v___x_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
lean_del_object(v___x_2122_);
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = lean_usize_of_nat(v___x_2126_);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_2090_, v_f_2091_, v_alts_2124_, v___x_2136_, v___x_2137_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
lean_dec_ref(v_alts_2124_);
return v___x_2138_;
}
}
}
}
case 7:
{
lean_object* v_k_2140_; 
v_k_2140_ = lean_ctor_get(v_a_2092_, 3);
lean_inc_ref(v_k_2140_);
lean_dec_ref_known(v_a_2092_, 4);
v_a_2092_ = v_k_2140_;
goto _start;
}
case 8:
{
lean_object* v_k_2142_; 
v_k_2142_ = lean_ctor_get(v_a_2092_, 3);
lean_inc_ref(v_k_2142_);
lean_dec_ref_known(v_a_2092_, 4);
v_a_2092_ = v_k_2142_;
goto _start;
}
case 9:
{
lean_object* v_k_2144_; 
v_k_2144_ = lean_ctor_get(v_a_2092_, 5);
lean_inc_ref(v_k_2144_);
lean_dec_ref_known(v_a_2092_, 6);
v_a_2092_ = v_k_2144_;
goto _start;
}
case 10:
{
lean_object* v_k_2146_; 
v_k_2146_ = lean_ctor_get(v_a_2092_, 2);
lean_inc_ref(v_k_2146_);
lean_dec_ref_known(v_a_2092_, 3);
v_a_2092_ = v_k_2146_;
goto _start;
}
case 11:
{
lean_object* v_k_2148_; 
v_k_2148_ = lean_ctor_get(v_a_2092_, 2);
lean_inc_ref(v_k_2148_);
lean_dec_ref_known(v_a_2092_, 3);
v_a_2092_ = v_k_2148_;
goto _start;
}
case 12:
{
lean_object* v_k_2150_; 
v_k_2150_ = lean_ctor_get(v_a_2092_, 3);
lean_inc_ref(v_k_2150_);
lean_dec_ref_known(v_a_2092_, 4);
v_a_2092_ = v_k_2150_;
goto _start;
}
case 13:
{
lean_object* v_k_2152_; 
v_k_2152_ = lean_ctor_get(v_a_2092_, 1);
lean_inc_ref(v_k_2152_);
lean_dec_ref_known(v_a_2092_, 2);
v_a_2092_ = v_k_2152_;
goto _start;
}
default: 
{
uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_dec_ref(v_a_2092_);
lean_dec_ref(v_f_2091_);
v___x_2154_ = 0;
v___x_2155_ = lean_box(v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
return v___x_2156_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(uint8_t v_pu_2157_, lean_object* v_f_2158_, lean_object* v_as_2159_, size_t v_i_2160_, size_t v_stop_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
uint8_t v___x_2167_; 
v___x_2167_ = lean_usize_dec_eq(v_i_2160_, v_stop_2161_);
if (v___x_2167_ == 0)
{
uint8_t v___x_2168_; lean_object* v___y_2170_; lean_object* v___x_2185_; 
v___x_2168_ = 1;
v___x_2185_ = lean_array_uget_borrowed(v_as_2159_, v_i_2160_);
switch(lean_obj_tag(v___x_2185_))
{
case 0:
{
lean_object* v_code_2186_; 
v_code_2186_ = lean_ctor_get(v___x_2185_, 2);
lean_inc_ref(v_code_2186_);
v___y_2170_ = v_code_2186_;
goto v___jp_2169_;
}
case 1:
{
lean_object* v_code_2187_; 
v_code_2187_ = lean_ctor_get(v___x_2185_, 1);
lean_inc_ref(v_code_2187_);
v___y_2170_ = v_code_2187_;
goto v___jp_2169_;
}
default: 
{
lean_object* v_code_2188_; 
v_code_2188_ = lean_ctor_get(v___x_2185_, 0);
lean_inc_ref(v_code_2188_);
v___y_2170_ = v_code_2188_;
goto v___jp_2169_;
}
}
v___jp_2169_:
{
lean_object* v___x_2171_; 
lean_inc_ref(v_f_2158_);
v___x_2171_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2157_, v_f_2158_, v___y_2170_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2184_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2184_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2184_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_unbox(v_a_2172_);
lean_dec(v_a_2172_);
if (v___x_2176_ == 0)
{
size_t v___x_2177_; size_t v___x_2178_; 
lean_del_object(v___x_2174_);
v___x_2177_ = ((size_t)1ULL);
v___x_2178_ = lean_usize_add(v_i_2160_, v___x_2177_);
v_i_2160_ = v___x_2178_;
goto _start;
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
lean_dec_ref(v_f_2158_);
v___x_2180_ = lean_box(v___x_2168_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2180_);
v___x_2182_ = v___x_2174_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_dec_ref(v_f_2158_);
return v___x_2171_;
}
}
}
else
{
uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec_ref(v_f_2158_);
v___x_2189_ = 0;
v___x_2190_ = lean_box(v___x_2189_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0___boxed(lean_object* v_pu_2192_, lean_object* v_f_2193_, lean_object* v_as_2194_, lean_object* v_i_2195_, lean_object* v_stop_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
uint8_t v_pu_boxed_2202_; size_t v_i_boxed_2203_; size_t v_stop_boxed_2204_; lean_object* v_res_2205_; 
v_pu_boxed_2202_ = lean_unbox(v_pu_2192_);
v_i_boxed_2203_ = lean_unbox_usize(v_i_2195_);
lean_dec(v_i_2195_);
v_stop_boxed_2204_ = lean_unbox_usize(v_stop_2196_);
lean_dec(v_stop_2196_);
v_res_2205_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_boxed_2202_, v_f_2193_, v_as_2194_, v_i_boxed_2203_, v_stop_boxed_2204_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec_ref(v_as_2194_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed(lean_object* v_pu_2206_, lean_object* v_f_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
uint8_t v_pu_boxed_2214_; lean_object* v_res_2215_; 
v_pu_boxed_2214_ = lean_unbox(v_pu_2206_);
v_res_2215_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_boxed_2214_, v_f_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(uint8_t v_pu_2216_, lean_object* v_f_2217_, lean_object* v_as_2218_, size_t v_i_2219_, size_t v_stop_2220_, lean_object* v_b_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
uint8_t v___x_2227_; 
v___x_2227_ = lean_usize_dec_eq(v_i_2219_, v_stop_2220_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v_value_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2228_ = lean_array_uget_borrowed(v_as_2218_, v_i_2219_);
v_value_2229_ = lean_ctor_get(v___x_2228_, 1);
v___x_2230_ = lean_box(v_pu_2216_);
lean_inc_ref(v_f_2217_);
v___x_2231_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed), 8, 2);
lean_closure_set(v___x_2231_, 0, v___x_2230_);
lean_closure_set(v___x_2231_, 1, v_f_2217_);
lean_inc_ref(v_value_2229_);
v___x_2232_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2229_, v___x_2231_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v_a_2235_; uint8_t v___x_2239_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v___x_2239_ = lean_unbox(v_a_2233_);
lean_dec(v_a_2233_);
if (v___x_2239_ == 0)
{
v_a_2235_ = v_b_2221_;
goto v___jp_2234_;
}
else
{
lean_object* v___x_2240_; 
lean_inc(v___x_2228_);
v___x_2240_ = lean_array_push(v_b_2221_, v___x_2228_);
v_a_2235_ = v___x_2240_;
goto v___jp_2234_;
}
v___jp_2234_:
{
size_t v___x_2236_; size_t v___x_2237_; 
v___x_2236_ = ((size_t)1ULL);
v___x_2237_ = lean_usize_add(v_i_2219_, v___x_2236_);
v_i_2219_ = v___x_2237_;
v_b_2221_ = v_a_2235_;
goto _start;
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec_ref(v_b_2221_);
lean_dec_ref(v_f_2217_);
v_a_2241_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2232_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2232_);
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
else
{
lean_object* v___x_2249_; 
lean_dec_ref(v_f_2217_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_b_2221_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0___boxed(lean_object* v_pu_2250_, lean_object* v_f_2251_, lean_object* v_as_2252_, lean_object* v_i_2253_, lean_object* v_stop_2254_, lean_object* v_b_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
uint8_t v_pu_boxed_2261_; size_t v_i_boxed_2262_; size_t v_stop_boxed_2263_; lean_object* v_res_2264_; 
v_pu_boxed_2261_ = lean_unbox(v_pu_2250_);
v_i_boxed_2262_ = lean_unbox_usize(v_i_2253_);
lean_dec(v_i_2253_);
v_stop_boxed_2263_ = lean_unbox_usize(v_stop_2254_);
lean_dec(v_stop_2254_);
v_res_2264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_boxed_2261_, v_f_2251_, v_as_2252_, v_i_boxed_2262_, v_stop_boxed_2263_, v_b_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v_as_2252_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl(uint8_t v_pu_2265_, lean_object* v_f_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = lean_array_get_size(v_a_2267_);
v___x_2275_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2276_ = lean_nat_dec_lt(v___x_2273_, v___x_2274_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
lean_dec_ref(v_f_2266_);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2275_);
return v___x_2277_;
}
else
{
uint8_t v___x_2278_; 
v___x_2278_ = lean_nat_dec_le(v___x_2274_, v___x_2274_);
if (v___x_2278_ == 0)
{
if (v___x_2276_ == 0)
{
lean_object* v___x_2279_; 
lean_dec_ref(v_f_2266_);
v___x_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2275_);
return v___x_2279_;
}
else
{
size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = ((size_t)0ULL);
v___x_2281_ = lean_usize_of_nat(v___x_2274_);
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2265_, v_f_2266_, v_a_2267_, v___x_2280_, v___x_2281_, v___x_2275_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
return v___x_2282_;
}
}
else
{
size_t v___x_2283_; size_t v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = ((size_t)0ULL);
v___x_2284_ = lean_usize_of_nat(v___x_2274_);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2265_, v_f_2266_, v_a_2267_, v___x_2283_, v___x_2284_, v___x_2275_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
return v___x_2285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl___boxed(lean_object* v_pu_2286_, lean_object* v_f_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
uint8_t v_pu_boxed_2294_; lean_object* v_res_2295_; 
v_pu_boxed_2294_ = lean_unbox(v_pu_2286_);
v_res_2295_ = l_Lean_Compiler_LCNF_Probe_filterByFunDecl(v_pu_boxed_2294_, v_f_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec_ref(v_a_2288_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(uint8_t v_pu_2296_, lean_object* v_f_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
switch(lean_obj_tag(v_a_2298_))
{
case 0:
{
lean_object* v_k_2304_; 
v_k_2304_ = lean_ctor_get(v_a_2298_, 1);
lean_inc_ref(v_k_2304_);
lean_dec_ref_known(v_a_2298_, 2);
v_a_2298_ = v_k_2304_;
goto _start;
}
case 1:
{
lean_object* v_decl_2306_; lean_object* v_k_2307_; lean_object* v_value_2308_; lean_object* v___x_2309_; 
v_decl_2306_ = lean_ctor_get(v_a_2298_, 0);
lean_inc_ref(v_decl_2306_);
v_k_2307_ = lean_ctor_get(v_a_2298_, 1);
lean_inc_ref(v_k_2307_);
lean_dec_ref_known(v_a_2298_, 2);
v_value_2308_ = lean_ctor_get(v_decl_2306_, 4);
lean_inc_ref(v_value_2308_);
lean_dec_ref(v_decl_2306_);
lean_inc_ref(v_f_2297_);
v___x_2309_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2296_, v_f_2297_, v_value_2308_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; uint8_t v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
v___x_2311_ = lean_unbox(v_a_2310_);
lean_dec(v_a_2310_);
if (v___x_2311_ == 0)
{
lean_dec_ref_known(v___x_2309_, 1);
v_a_2298_ = v_k_2307_;
goto _start;
}
else
{
lean_dec_ref(v_k_2307_);
lean_dec_ref(v_f_2297_);
return v___x_2309_;
}
}
else
{
lean_dec_ref(v_k_2307_);
lean_dec_ref(v_f_2297_);
return v___x_2309_;
}
}
case 2:
{
lean_object* v_decl_2313_; lean_object* v_k_2314_; lean_object* v_value_2315_; lean_object* v___x_2316_; 
v_decl_2313_ = lean_ctor_get(v_a_2298_, 0);
lean_inc_ref(v_decl_2313_);
v_k_2314_ = lean_ctor_get(v_a_2298_, 1);
lean_inc_ref(v_k_2314_);
lean_dec_ref_known(v_a_2298_, 2);
v_value_2315_ = lean_ctor_get(v_decl_2313_, 4);
lean_inc_ref(v_value_2315_);
lean_dec_ref(v_decl_2313_);
lean_inc_ref(v_f_2297_);
v___x_2316_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2296_, v_f_2297_, v_value_2315_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; uint8_t v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
v___x_2318_ = lean_unbox(v_a_2317_);
lean_dec(v_a_2317_);
if (v___x_2318_ == 0)
{
lean_dec_ref_known(v___x_2316_, 1);
v_a_2298_ = v_k_2314_;
goto _start;
}
else
{
lean_dec_ref(v_k_2314_);
lean_dec_ref(v_f_2297_);
return v___x_2316_;
}
}
else
{
lean_dec_ref(v_k_2314_);
lean_dec_ref(v_f_2297_);
return v___x_2316_;
}
}
case 4:
{
lean_object* v_cases_2320_; lean_object* v___x_2321_; 
v_cases_2320_ = lean_ctor_get(v_a_2298_, 0);
lean_inc_ref_n(v_cases_2320_, 2);
lean_dec_ref_known(v_a_2298_, 1);
lean_inc_ref(v_f_2297_);
lean_inc(v_a_2302_);
lean_inc_ref(v_a_2301_);
lean_inc(v_a_2300_);
lean_inc_ref(v_a_2299_);
v___x_2321_ = lean_apply_6(v_f_2297_, v_cases_2320_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, lean_box(0));
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; uint8_t v___x_2323_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
v___x_2323_ = lean_unbox(v_a_2322_);
lean_dec(v_a_2322_);
if (v___x_2323_ == 0)
{
lean_object* v_alts_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_alts_2324_ = lean_ctor_get(v_cases_2320_, 3);
lean_inc_ref(v_alts_2324_);
lean_dec_ref(v_cases_2320_);
v___x_2325_ = lean_unsigned_to_nat(0u);
v___x_2326_ = lean_array_get_size(v_alts_2324_);
v___x_2327_ = lean_nat_dec_lt(v___x_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_dec_ref(v_alts_2324_);
lean_dec_ref(v_f_2297_);
return v___x_2321_;
}
else
{
if (v___x_2327_ == 0)
{
lean_dec_ref(v_alts_2324_);
lean_dec_ref(v_f_2297_);
return v___x_2321_;
}
else
{
size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; 
lean_dec_ref_known(v___x_2321_, 1);
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = lean_usize_of_nat(v___x_2326_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_2296_, v_f_2297_, v_alts_2324_, v___x_2328_, v___x_2329_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec_ref(v_alts_2324_);
return v___x_2330_;
}
}
}
else
{
lean_dec_ref(v_cases_2320_);
lean_dec_ref(v_f_2297_);
return v___x_2321_;
}
}
else
{
lean_dec_ref(v_cases_2320_);
lean_dec_ref(v_f_2297_);
return v___x_2321_;
}
}
case 7:
{
lean_object* v_k_2331_; 
v_k_2331_ = lean_ctor_get(v_a_2298_, 3);
lean_inc_ref(v_k_2331_);
lean_dec_ref_known(v_a_2298_, 4);
v_a_2298_ = v_k_2331_;
goto _start;
}
case 8:
{
lean_object* v_k_2333_; 
v_k_2333_ = lean_ctor_get(v_a_2298_, 3);
lean_inc_ref(v_k_2333_);
lean_dec_ref_known(v_a_2298_, 4);
v_a_2298_ = v_k_2333_;
goto _start;
}
case 9:
{
lean_object* v_k_2335_; 
v_k_2335_ = lean_ctor_get(v_a_2298_, 5);
lean_inc_ref(v_k_2335_);
lean_dec_ref_known(v_a_2298_, 6);
v_a_2298_ = v_k_2335_;
goto _start;
}
case 10:
{
lean_object* v_k_2337_; 
v_k_2337_ = lean_ctor_get(v_a_2298_, 2);
lean_inc_ref(v_k_2337_);
lean_dec_ref_known(v_a_2298_, 3);
v_a_2298_ = v_k_2337_;
goto _start;
}
case 11:
{
lean_object* v_k_2339_; 
v_k_2339_ = lean_ctor_get(v_a_2298_, 2);
lean_inc_ref(v_k_2339_);
lean_dec_ref_known(v_a_2298_, 3);
v_a_2298_ = v_k_2339_;
goto _start;
}
case 12:
{
lean_object* v_k_2341_; 
v_k_2341_ = lean_ctor_get(v_a_2298_, 3);
lean_inc_ref(v_k_2341_);
lean_dec_ref_known(v_a_2298_, 4);
v_a_2298_ = v_k_2341_;
goto _start;
}
case 13:
{
lean_object* v_k_2343_; 
v_k_2343_ = lean_ctor_get(v_a_2298_, 1);
lean_inc_ref(v_k_2343_);
lean_dec_ref_known(v_a_2298_, 2);
v_a_2298_ = v_k_2343_;
goto _start;
}
default: 
{
uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_dec_ref(v_a_2298_);
lean_dec_ref(v_f_2297_);
v___x_2345_ = 0;
v___x_2346_ = lean_box(v___x_2345_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(uint8_t v_pu_2348_, lean_object* v_f_2349_, lean_object* v_as_2350_, size_t v_i_2351_, size_t v_stop_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_usize_dec_eq(v_i_2351_, v_stop_2352_);
if (v___x_2358_ == 0)
{
uint8_t v___x_2359_; lean_object* v___y_2361_; lean_object* v___x_2376_; 
v___x_2359_ = 1;
v___x_2376_ = lean_array_uget_borrowed(v_as_2350_, v_i_2351_);
switch(lean_obj_tag(v___x_2376_))
{
case 0:
{
lean_object* v_code_2377_; 
v_code_2377_ = lean_ctor_get(v___x_2376_, 2);
lean_inc_ref(v_code_2377_);
v___y_2361_ = v_code_2377_;
goto v___jp_2360_;
}
case 1:
{
lean_object* v_code_2378_; 
v_code_2378_ = lean_ctor_get(v___x_2376_, 1);
lean_inc_ref(v_code_2378_);
v___y_2361_ = v_code_2378_;
goto v___jp_2360_;
}
default: 
{
lean_object* v_code_2379_; 
v_code_2379_ = lean_ctor_get(v___x_2376_, 0);
lean_inc_ref(v_code_2379_);
v___y_2361_ = v_code_2379_;
goto v___jp_2360_;
}
}
v___jp_2360_:
{
lean_object* v___x_2362_; 
lean_inc_ref(v_f_2349_);
v___x_2362_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2348_, v_f_2349_, v___y_2361_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2375_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2375_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2375_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
uint8_t v___x_2367_; 
v___x_2367_ = lean_unbox(v_a_2363_);
lean_dec(v_a_2363_);
if (v___x_2367_ == 0)
{
size_t v___x_2368_; size_t v___x_2369_; 
lean_del_object(v___x_2365_);
v___x_2368_ = ((size_t)1ULL);
v___x_2369_ = lean_usize_add(v_i_2351_, v___x_2368_);
v_i_2351_ = v___x_2369_;
goto _start;
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
lean_dec_ref(v_f_2349_);
v___x_2371_ = lean_box(v___x_2359_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2371_);
v___x_2373_ = v___x_2365_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_dec_ref(v_f_2349_);
return v___x_2362_;
}
}
}
else
{
uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec_ref(v_f_2349_);
v___x_2380_ = 0;
v___x_2381_ = lean_box(v___x_2380_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0___boxed(lean_object* v_pu_2383_, lean_object* v_f_2384_, lean_object* v_as_2385_, lean_object* v_i_2386_, lean_object* v_stop_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
uint8_t v_pu_boxed_2393_; size_t v_i_boxed_2394_; size_t v_stop_boxed_2395_; lean_object* v_res_2396_; 
v_pu_boxed_2393_ = lean_unbox(v_pu_2383_);
v_i_boxed_2394_ = lean_unbox_usize(v_i_2386_);
lean_dec(v_i_2386_);
v_stop_boxed_2395_ = lean_unbox_usize(v_stop_2387_);
lean_dec(v_stop_2387_);
v_res_2396_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_boxed_2393_, v_f_2384_, v_as_2385_, v_i_boxed_2394_, v_stop_boxed_2395_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec_ref(v_as_2385_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed(lean_object* v_pu_2397_, lean_object* v_f_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
uint8_t v_pu_boxed_2405_; lean_object* v_res_2406_; 
v_pu_boxed_2405_ = lean_unbox(v_pu_2397_);
v_res_2406_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_boxed_2405_, v_f_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(uint8_t v_pu_2407_, lean_object* v_f_2408_, lean_object* v_as_2409_, size_t v_i_2410_, size_t v_stop_2411_, lean_object* v_b_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
uint8_t v___x_2418_; 
v___x_2418_ = lean_usize_dec_eq(v_i_2410_, v_stop_2411_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v_value_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2419_ = lean_array_uget_borrowed(v_as_2409_, v_i_2410_);
v_value_2420_ = lean_ctor_get(v___x_2419_, 1);
v___x_2421_ = lean_box(v_pu_2407_);
lean_inc_ref(v_f_2408_);
v___x_2422_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed), 8, 2);
lean_closure_set(v___x_2422_, 0, v___x_2421_);
lean_closure_set(v___x_2422_, 1, v_f_2408_);
lean_inc_ref(v_value_2420_);
v___x_2423_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2420_, v___x_2422_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v_a_2426_; uint8_t v___x_2430_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v___x_2430_ = lean_unbox(v_a_2424_);
lean_dec(v_a_2424_);
if (v___x_2430_ == 0)
{
v_a_2426_ = v_b_2412_;
goto v___jp_2425_;
}
else
{
lean_object* v___x_2431_; 
lean_inc(v___x_2419_);
v___x_2431_ = lean_array_push(v_b_2412_, v___x_2419_);
v_a_2426_ = v___x_2431_;
goto v___jp_2425_;
}
v___jp_2425_:
{
size_t v___x_2427_; size_t v___x_2428_; 
v___x_2427_ = ((size_t)1ULL);
v___x_2428_ = lean_usize_add(v_i_2410_, v___x_2427_);
v_i_2410_ = v___x_2428_;
v_b_2412_ = v_a_2426_;
goto _start;
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec_ref(v_b_2412_);
lean_dec_ref(v_f_2408_);
v_a_2432_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2423_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2423_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v___x_2440_; 
lean_dec_ref(v_f_2408_);
v___x_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_b_2412_);
return v___x_2440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0___boxed(lean_object* v_pu_2441_, lean_object* v_f_2442_, lean_object* v_as_2443_, lean_object* v_i_2444_, lean_object* v_stop_2445_, lean_object* v_b_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
uint8_t v_pu_boxed_2452_; size_t v_i_boxed_2453_; size_t v_stop_boxed_2454_; lean_object* v_res_2455_; 
v_pu_boxed_2452_ = lean_unbox(v_pu_2441_);
v_i_boxed_2453_ = lean_unbox_usize(v_i_2444_);
lean_dec(v_i_2444_);
v_stop_boxed_2454_ = lean_unbox_usize(v_stop_2445_);
lean_dec(v_stop_2445_);
v_res_2455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_boxed_2452_, v_f_2442_, v_as_2443_, v_i_boxed_2453_, v_stop_boxed_2454_, v_b_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v_as_2443_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases(uint8_t v_pu_2456_, lean_object* v_f_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2464_ = lean_unsigned_to_nat(0u);
v___x_2465_ = lean_array_get_size(v_a_2458_);
v___x_2466_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2467_ = lean_nat_dec_lt(v___x_2464_, v___x_2465_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_dec_ref(v_f_2457_);
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
return v___x_2468_;
}
else
{
uint8_t v___x_2469_; 
v___x_2469_ = lean_nat_dec_le(v___x_2465_, v___x_2465_);
if (v___x_2469_ == 0)
{
if (v___x_2467_ == 0)
{
lean_object* v___x_2470_; 
lean_dec_ref(v_f_2457_);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2466_);
return v___x_2470_;
}
else
{
size_t v___x_2471_; size_t v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = ((size_t)0ULL);
v___x_2472_ = lean_usize_of_nat(v___x_2465_);
v___x_2473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2456_, v_f_2457_, v_a_2458_, v___x_2471_, v___x_2472_, v___x_2466_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
return v___x_2473_;
}
}
else
{
size_t v___x_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = ((size_t)0ULL);
v___x_2475_ = lean_usize_of_nat(v___x_2465_);
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2456_, v_f_2457_, v_a_2458_, v___x_2474_, v___x_2475_, v___x_2466_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases___boxed(lean_object* v_pu_2477_, lean_object* v_f_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
uint8_t v_pu_boxed_2485_; lean_object* v_res_2486_; 
v_pu_boxed_2485_ = lean_unbox(v_pu_2477_);
v_res_2486_ = l_Lean_Compiler_LCNF_Probe_filterByCases(v_pu_boxed_2485_, v_f_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec_ref(v_a_2479_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(uint8_t v_pu_2487_, lean_object* v_f_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
switch(lean_obj_tag(v_a_2489_))
{
case 0:
{
lean_object* v_k_2495_; 
v_k_2495_ = lean_ctor_get(v_a_2489_, 1);
lean_inc_ref(v_k_2495_);
lean_dec_ref_known(v_a_2489_, 2);
v_a_2489_ = v_k_2495_;
goto _start;
}
case 1:
{
lean_object* v_decl_2497_; lean_object* v_k_2498_; lean_object* v_value_2499_; lean_object* v___x_2500_; 
v_decl_2497_ = lean_ctor_get(v_a_2489_, 0);
lean_inc_ref(v_decl_2497_);
v_k_2498_ = lean_ctor_get(v_a_2489_, 1);
lean_inc_ref(v_k_2498_);
lean_dec_ref_known(v_a_2489_, 2);
v_value_2499_ = lean_ctor_get(v_decl_2497_, 4);
lean_inc_ref(v_value_2499_);
lean_dec_ref(v_decl_2497_);
lean_inc_ref(v_f_2488_);
v___x_2500_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2487_, v_f_2488_, v_value_2499_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; uint8_t v___x_2502_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
v___x_2502_ = lean_unbox(v_a_2501_);
lean_dec(v_a_2501_);
if (v___x_2502_ == 0)
{
lean_dec_ref_known(v___x_2500_, 1);
v_a_2489_ = v_k_2498_;
goto _start;
}
else
{
lean_dec_ref(v_k_2498_);
lean_dec_ref(v_f_2488_);
return v___x_2500_;
}
}
else
{
lean_dec_ref(v_k_2498_);
lean_dec_ref(v_f_2488_);
return v___x_2500_;
}
}
case 2:
{
lean_object* v_decl_2504_; lean_object* v_k_2505_; lean_object* v_value_2506_; lean_object* v___x_2507_; 
v_decl_2504_ = lean_ctor_get(v_a_2489_, 0);
lean_inc_ref(v_decl_2504_);
v_k_2505_ = lean_ctor_get(v_a_2489_, 1);
lean_inc_ref(v_k_2505_);
lean_dec_ref_known(v_a_2489_, 2);
v_value_2506_ = lean_ctor_get(v_decl_2504_, 4);
lean_inc_ref(v_value_2506_);
lean_dec_ref(v_decl_2504_);
lean_inc_ref(v_f_2488_);
v___x_2507_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2487_, v_f_2488_, v_value_2506_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; uint8_t v___x_2509_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
v___x_2509_ = lean_unbox(v_a_2508_);
lean_dec(v_a_2508_);
if (v___x_2509_ == 0)
{
lean_dec_ref_known(v___x_2507_, 1);
v_a_2489_ = v_k_2505_;
goto _start;
}
else
{
lean_dec_ref(v_k_2505_);
lean_dec_ref(v_f_2488_);
return v___x_2507_;
}
}
else
{
lean_dec_ref(v_k_2505_);
lean_dec_ref(v_f_2488_);
return v___x_2507_;
}
}
case 3:
{
lean_object* v_fvarId_2511_; lean_object* v_args_2512_; lean_object* v___x_2513_; 
v_fvarId_2511_ = lean_ctor_get(v_a_2489_, 0);
lean_inc(v_fvarId_2511_);
v_args_2512_ = lean_ctor_get(v_a_2489_, 1);
lean_inc_ref(v_args_2512_);
lean_dec_ref_known(v_a_2489_, 2);
lean_inc(v_a_2493_);
lean_inc_ref(v_a_2492_);
lean_inc(v_a_2491_);
lean_inc_ref(v_a_2490_);
v___x_2513_ = lean_apply_7(v_f_2488_, v_fvarId_2511_, v_args_2512_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, lean_box(0));
return v___x_2513_;
}
case 4:
{
lean_object* v_cases_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2533_; 
v_cases_2514_ = lean_ctor_get(v_a_2489_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_a_2489_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2516_ = v_a_2489_;
v_isShared_2517_ = v_isSharedCheck_2533_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_cases_2514_);
lean_dec(v_a_2489_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2533_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v_alts_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v_alts_2518_ = lean_ctor_get(v_cases_2514_, 3);
lean_inc_ref(v_alts_2518_);
lean_dec_ref(v_cases_2514_);
v___x_2519_ = lean_unsigned_to_nat(0u);
v___x_2520_ = lean_array_get_size(v_alts_2518_);
v___x_2521_ = lean_nat_dec_lt(v___x_2519_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
lean_dec_ref(v_alts_2518_);
lean_dec_ref(v_f_2488_);
v___x_2522_ = lean_box(v___x_2521_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set_tag(v___x_2516_, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2522_);
v___x_2524_ = v___x_2516_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
else
{
if (v___x_2521_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_dec_ref(v_alts_2518_);
lean_dec_ref(v_f_2488_);
v___x_2526_ = lean_box(v___x_2521_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set_tag(v___x_2516_, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2526_);
v___x_2528_ = v___x_2516_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
else
{
size_t v___x_2530_; size_t v___x_2531_; lean_object* v___x_2532_; 
lean_del_object(v___x_2516_);
v___x_2530_ = ((size_t)0ULL);
v___x_2531_ = lean_usize_of_nat(v___x_2520_);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_2487_, v_f_2488_, v_alts_2518_, v___x_2530_, v___x_2531_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
lean_dec_ref(v_alts_2518_);
return v___x_2532_;
}
}
}
}
case 7:
{
lean_object* v_k_2534_; 
v_k_2534_ = lean_ctor_get(v_a_2489_, 3);
lean_inc_ref(v_k_2534_);
lean_dec_ref_known(v_a_2489_, 4);
v_a_2489_ = v_k_2534_;
goto _start;
}
case 8:
{
lean_object* v_k_2536_; 
v_k_2536_ = lean_ctor_get(v_a_2489_, 3);
lean_inc_ref(v_k_2536_);
lean_dec_ref_known(v_a_2489_, 4);
v_a_2489_ = v_k_2536_;
goto _start;
}
case 9:
{
lean_object* v_k_2538_; 
v_k_2538_ = lean_ctor_get(v_a_2489_, 5);
lean_inc_ref(v_k_2538_);
lean_dec_ref_known(v_a_2489_, 6);
v_a_2489_ = v_k_2538_;
goto _start;
}
case 10:
{
lean_object* v_k_2540_; 
v_k_2540_ = lean_ctor_get(v_a_2489_, 2);
lean_inc_ref(v_k_2540_);
lean_dec_ref_known(v_a_2489_, 3);
v_a_2489_ = v_k_2540_;
goto _start;
}
case 11:
{
lean_object* v_k_2542_; 
v_k_2542_ = lean_ctor_get(v_a_2489_, 2);
lean_inc_ref(v_k_2542_);
lean_dec_ref_known(v_a_2489_, 3);
v_a_2489_ = v_k_2542_;
goto _start;
}
case 12:
{
lean_object* v_k_2544_; 
v_k_2544_ = lean_ctor_get(v_a_2489_, 3);
lean_inc_ref(v_k_2544_);
lean_dec_ref_known(v_a_2489_, 4);
v_a_2489_ = v_k_2544_;
goto _start;
}
case 13:
{
lean_object* v_k_2546_; 
v_k_2546_ = lean_ctor_get(v_a_2489_, 1);
lean_inc_ref(v_k_2546_);
lean_dec_ref_known(v_a_2489_, 2);
v_a_2489_ = v_k_2546_;
goto _start;
}
default: 
{
uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
lean_dec_ref(v_a_2489_);
lean_dec_ref(v_f_2488_);
v___x_2548_ = 0;
v___x_2549_ = lean_box(v___x_2548_);
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
return v___x_2550_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(uint8_t v_pu_2551_, lean_object* v_f_2552_, lean_object* v_as_2553_, size_t v_i_2554_, size_t v_stop_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
uint8_t v___x_2561_; 
v___x_2561_ = lean_usize_dec_eq(v_i_2554_, v_stop_2555_);
if (v___x_2561_ == 0)
{
uint8_t v___x_2562_; lean_object* v___y_2564_; lean_object* v___x_2579_; 
v___x_2562_ = 1;
v___x_2579_ = lean_array_uget_borrowed(v_as_2553_, v_i_2554_);
switch(lean_obj_tag(v___x_2579_))
{
case 0:
{
lean_object* v_code_2580_; 
v_code_2580_ = lean_ctor_get(v___x_2579_, 2);
lean_inc_ref(v_code_2580_);
v___y_2564_ = v_code_2580_;
goto v___jp_2563_;
}
case 1:
{
lean_object* v_code_2581_; 
v_code_2581_ = lean_ctor_get(v___x_2579_, 1);
lean_inc_ref(v_code_2581_);
v___y_2564_ = v_code_2581_;
goto v___jp_2563_;
}
default: 
{
lean_object* v_code_2582_; 
v_code_2582_ = lean_ctor_get(v___x_2579_, 0);
lean_inc_ref(v_code_2582_);
v___y_2564_ = v_code_2582_;
goto v___jp_2563_;
}
}
v___jp_2563_:
{
lean_object* v___x_2565_; 
lean_inc_ref(v_f_2552_);
v___x_2565_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2551_, v_f_2552_, v___y_2564_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2578_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2578_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2578_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
uint8_t v___x_2570_; 
v___x_2570_ = lean_unbox(v_a_2566_);
lean_dec(v_a_2566_);
if (v___x_2570_ == 0)
{
size_t v___x_2571_; size_t v___x_2572_; 
lean_del_object(v___x_2568_);
v___x_2571_ = ((size_t)1ULL);
v___x_2572_ = lean_usize_add(v_i_2554_, v___x_2571_);
v_i_2554_ = v___x_2572_;
goto _start;
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_dec_ref(v_f_2552_);
v___x_2574_ = lean_box(v___x_2562_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2574_);
v___x_2576_ = v___x_2568_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
lean_dec_ref(v_f_2552_);
return v___x_2565_;
}
}
}
else
{
uint8_t v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec_ref(v_f_2552_);
v___x_2583_ = 0;
v___x_2584_ = lean_box(v___x_2583_);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
return v___x_2585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0___boxed(lean_object* v_pu_2586_, lean_object* v_f_2587_, lean_object* v_as_2588_, lean_object* v_i_2589_, lean_object* v_stop_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
uint8_t v_pu_boxed_2596_; size_t v_i_boxed_2597_; size_t v_stop_boxed_2598_; lean_object* v_res_2599_; 
v_pu_boxed_2596_ = lean_unbox(v_pu_2586_);
v_i_boxed_2597_ = lean_unbox_usize(v_i_2589_);
lean_dec(v_i_2589_);
v_stop_boxed_2598_ = lean_unbox_usize(v_stop_2590_);
lean_dec(v_stop_2590_);
v_res_2599_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_boxed_2596_, v_f_2587_, v_as_2588_, v_i_boxed_2597_, v_stop_boxed_2598_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec_ref(v_as_2588_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed(lean_object* v_pu_2600_, lean_object* v_f_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
uint8_t v_pu_boxed_2608_; lean_object* v_res_2609_; 
v_pu_boxed_2608_ = lean_unbox(v_pu_2600_);
v_res_2609_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_boxed_2608_, v_f_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
lean_dec(v_a_2604_);
lean_dec_ref(v_a_2603_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(uint8_t v_pu_2610_, lean_object* v_f_2611_, lean_object* v_as_2612_, size_t v_i_2613_, size_t v_stop_2614_, lean_object* v_b_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
uint8_t v___x_2621_; 
v___x_2621_ = lean_usize_dec_eq(v_i_2613_, v_stop_2614_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; lean_object* v_value_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2622_ = lean_array_uget_borrowed(v_as_2612_, v_i_2613_);
v_value_2623_ = lean_ctor_get(v___x_2622_, 1);
v___x_2624_ = lean_box(v_pu_2610_);
lean_inc_ref(v_f_2611_);
v___x_2625_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed), 8, 2);
lean_closure_set(v___x_2625_, 0, v___x_2624_);
lean_closure_set(v___x_2625_, 1, v_f_2611_);
lean_inc_ref(v_value_2623_);
v___x_2626_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2623_, v___x_2625_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v_a_2629_; uint8_t v___x_2633_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2633_ = lean_unbox(v_a_2627_);
lean_dec(v_a_2627_);
if (v___x_2633_ == 0)
{
v_a_2629_ = v_b_2615_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2634_; 
lean_inc(v___x_2622_);
v___x_2634_ = lean_array_push(v_b_2615_, v___x_2622_);
v_a_2629_ = v___x_2634_;
goto v___jp_2628_;
}
v___jp_2628_:
{
size_t v___x_2630_; size_t v___x_2631_; 
v___x_2630_ = ((size_t)1ULL);
v___x_2631_ = lean_usize_add(v_i_2613_, v___x_2630_);
v_i_2613_ = v___x_2631_;
v_b_2615_ = v_a_2629_;
goto _start;
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec_ref(v_b_2615_);
lean_dec_ref(v_f_2611_);
v_a_2635_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2626_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2626_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v___x_2643_; 
lean_dec_ref(v_f_2611_);
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_b_2615_);
return v___x_2643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0___boxed(lean_object* v_pu_2644_, lean_object* v_f_2645_, lean_object* v_as_2646_, lean_object* v_i_2647_, lean_object* v_stop_2648_, lean_object* v_b_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v_pu_boxed_2655_; size_t v_i_boxed_2656_; size_t v_stop_boxed_2657_; lean_object* v_res_2658_; 
v_pu_boxed_2655_ = lean_unbox(v_pu_2644_);
v_i_boxed_2656_ = lean_unbox_usize(v_i_2647_);
lean_dec(v_i_2647_);
v_stop_boxed_2657_ = lean_unbox_usize(v_stop_2648_);
lean_dec(v_stop_2648_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_boxed_2655_, v_f_2645_, v_as_2646_, v_i_boxed_2656_, v_stop_boxed_2657_, v_b_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec_ref(v_as_2646_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp(uint8_t v_pu_2659_, lean_object* v_f_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2667_ = lean_unsigned_to_nat(0u);
v___x_2668_ = lean_array_get_size(v_a_2661_);
v___x_2669_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2670_ = lean_nat_dec_lt(v___x_2667_, v___x_2668_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
lean_dec_ref(v_f_2660_);
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2669_);
return v___x_2671_;
}
else
{
uint8_t v___x_2672_; 
v___x_2672_ = lean_nat_dec_le(v___x_2668_, v___x_2668_);
if (v___x_2672_ == 0)
{
if (v___x_2670_ == 0)
{
lean_object* v___x_2673_; 
lean_dec_ref(v_f_2660_);
v___x_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2669_);
return v___x_2673_;
}
else
{
size_t v___x_2674_; size_t v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = ((size_t)0ULL);
v___x_2675_ = lean_usize_of_nat(v___x_2668_);
v___x_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2659_, v_f_2660_, v_a_2661_, v___x_2674_, v___x_2675_, v___x_2669_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
return v___x_2676_;
}
}
else
{
size_t v___x_2677_; size_t v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = ((size_t)0ULL);
v___x_2678_ = lean_usize_of_nat(v___x_2668_);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2659_, v_f_2660_, v_a_2661_, v___x_2677_, v___x_2678_, v___x_2669_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_);
return v___x_2679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp___boxed(lean_object* v_pu_2680_, lean_object* v_f_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
uint8_t v_pu_boxed_2688_; lean_object* v_res_2689_; 
v_pu_boxed_2688_ = lean_unbox(v_pu_2680_);
v_res_2689_ = l_Lean_Compiler_LCNF_Probe_filterByJmp(v_pu_boxed_2688_, v_f_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec_ref(v_a_2682_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(uint8_t v_pu_2690_, lean_object* v_f_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
switch(lean_obj_tag(v_a_2692_))
{
case 0:
{
lean_object* v_k_2698_; 
v_k_2698_ = lean_ctor_get(v_a_2692_, 1);
lean_inc_ref(v_k_2698_);
lean_dec_ref_known(v_a_2692_, 2);
v_a_2692_ = v_k_2698_;
goto _start;
}
case 1:
{
lean_object* v_decl_2700_; lean_object* v_k_2701_; lean_object* v_value_2702_; lean_object* v___x_2703_; 
v_decl_2700_ = lean_ctor_get(v_a_2692_, 0);
lean_inc_ref(v_decl_2700_);
v_k_2701_ = lean_ctor_get(v_a_2692_, 1);
lean_inc_ref(v_k_2701_);
lean_dec_ref_known(v_a_2692_, 2);
v_value_2702_ = lean_ctor_get(v_decl_2700_, 4);
lean_inc_ref(v_value_2702_);
lean_dec_ref(v_decl_2700_);
lean_inc_ref(v_f_2691_);
v___x_2703_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2690_, v_f_2691_, v_value_2702_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; uint8_t v___x_2705_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
v___x_2705_ = lean_unbox(v_a_2704_);
lean_dec(v_a_2704_);
if (v___x_2705_ == 0)
{
lean_dec_ref_known(v___x_2703_, 1);
v_a_2692_ = v_k_2701_;
goto _start;
}
else
{
lean_dec_ref(v_k_2701_);
lean_dec_ref(v_f_2691_);
return v___x_2703_;
}
}
else
{
lean_dec_ref(v_k_2701_);
lean_dec_ref(v_f_2691_);
return v___x_2703_;
}
}
case 2:
{
lean_object* v_decl_2707_; lean_object* v_k_2708_; lean_object* v_value_2709_; lean_object* v___x_2710_; 
v_decl_2707_ = lean_ctor_get(v_a_2692_, 0);
lean_inc_ref(v_decl_2707_);
v_k_2708_ = lean_ctor_get(v_a_2692_, 1);
lean_inc_ref(v_k_2708_);
lean_dec_ref_known(v_a_2692_, 2);
v_value_2709_ = lean_ctor_get(v_decl_2707_, 4);
lean_inc_ref(v_value_2709_);
lean_dec_ref(v_decl_2707_);
lean_inc_ref(v_f_2691_);
v___x_2710_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2690_, v_f_2691_, v_value_2709_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; uint8_t v___x_2712_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
v___x_2712_ = lean_unbox(v_a_2711_);
lean_dec(v_a_2711_);
if (v___x_2712_ == 0)
{
lean_dec_ref_known(v___x_2710_, 1);
v_a_2692_ = v_k_2708_;
goto _start;
}
else
{
lean_dec_ref(v_k_2708_);
lean_dec_ref(v_f_2691_);
return v___x_2710_;
}
}
else
{
lean_dec_ref(v_k_2708_);
lean_dec_ref(v_f_2691_);
return v___x_2710_;
}
}
case 4:
{
lean_object* v_cases_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2733_; 
v_cases_2714_ = lean_ctor_get(v_a_2692_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_a_2692_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2716_ = v_a_2692_;
v_isShared_2717_ = v_isSharedCheck_2733_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_cases_2714_);
lean_dec(v_a_2692_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2733_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v_alts_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; 
v_alts_2718_ = lean_ctor_get(v_cases_2714_, 3);
lean_inc_ref(v_alts_2718_);
lean_dec_ref(v_cases_2714_);
v___x_2719_ = lean_unsigned_to_nat(0u);
v___x_2720_ = lean_array_get_size(v_alts_2718_);
v___x_2721_ = lean_nat_dec_lt(v___x_2719_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
lean_dec_ref(v_alts_2718_);
lean_dec_ref(v_f_2691_);
v___x_2722_ = lean_box(v___x_2721_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2722_);
v___x_2724_ = v___x_2716_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
else
{
if (v___x_2721_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
lean_dec_ref(v_alts_2718_);
lean_dec_ref(v_f_2691_);
v___x_2726_ = lean_box(v___x_2721_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2726_);
v___x_2728_ = v___x_2716_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
else
{
size_t v___x_2730_; size_t v___x_2731_; lean_object* v___x_2732_; 
lean_del_object(v___x_2716_);
v___x_2730_ = ((size_t)0ULL);
v___x_2731_ = lean_usize_of_nat(v___x_2720_);
v___x_2732_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_2690_, v_f_2691_, v_alts_2718_, v___x_2730_, v___x_2731_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
lean_dec_ref(v_alts_2718_);
return v___x_2732_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2734_; lean_object* v___x_2735_; 
v_fvarId_2734_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_fvarId_2734_);
lean_dec_ref_known(v_a_2692_, 1);
lean_inc(v_a_2696_);
lean_inc_ref(v_a_2695_);
lean_inc(v_a_2694_);
lean_inc_ref(v_a_2693_);
v___x_2735_ = lean_apply_6(v_f_2691_, v_fvarId_2734_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, lean_box(0));
return v___x_2735_;
}
case 7:
{
lean_object* v_k_2736_; 
v_k_2736_ = lean_ctor_get(v_a_2692_, 3);
lean_inc_ref(v_k_2736_);
lean_dec_ref_known(v_a_2692_, 4);
v_a_2692_ = v_k_2736_;
goto _start;
}
case 8:
{
lean_object* v_k_2738_; 
v_k_2738_ = lean_ctor_get(v_a_2692_, 3);
lean_inc_ref(v_k_2738_);
lean_dec_ref_known(v_a_2692_, 4);
v_a_2692_ = v_k_2738_;
goto _start;
}
case 9:
{
lean_object* v_k_2740_; 
v_k_2740_ = lean_ctor_get(v_a_2692_, 5);
lean_inc_ref(v_k_2740_);
lean_dec_ref_known(v_a_2692_, 6);
v_a_2692_ = v_k_2740_;
goto _start;
}
case 10:
{
lean_object* v_k_2742_; 
v_k_2742_ = lean_ctor_get(v_a_2692_, 2);
lean_inc_ref(v_k_2742_);
lean_dec_ref_known(v_a_2692_, 3);
v_a_2692_ = v_k_2742_;
goto _start;
}
case 11:
{
lean_object* v_k_2744_; 
v_k_2744_ = lean_ctor_get(v_a_2692_, 2);
lean_inc_ref(v_k_2744_);
lean_dec_ref_known(v_a_2692_, 3);
v_a_2692_ = v_k_2744_;
goto _start;
}
case 12:
{
lean_object* v_k_2746_; 
v_k_2746_ = lean_ctor_get(v_a_2692_, 3);
lean_inc_ref(v_k_2746_);
lean_dec_ref_known(v_a_2692_, 4);
v_a_2692_ = v_k_2746_;
goto _start;
}
case 13:
{
lean_object* v_k_2748_; 
v_k_2748_ = lean_ctor_get(v_a_2692_, 1);
lean_inc_ref(v_k_2748_);
lean_dec_ref_known(v_a_2692_, 2);
v_a_2692_ = v_k_2748_;
goto _start;
}
default: 
{
uint8_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_dec_ref(v_a_2692_);
lean_dec_ref(v_f_2691_);
v___x_2750_ = 0;
v___x_2751_ = lean_box(v___x_2750_);
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
return v___x_2752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(uint8_t v_pu_2753_, lean_object* v_f_2754_, lean_object* v_as_2755_, size_t v_i_2756_, size_t v_stop_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_usize_dec_eq(v_i_2756_, v_stop_2757_);
if (v___x_2763_ == 0)
{
uint8_t v___x_2764_; lean_object* v___y_2766_; lean_object* v___x_2781_; 
v___x_2764_ = 1;
v___x_2781_ = lean_array_uget_borrowed(v_as_2755_, v_i_2756_);
switch(lean_obj_tag(v___x_2781_))
{
case 0:
{
lean_object* v_code_2782_; 
v_code_2782_ = lean_ctor_get(v___x_2781_, 2);
lean_inc_ref(v_code_2782_);
v___y_2766_ = v_code_2782_;
goto v___jp_2765_;
}
case 1:
{
lean_object* v_code_2783_; 
v_code_2783_ = lean_ctor_get(v___x_2781_, 1);
lean_inc_ref(v_code_2783_);
v___y_2766_ = v_code_2783_;
goto v___jp_2765_;
}
default: 
{
lean_object* v_code_2784_; 
v_code_2784_ = lean_ctor_get(v___x_2781_, 0);
lean_inc_ref(v_code_2784_);
v___y_2766_ = v_code_2784_;
goto v___jp_2765_;
}
}
v___jp_2765_:
{
lean_object* v___x_2767_; 
lean_inc_ref(v_f_2754_);
v___x_2767_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2753_, v_f_2754_, v___y_2766_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2780_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2770_ = v___x_2767_;
v_isShared_2771_ = v_isSharedCheck_2780_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2767_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2780_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_unbox(v_a_2768_);
lean_dec(v_a_2768_);
if (v___x_2772_ == 0)
{
size_t v___x_2773_; size_t v___x_2774_; 
lean_del_object(v___x_2770_);
v___x_2773_ = ((size_t)1ULL);
v___x_2774_ = lean_usize_add(v_i_2756_, v___x_2773_);
v_i_2756_ = v___x_2774_;
goto _start;
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2778_; 
lean_dec_ref(v_f_2754_);
v___x_2776_ = lean_box(v___x_2764_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2776_);
v___x_2778_ = v___x_2770_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
else
{
lean_dec_ref(v_f_2754_);
return v___x_2767_;
}
}
}
else
{
uint8_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_dec_ref(v_f_2754_);
v___x_2785_ = 0;
v___x_2786_ = lean_box(v___x_2785_);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0___boxed(lean_object* v_pu_2788_, lean_object* v_f_2789_, lean_object* v_as_2790_, lean_object* v_i_2791_, lean_object* v_stop_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
uint8_t v_pu_boxed_2798_; size_t v_i_boxed_2799_; size_t v_stop_boxed_2800_; lean_object* v_res_2801_; 
v_pu_boxed_2798_ = lean_unbox(v_pu_2788_);
v_i_boxed_2799_ = lean_unbox_usize(v_i_2791_);
lean_dec(v_i_2791_);
v_stop_boxed_2800_ = lean_unbox_usize(v_stop_2792_);
lean_dec(v_stop_2792_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_boxed_2798_, v_f_2789_, v_as_2790_, v_i_boxed_2799_, v_stop_boxed_2800_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v_as_2790_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed(lean_object* v_pu_2802_, lean_object* v_f_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
uint8_t v_pu_boxed_2810_; lean_object* v_res_2811_; 
v_pu_boxed_2810_ = lean_unbox(v_pu_2802_);
v_res_2811_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_boxed_2810_, v_f_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(uint8_t v_pu_2812_, lean_object* v_f_2813_, lean_object* v_as_2814_, size_t v_i_2815_, size_t v_stop_2816_, lean_object* v_b_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
uint8_t v___x_2823_; 
v___x_2823_ = lean_usize_dec_eq(v_i_2815_, v_stop_2816_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v_value_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2824_ = lean_array_uget_borrowed(v_as_2814_, v_i_2815_);
v_value_2825_ = lean_ctor_get(v___x_2824_, 1);
v___x_2826_ = lean_box(v_pu_2812_);
lean_inc_ref(v_f_2813_);
v___x_2827_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed), 8, 2);
lean_closure_set(v___x_2827_, 0, v___x_2826_);
lean_closure_set(v___x_2827_, 1, v_f_2813_);
lean_inc_ref(v_value_2825_);
v___x_2828_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2825_, v___x_2827_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v_a_2831_; uint8_t v___x_2835_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
v___x_2835_ = lean_unbox(v_a_2829_);
lean_dec(v_a_2829_);
if (v___x_2835_ == 0)
{
v_a_2831_ = v_b_2817_;
goto v___jp_2830_;
}
else
{
lean_object* v___x_2836_; 
lean_inc(v___x_2824_);
v___x_2836_ = lean_array_push(v_b_2817_, v___x_2824_);
v_a_2831_ = v___x_2836_;
goto v___jp_2830_;
}
v___jp_2830_:
{
size_t v___x_2832_; size_t v___x_2833_; 
v___x_2832_ = ((size_t)1ULL);
v___x_2833_ = lean_usize_add(v_i_2815_, v___x_2832_);
v_i_2815_ = v___x_2833_;
v_b_2817_ = v_a_2831_;
goto _start;
}
}
else
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec_ref(v_b_2817_);
lean_dec_ref(v_f_2813_);
v_a_2837_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2828_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2828_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
else
{
lean_object* v___x_2845_; 
lean_dec_ref(v_f_2813_);
v___x_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2845_, 0, v_b_2817_);
return v___x_2845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0___boxed(lean_object* v_pu_2846_, lean_object* v_f_2847_, lean_object* v_as_2848_, lean_object* v_i_2849_, lean_object* v_stop_2850_, lean_object* v_b_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
uint8_t v_pu_boxed_2857_; size_t v_i_boxed_2858_; size_t v_stop_boxed_2859_; lean_object* v_res_2860_; 
v_pu_boxed_2857_ = lean_unbox(v_pu_2846_);
v_i_boxed_2858_ = lean_unbox_usize(v_i_2849_);
lean_dec(v_i_2849_);
v_stop_boxed_2859_ = lean_unbox_usize(v_stop_2850_);
lean_dec(v_stop_2850_);
v_res_2860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_boxed_2857_, v_f_2847_, v_as_2848_, v_i_boxed_2858_, v_stop_boxed_2859_, v_b_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec_ref(v_as_2848_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn(uint8_t v_pu_2861_, lean_object* v_f_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = lean_array_get_size(v_a_2863_);
v___x_2871_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2872_ = lean_nat_dec_lt(v___x_2869_, v___x_2870_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; 
lean_dec_ref(v_f_2862_);
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2871_);
return v___x_2873_;
}
else
{
uint8_t v___x_2874_; 
v___x_2874_ = lean_nat_dec_le(v___x_2870_, v___x_2870_);
if (v___x_2874_ == 0)
{
if (v___x_2872_ == 0)
{
lean_object* v___x_2875_; 
lean_dec_ref(v_f_2862_);
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2871_);
return v___x_2875_;
}
else
{
size_t v___x_2876_; size_t v___x_2877_; lean_object* v___x_2878_; 
v___x_2876_ = ((size_t)0ULL);
v___x_2877_ = lean_usize_of_nat(v___x_2870_);
v___x_2878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2861_, v_f_2862_, v_a_2863_, v___x_2876_, v___x_2877_, v___x_2871_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
return v___x_2878_;
}
}
else
{
size_t v___x_2879_; size_t v___x_2880_; lean_object* v___x_2881_; 
v___x_2879_ = ((size_t)0ULL);
v___x_2880_ = lean_usize_of_nat(v___x_2870_);
v___x_2881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2861_, v_f_2862_, v_a_2863_, v___x_2879_, v___x_2880_, v___x_2871_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
return v___x_2881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn___boxed(lean_object* v_pu_2882_, lean_object* v_f_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
uint8_t v_pu_boxed_2890_; lean_object* v_res_2891_; 
v_pu_boxed_2890_ = lean_unbox(v_pu_2882_);
v_res_2891_ = l_Lean_Compiler_LCNF_Probe_filterByReturn(v_pu_boxed_2890_, v_f_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec_ref(v_a_2884_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(uint8_t v_pu_2892_, lean_object* v_f_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
switch(lean_obj_tag(v_a_2894_))
{
case 0:
{
lean_object* v_k_2900_; 
v_k_2900_ = lean_ctor_get(v_a_2894_, 1);
lean_inc_ref(v_k_2900_);
lean_dec_ref_known(v_a_2894_, 2);
v_a_2894_ = v_k_2900_;
goto _start;
}
case 1:
{
lean_object* v_decl_2902_; lean_object* v_k_2903_; lean_object* v_value_2904_; lean_object* v___x_2905_; 
v_decl_2902_ = lean_ctor_get(v_a_2894_, 0);
lean_inc_ref(v_decl_2902_);
v_k_2903_ = lean_ctor_get(v_a_2894_, 1);
lean_inc_ref(v_k_2903_);
lean_dec_ref_known(v_a_2894_, 2);
v_value_2904_ = lean_ctor_get(v_decl_2902_, 4);
lean_inc_ref(v_value_2904_);
lean_dec_ref(v_decl_2902_);
lean_inc_ref(v_f_2893_);
v___x_2905_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2892_, v_f_2893_, v_value_2904_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; uint8_t v___x_2907_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
v___x_2907_ = lean_unbox(v_a_2906_);
lean_dec(v_a_2906_);
if (v___x_2907_ == 0)
{
lean_dec_ref_known(v___x_2905_, 1);
v_a_2894_ = v_k_2903_;
goto _start;
}
else
{
lean_dec_ref(v_k_2903_);
lean_dec_ref(v_f_2893_);
return v___x_2905_;
}
}
else
{
lean_dec_ref(v_k_2903_);
lean_dec_ref(v_f_2893_);
return v___x_2905_;
}
}
case 2:
{
lean_object* v_decl_2909_; lean_object* v_k_2910_; lean_object* v_value_2911_; lean_object* v___x_2912_; 
v_decl_2909_ = lean_ctor_get(v_a_2894_, 0);
lean_inc_ref(v_decl_2909_);
v_k_2910_ = lean_ctor_get(v_a_2894_, 1);
lean_inc_ref(v_k_2910_);
lean_dec_ref_known(v_a_2894_, 2);
v_value_2911_ = lean_ctor_get(v_decl_2909_, 4);
lean_inc_ref(v_value_2911_);
lean_dec_ref(v_decl_2909_);
lean_inc_ref(v_f_2893_);
v___x_2912_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2892_, v_f_2893_, v_value_2911_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; uint8_t v___x_2914_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
v___x_2914_ = lean_unbox(v_a_2913_);
lean_dec(v_a_2913_);
if (v___x_2914_ == 0)
{
lean_dec_ref_known(v___x_2912_, 1);
v_a_2894_ = v_k_2910_;
goto _start;
}
else
{
lean_dec_ref(v_k_2910_);
lean_dec_ref(v_f_2893_);
return v___x_2912_;
}
}
else
{
lean_dec_ref(v_k_2910_);
lean_dec_ref(v_f_2893_);
return v___x_2912_;
}
}
case 4:
{
lean_object* v_cases_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2935_; 
v_cases_2916_ = lean_ctor_get(v_a_2894_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_a_2894_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2918_ = v_a_2894_;
v_isShared_2919_ = v_isSharedCheck_2935_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_cases_2916_);
lean_dec(v_a_2894_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2935_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v_alts_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v_alts_2920_ = lean_ctor_get(v_cases_2916_, 3);
lean_inc_ref(v_alts_2920_);
lean_dec_ref(v_cases_2916_);
v___x_2921_ = lean_unsigned_to_nat(0u);
v___x_2922_ = lean_array_get_size(v_alts_2920_);
v___x_2923_ = lean_nat_dec_lt(v___x_2921_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2926_; 
lean_dec_ref(v_alts_2920_);
lean_dec_ref(v_f_2893_);
v___x_2924_ = lean_box(v___x_2923_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set_tag(v___x_2918_, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2924_);
v___x_2926_ = v___x_2918_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
else
{
if (v___x_2923_ == 0)
{
lean_object* v___x_2928_; lean_object* v___x_2930_; 
lean_dec_ref(v_alts_2920_);
lean_dec_ref(v_f_2893_);
v___x_2928_ = lean_box(v___x_2923_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set_tag(v___x_2918_, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2928_);
v___x_2930_ = v___x_2918_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
else
{
size_t v___x_2932_; size_t v___x_2933_; lean_object* v___x_2934_; 
lean_del_object(v___x_2918_);
v___x_2932_ = ((size_t)0ULL);
v___x_2933_ = lean_usize_of_nat(v___x_2922_);
v___x_2934_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_2892_, v_f_2893_, v_alts_2920_, v___x_2932_, v___x_2933_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
lean_dec_ref(v_alts_2920_);
return v___x_2934_;
}
}
}
}
case 6:
{
lean_object* v_type_2936_; lean_object* v___x_2937_; 
v_type_2936_ = lean_ctor_get(v_a_2894_, 0);
lean_inc_ref(v_type_2936_);
lean_dec_ref_known(v_a_2894_, 1);
lean_inc(v_a_2898_);
lean_inc_ref(v_a_2897_);
lean_inc(v_a_2896_);
lean_inc_ref(v_a_2895_);
v___x_2937_ = lean_apply_6(v_f_2893_, v_type_2936_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, lean_box(0));
return v___x_2937_;
}
case 7:
{
lean_object* v_k_2938_; 
v_k_2938_ = lean_ctor_get(v_a_2894_, 3);
lean_inc_ref(v_k_2938_);
lean_dec_ref_known(v_a_2894_, 4);
v_a_2894_ = v_k_2938_;
goto _start;
}
case 8:
{
lean_object* v_k_2940_; 
v_k_2940_ = lean_ctor_get(v_a_2894_, 3);
lean_inc_ref(v_k_2940_);
lean_dec_ref_known(v_a_2894_, 4);
v_a_2894_ = v_k_2940_;
goto _start;
}
case 9:
{
lean_object* v_k_2942_; 
v_k_2942_ = lean_ctor_get(v_a_2894_, 5);
lean_inc_ref(v_k_2942_);
lean_dec_ref_known(v_a_2894_, 6);
v_a_2894_ = v_k_2942_;
goto _start;
}
case 10:
{
lean_object* v_k_2944_; 
v_k_2944_ = lean_ctor_get(v_a_2894_, 2);
lean_inc_ref(v_k_2944_);
lean_dec_ref_known(v_a_2894_, 3);
v_a_2894_ = v_k_2944_;
goto _start;
}
case 11:
{
lean_object* v_k_2946_; 
v_k_2946_ = lean_ctor_get(v_a_2894_, 2);
lean_inc_ref(v_k_2946_);
lean_dec_ref_known(v_a_2894_, 3);
v_a_2894_ = v_k_2946_;
goto _start;
}
case 12:
{
lean_object* v_k_2948_; 
v_k_2948_ = lean_ctor_get(v_a_2894_, 3);
lean_inc_ref(v_k_2948_);
lean_dec_ref_known(v_a_2894_, 4);
v_a_2894_ = v_k_2948_;
goto _start;
}
case 13:
{
lean_object* v_k_2950_; 
v_k_2950_ = lean_ctor_get(v_a_2894_, 1);
lean_inc_ref(v_k_2950_);
lean_dec_ref_known(v_a_2894_, 2);
v_a_2894_ = v_k_2950_;
goto _start;
}
default: 
{
uint8_t v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec_ref(v_a_2894_);
lean_dec_ref(v_f_2893_);
v___x_2952_ = 0;
v___x_2953_ = lean_box(v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(uint8_t v_pu_2955_, lean_object* v_f_2956_, lean_object* v_as_2957_, size_t v_i_2958_, size_t v_stop_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
uint8_t v___x_2965_; 
v___x_2965_ = lean_usize_dec_eq(v_i_2958_, v_stop_2959_);
if (v___x_2965_ == 0)
{
uint8_t v___x_2966_; lean_object* v___y_2968_; lean_object* v___x_2983_; 
v___x_2966_ = 1;
v___x_2983_ = lean_array_uget_borrowed(v_as_2957_, v_i_2958_);
switch(lean_obj_tag(v___x_2983_))
{
case 0:
{
lean_object* v_code_2984_; 
v_code_2984_ = lean_ctor_get(v___x_2983_, 2);
lean_inc_ref(v_code_2984_);
v___y_2968_ = v_code_2984_;
goto v___jp_2967_;
}
case 1:
{
lean_object* v_code_2985_; 
v_code_2985_ = lean_ctor_get(v___x_2983_, 1);
lean_inc_ref(v_code_2985_);
v___y_2968_ = v_code_2985_;
goto v___jp_2967_;
}
default: 
{
lean_object* v_code_2986_; 
v_code_2986_ = lean_ctor_get(v___x_2983_, 0);
lean_inc_ref(v_code_2986_);
v___y_2968_ = v_code_2986_;
goto v___jp_2967_;
}
}
v___jp_2967_:
{
lean_object* v___x_2969_; 
lean_inc_ref(v_f_2956_);
v___x_2969_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2955_, v_f_2956_, v___y_2968_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2982_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2972_ = v___x_2969_;
v_isShared_2973_ = v_isSharedCheck_2982_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2982_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
uint8_t v___x_2974_; 
v___x_2974_ = lean_unbox(v_a_2970_);
lean_dec(v_a_2970_);
if (v___x_2974_ == 0)
{
size_t v___x_2975_; size_t v___x_2976_; 
lean_del_object(v___x_2972_);
v___x_2975_ = ((size_t)1ULL);
v___x_2976_ = lean_usize_add(v_i_2958_, v___x_2975_);
v_i_2958_ = v___x_2976_;
goto _start;
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
lean_dec_ref(v_f_2956_);
v___x_2978_ = lean_box(v___x_2966_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v___x_2978_);
v___x_2980_ = v___x_2972_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_dec_ref(v_f_2956_);
return v___x_2969_;
}
}
}
else
{
uint8_t v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
lean_dec_ref(v_f_2956_);
v___x_2987_ = 0;
v___x_2988_ = lean_box(v___x_2987_);
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
return v___x_2989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0___boxed(lean_object* v_pu_2990_, lean_object* v_f_2991_, lean_object* v_as_2992_, lean_object* v_i_2993_, lean_object* v_stop_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
uint8_t v_pu_boxed_3000_; size_t v_i_boxed_3001_; size_t v_stop_boxed_3002_; lean_object* v_res_3003_; 
v_pu_boxed_3000_ = lean_unbox(v_pu_2990_);
v_i_boxed_3001_ = lean_unbox_usize(v_i_2993_);
lean_dec(v_i_2993_);
v_stop_boxed_3002_ = lean_unbox_usize(v_stop_2994_);
lean_dec(v_stop_2994_);
v_res_3003_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_boxed_3000_, v_f_2991_, v_as_2992_, v_i_boxed_3001_, v_stop_boxed_3002_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec_ref(v_as_2992_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed(lean_object* v_pu_3004_, lean_object* v_f_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
uint8_t v_pu_boxed_3012_; lean_object* v_res_3013_; 
v_pu_boxed_3012_ = lean_unbox(v_pu_3004_);
v_res_3013_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_boxed_3012_, v_f_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(uint8_t v_pu_3014_, lean_object* v_f_3015_, lean_object* v_as_3016_, size_t v_i_3017_, size_t v_stop_3018_, lean_object* v_b_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_usize_dec_eq(v_i_3017_, v_stop_3018_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v_value_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3026_ = lean_array_uget_borrowed(v_as_3016_, v_i_3017_);
v_value_3027_ = lean_ctor_get(v___x_3026_, 1);
v___x_3028_ = lean_box(v_pu_3014_);
lean_inc_ref(v_f_3015_);
v___x_3029_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed), 8, 2);
lean_closure_set(v___x_3029_, 0, v___x_3028_);
lean_closure_set(v___x_3029_, 1, v_f_3015_);
lean_inc_ref(v_value_3027_);
v___x_3030_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_3027_, v___x_3029_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v_a_3033_; uint8_t v___x_3037_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v___x_3037_ = lean_unbox(v_a_3031_);
lean_dec(v_a_3031_);
if (v___x_3037_ == 0)
{
v_a_3033_ = v_b_3019_;
goto v___jp_3032_;
}
else
{
lean_object* v___x_3038_; 
lean_inc(v___x_3026_);
v___x_3038_ = lean_array_push(v_b_3019_, v___x_3026_);
v_a_3033_ = v___x_3038_;
goto v___jp_3032_;
}
v___jp_3032_:
{
size_t v___x_3034_; size_t v___x_3035_; 
v___x_3034_ = ((size_t)1ULL);
v___x_3035_ = lean_usize_add(v_i_3017_, v___x_3034_);
v_i_3017_ = v___x_3035_;
v_b_3019_ = v_a_3033_;
goto _start;
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v_b_3019_);
lean_dec_ref(v_f_3015_);
v_a_3039_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3030_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3030_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
lean_object* v___x_3047_; 
lean_dec_ref(v_f_3015_);
v___x_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_b_3019_);
return v___x_3047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0___boxed(lean_object* v_pu_3048_, lean_object* v_f_3049_, lean_object* v_as_3050_, lean_object* v_i_3051_, lean_object* v_stop_3052_, lean_object* v_b_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
uint8_t v_pu_boxed_3059_; size_t v_i_boxed_3060_; size_t v_stop_boxed_3061_; lean_object* v_res_3062_; 
v_pu_boxed_3059_ = lean_unbox(v_pu_3048_);
v_i_boxed_3060_ = lean_unbox_usize(v_i_3051_);
lean_dec(v_i_3051_);
v_stop_boxed_3061_ = lean_unbox_usize(v_stop_3052_);
lean_dec(v_stop_3052_);
v_res_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_boxed_3059_, v_f_3049_, v_as_3050_, v_i_boxed_3060_, v_stop_boxed_3061_, v_b_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v_as_3050_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach(uint8_t v_pu_3063_, lean_object* v_f_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; 
v___x_3071_ = lean_unsigned_to_nat(0u);
v___x_3072_ = lean_array_get_size(v_a_3065_);
v___x_3073_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_3074_ = lean_nat_dec_lt(v___x_3071_, v___x_3072_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; 
lean_dec_ref(v_f_3064_);
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
return v___x_3075_;
}
else
{
uint8_t v___x_3076_; 
v___x_3076_ = lean_nat_dec_le(v___x_3072_, v___x_3072_);
if (v___x_3076_ == 0)
{
if (v___x_3074_ == 0)
{
lean_object* v___x_3077_; 
lean_dec_ref(v_f_3064_);
v___x_3077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3073_);
return v___x_3077_;
}
else
{
size_t v___x_3078_; size_t v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((size_t)0ULL);
v___x_3079_ = lean_usize_of_nat(v___x_3072_);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_3063_, v_f_3064_, v_a_3065_, v___x_3078_, v___x_3079_, v___x_3073_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
return v___x_3080_;
}
}
else
{
size_t v___x_3081_; size_t v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = ((size_t)0ULL);
v___x_3082_ = lean_usize_of_nat(v___x_3072_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_3063_, v_f_3064_, v_a_3065_, v___x_3081_, v___x_3082_, v___x_3073_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
return v___x_3083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach___boxed(lean_object* v_pu_3084_, lean_object* v_f_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
uint8_t v_pu_boxed_3092_; lean_object* v_res_3093_; 
v_pu_boxed_3092_ = lean_unbox(v_pu_3084_);
v_res_3093_ = l_Lean_Compiler_LCNF_Probe_filterByUnreach(v_pu_boxed_3092_, v_f_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec_ref(v_a_3086_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(lean_object* v_decl_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_toSignature_3100_; lean_object* v_name_3101_; lean_object* v___x_3102_; 
v_toSignature_3100_ = lean_ctor_get(v_decl_3094_, 0);
v_name_3101_ = lean_ctor_get(v_toSignature_3100_, 0);
lean_inc(v_name_3101_);
v___x_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3102_, 0, v_name_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed(lean_object* v_decl_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(v_decl_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v_decl_3103_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg(lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v___x_3117_; lean_object* v_toApplicative_3118_; lean_object* v_toFunctor_3119_; lean_object* v_toSeq_3120_; lean_object* v_toSeqLeft_3121_; lean_object* v_toSeqRight_3122_; lean_object* v___f_3123_; lean_object* v___f_3124_; lean_object* v___f_3125_; lean_object* v___f_3126_; lean_object* v___x_3127_; lean_object* v___f_3128_; lean_object* v___f_3129_; lean_object* v___f_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v_toApplicative_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3166_; 
v___x_3117_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3118_ = lean_ctor_get(v___x_3117_, 0);
v_toFunctor_3119_ = lean_ctor_get(v_toApplicative_3118_, 0);
v_toSeq_3120_ = lean_ctor_get(v_toApplicative_3118_, 2);
v_toSeqLeft_3121_ = lean_ctor_get(v_toApplicative_3118_, 3);
v_toSeqRight_3122_ = lean_ctor_get(v_toApplicative_3118_, 4);
v___f_3123_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3124_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3119_, 2);
v___f_3125_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3125_, 0, v_toFunctor_3119_);
v___f_3126_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3126_, 0, v_toFunctor_3119_);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___f_3125_);
lean_ctor_set(v___x_3127_, 1, v___f_3126_);
lean_inc(v_toSeqRight_3122_);
v___f_3128_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3128_, 0, v_toSeqRight_3122_);
lean_inc(v_toSeqLeft_3121_);
v___f_3129_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3129_, 0, v_toSeqLeft_3121_);
lean_inc(v_toSeq_3120_);
v___f_3130_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3130_, 0, v_toSeq_3120_);
v___x_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3127_);
lean_ctor_set(v___x_3131_, 1, v___f_3123_);
lean_ctor_set(v___x_3131_, 2, v___f_3130_);
lean_ctor_set(v___x_3131_, 3, v___f_3129_);
lean_ctor_set(v___x_3131_, 4, v___f_3128_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
lean_ctor_set(v___x_3132_, 1, v___f_3124_);
v___x_3133_ = l_StateRefT_x27_instMonad___redArg(v___x_3132_);
v_toApplicative_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; 
v_unused_3167_ = lean_ctor_get(v___x_3133_, 1);
lean_dec(v_unused_3167_);
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3166_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_toApplicative_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3166_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v_toFunctor_3138_; lean_object* v_toSeq_3139_; lean_object* v_toSeqLeft_3140_; lean_object* v_toSeqRight_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3164_; 
v_toFunctor_3138_ = lean_ctor_get(v_toApplicative_3134_, 0);
v_toSeq_3139_ = lean_ctor_get(v_toApplicative_3134_, 2);
v_toSeqLeft_3140_ = lean_ctor_get(v_toApplicative_3134_, 3);
v_toSeqRight_3141_ = lean_ctor_get(v_toApplicative_3134_, 4);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_toApplicative_3134_);
if (v_isSharedCheck_3164_ == 0)
{
lean_object* v_unused_3165_; 
v_unused_3165_ = lean_ctor_get(v_toApplicative_3134_, 1);
lean_dec(v_unused_3165_);
v___x_3143_ = v_toApplicative_3134_;
v_isShared_3144_ = v_isSharedCheck_3164_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_toSeqRight_3141_);
lean_inc(v_toSeqLeft_3140_);
lean_inc(v_toSeq_3139_);
lean_inc(v_toFunctor_3138_);
lean_dec(v_toApplicative_3134_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3164_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___f_3145_; lean_object* v___f_3146_; lean_object* v___f_3147_; lean_object* v___f_3148_; lean_object* v___f_3149_; lean_object* v___x_3150_; lean_object* v___f_3151_; lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___x_3155_; 
v___f_3145_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3146_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3147_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3138_);
v___f_3148_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3148_, 0, v_toFunctor_3138_);
v___f_3149_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3149_, 0, v_toFunctor_3138_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___f_3148_);
lean_ctor_set(v___x_3150_, 1, v___f_3149_);
v___f_3151_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3151_, 0, v_toSeqRight_3141_);
v___f_3152_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3152_, 0, v_toSeqLeft_3140_);
v___f_3153_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3153_, 0, v_toSeq_3139_);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 4, v___f_3151_);
lean_ctor_set(v___x_3143_, 3, v___f_3152_);
lean_ctor_set(v___x_3143_, 2, v___f_3153_);
lean_ctor_set(v___x_3143_, 1, v___f_3146_);
lean_ctor_set(v___x_3143_, 0, v___x_3150_);
v___x_3155_ = v___x_3143_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v___f_3146_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v___f_3153_);
lean_ctor_set(v_reuseFailAlloc_3163_, 3, v___f_3152_);
lean_ctor_set(v_reuseFailAlloc_3163_, 4, v___f_3151_);
v___x_3155_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3157_; 
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 1, v___f_3147_);
lean_ctor_set(v___x_3136_, 0, v___x_3155_);
v___x_3157_ = v___x_3136_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v___f_3147_);
v___x_3157_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
size_t v_sz_3158_; size_t v___x_3159_; lean_object* v___x_127__overap_3160_; lean_object* v___x_3161_; 
v_sz_3158_ = lean_array_size(v_a_3111_);
v___x_3159_ = ((size_t)0ULL);
v___x_127__overap_3160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3157_, v___f_3145_, v_sz_3158_, v___x_3159_, v_a_3111_);
lean_inc(v_a_3115_);
lean_inc_ref(v_a_3114_);
lean_inc(v_a_3113_);
lean_inc_ref(v_a_3112_);
v___x_3161_ = lean_apply_5(v___x_127__overap_3160_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, lean_box(0));
return v___x_3161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___boxed(lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg(v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
lean_dec(v_a_3172_);
lean_dec_ref(v_a_3171_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames(uint8_t v_pu_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v___x_3182_; lean_object* v_toApplicative_3183_; lean_object* v_toFunctor_3184_; lean_object* v_toSeq_3185_; lean_object* v_toSeqLeft_3186_; lean_object* v_toSeqRight_3187_; lean_object* v___f_3188_; lean_object* v___f_3189_; lean_object* v___f_3190_; lean_object* v___f_3191_; lean_object* v___x_3192_; lean_object* v___f_3193_; lean_object* v___f_3194_; lean_object* v___f_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_toApplicative_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3231_; 
v___x_3182_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3183_ = lean_ctor_get(v___x_3182_, 0);
v_toFunctor_3184_ = lean_ctor_get(v_toApplicative_3183_, 0);
v_toSeq_3185_ = lean_ctor_get(v_toApplicative_3183_, 2);
v_toSeqLeft_3186_ = lean_ctor_get(v_toApplicative_3183_, 3);
v_toSeqRight_3187_ = lean_ctor_get(v_toApplicative_3183_, 4);
v___f_3188_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3189_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3184_, 2);
v___f_3190_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3190_, 0, v_toFunctor_3184_);
v___f_3191_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3191_, 0, v_toFunctor_3184_);
v___x_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___f_3190_);
lean_ctor_set(v___x_3192_, 1, v___f_3191_);
lean_inc(v_toSeqRight_3187_);
v___f_3193_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3193_, 0, v_toSeqRight_3187_);
lean_inc(v_toSeqLeft_3186_);
v___f_3194_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3194_, 0, v_toSeqLeft_3186_);
lean_inc(v_toSeq_3185_);
v___f_3195_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3195_, 0, v_toSeq_3185_);
v___x_3196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3192_);
lean_ctor_set(v___x_3196_, 1, v___f_3188_);
lean_ctor_set(v___x_3196_, 2, v___f_3195_);
lean_ctor_set(v___x_3196_, 3, v___f_3194_);
lean_ctor_set(v___x_3196_, 4, v___f_3193_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
lean_ctor_set(v___x_3197_, 1, v___f_3189_);
v___x_3198_ = l_StateRefT_x27_instMonad___redArg(v___x_3197_);
v_toApplicative_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v___x_3198_, 1);
lean_dec(v_unused_3232_);
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3231_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_toApplicative_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3231_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v_toFunctor_3203_; lean_object* v_toSeq_3204_; lean_object* v_toSeqLeft_3205_; lean_object* v_toSeqRight_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3229_; 
v_toFunctor_3203_ = lean_ctor_get(v_toApplicative_3199_, 0);
v_toSeq_3204_ = lean_ctor_get(v_toApplicative_3199_, 2);
v_toSeqLeft_3205_ = lean_ctor_get(v_toApplicative_3199_, 3);
v_toSeqRight_3206_ = lean_ctor_get(v_toApplicative_3199_, 4);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_toApplicative_3199_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v_toApplicative_3199_, 1);
lean_dec(v_unused_3230_);
v___x_3208_ = v_toApplicative_3199_;
v_isShared_3209_ = v_isSharedCheck_3229_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_toSeqRight_3206_);
lean_inc(v_toSeqLeft_3205_);
lean_inc(v_toSeq_3204_);
lean_inc(v_toFunctor_3203_);
lean_dec(v_toApplicative_3199_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3229_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___f_3210_; lean_object* v___f_3211_; lean_object* v___f_3212_; lean_object* v___f_3213_; lean_object* v___f_3214_; lean_object* v___x_3215_; lean_object* v___f_3216_; lean_object* v___f_3217_; lean_object* v___f_3218_; lean_object* v___x_3220_; 
v___f_3210_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3211_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3212_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3203_);
v___f_3213_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3213_, 0, v_toFunctor_3203_);
v___f_3214_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3214_, 0, v_toFunctor_3203_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___f_3213_);
lean_ctor_set(v___x_3215_, 1, v___f_3214_);
v___f_3216_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3216_, 0, v_toSeqRight_3206_);
v___f_3217_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3217_, 0, v_toSeqLeft_3205_);
v___f_3218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3218_, 0, v_toSeq_3204_);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 4, v___f_3216_);
lean_ctor_set(v___x_3208_, 3, v___f_3217_);
lean_ctor_set(v___x_3208_, 2, v___f_3218_);
lean_ctor_set(v___x_3208_, 1, v___f_3211_);
lean_ctor_set(v___x_3208_, 0, v___x_3215_);
v___x_3220_ = v___x_3208_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3215_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v___f_3211_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v___f_3218_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v___f_3217_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v___f_3216_);
v___x_3220_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3222_; 
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 1, v___f_3212_);
lean_ctor_set(v___x_3201_, 0, v___x_3220_);
v___x_3222_ = v___x_3201_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v___f_3212_);
v___x_3222_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
size_t v_sz_3223_; size_t v___x_3224_; lean_object* v___x_185__overap_3225_; lean_object* v___x_3226_; 
v_sz_3223_ = lean_array_size(v_a_3176_);
v___x_3224_ = ((size_t)0ULL);
v___x_185__overap_3225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3222_, v___f_3210_, v_sz_3223_, v___x_3224_, v_a_3176_);
lean_inc(v_a_3180_);
lean_inc_ref(v_a_3179_);
lean_inc(v_a_3178_);
lean_inc_ref(v_a_3177_);
v___x_3226_ = lean_apply_5(v___x_185__overap_3225_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, lean_box(0));
return v___x_3226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___boxed(lean_object* v_pu_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
uint8_t v_pu_boxed_3240_; lean_object* v_res_3241_; 
v_pu_boxed_3240_ = lean_unbox(v_pu_3233_);
v_res_3241_ = l_Lean_Compiler_LCNF_Probe_declNames(v_pu_boxed_3240_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_a_3236_);
lean_dec_ref(v_a_3235_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(lean_object* v_inst_3242_, lean_object* v_x_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = lean_apply_1(v_inst_3242_, v_x_3243_);
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed(lean_object* v_inst_3251_, lean_object* v_x_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(v_inst_3251_, v_x_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg(lean_object* v_inst_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_){
_start:
{
lean_object* v___x_3266_; lean_object* v_toApplicative_3267_; lean_object* v_toFunctor_3268_; lean_object* v_toSeq_3269_; lean_object* v_toSeqLeft_3270_; lean_object* v_toSeqRight_3271_; lean_object* v___f_3272_; lean_object* v___f_3273_; lean_object* v___f_3274_; lean_object* v___f_3275_; lean_object* v___x_3276_; lean_object* v___f_3277_; lean_object* v___f_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v_toApplicative_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3315_; 
v___x_3266_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3267_ = lean_ctor_get(v___x_3266_, 0);
v_toFunctor_3268_ = lean_ctor_get(v_toApplicative_3267_, 0);
v_toSeq_3269_ = lean_ctor_get(v_toApplicative_3267_, 2);
v_toSeqLeft_3270_ = lean_ctor_get(v_toApplicative_3267_, 3);
v_toSeqRight_3271_ = lean_ctor_get(v_toApplicative_3267_, 4);
v___f_3272_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3273_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3268_, 2);
v___f_3274_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3274_, 0, v_toFunctor_3268_);
v___f_3275_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3275_, 0, v_toFunctor_3268_);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___f_3274_);
lean_ctor_set(v___x_3276_, 1, v___f_3275_);
lean_inc(v_toSeqRight_3271_);
v___f_3277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3277_, 0, v_toSeqRight_3271_);
lean_inc(v_toSeqLeft_3270_);
v___f_3278_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3278_, 0, v_toSeqLeft_3270_);
lean_inc(v_toSeq_3269_);
v___f_3279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3279_, 0, v_toSeq_3269_);
v___x_3280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3276_);
lean_ctor_set(v___x_3280_, 1, v___f_3272_);
lean_ctor_set(v___x_3280_, 2, v___f_3279_);
lean_ctor_set(v___x_3280_, 3, v___f_3278_);
lean_ctor_set(v___x_3280_, 4, v___f_3277_);
v___x_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set(v___x_3281_, 1, v___f_3273_);
v___x_3282_ = l_StateRefT_x27_instMonad___redArg(v___x_3281_);
v_toApplicative_3283_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; 
v_unused_3316_ = lean_ctor_get(v___x_3282_, 1);
lean_dec(v_unused_3316_);
v___x_3285_ = v___x_3282_;
v_isShared_3286_ = v_isSharedCheck_3315_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_toApplicative_3283_);
lean_dec(v___x_3282_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3315_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v_toFunctor_3287_; lean_object* v_toSeq_3288_; lean_object* v_toSeqLeft_3289_; lean_object* v_toSeqRight_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3313_; 
v_toFunctor_3287_ = lean_ctor_get(v_toApplicative_3283_, 0);
v_toSeq_3288_ = lean_ctor_get(v_toApplicative_3283_, 2);
v_toSeqLeft_3289_ = lean_ctor_get(v_toApplicative_3283_, 3);
v_toSeqRight_3290_ = lean_ctor_get(v_toApplicative_3283_, 4);
v_isSharedCheck_3313_ = !lean_is_exclusive(v_toApplicative_3283_);
if (v_isSharedCheck_3313_ == 0)
{
lean_object* v_unused_3314_; 
v_unused_3314_ = lean_ctor_get(v_toApplicative_3283_, 1);
lean_dec(v_unused_3314_);
v___x_3292_ = v_toApplicative_3283_;
v_isShared_3293_ = v_isSharedCheck_3313_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_toSeqRight_3290_);
lean_inc(v_toSeqLeft_3289_);
lean_inc(v_toSeq_3288_);
lean_inc(v_toFunctor_3287_);
lean_dec(v_toApplicative_3283_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3313_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___f_3294_; lean_object* v___f_3295_; lean_object* v___f_3296_; lean_object* v___f_3297_; lean_object* v___f_3298_; lean_object* v___x_3299_; lean_object* v___f_3300_; lean_object* v___f_3301_; lean_object* v___f_3302_; lean_object* v___x_3304_; 
v___f_3294_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3294_, 0, v_inst_3259_);
v___f_3295_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3296_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3287_);
v___f_3297_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3297_, 0, v_toFunctor_3287_);
v___f_3298_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3298_, 0, v_toFunctor_3287_);
v___x_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___f_3297_);
lean_ctor_set(v___x_3299_, 1, v___f_3298_);
v___f_3300_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3300_, 0, v_toSeqRight_3290_);
v___f_3301_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3301_, 0, v_toSeqLeft_3289_);
v___f_3302_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3302_, 0, v_toSeq_3288_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 4, v___f_3300_);
lean_ctor_set(v___x_3292_, 3, v___f_3301_);
lean_ctor_set(v___x_3292_, 2, v___f_3302_);
lean_ctor_set(v___x_3292_, 1, v___f_3295_);
lean_ctor_set(v___x_3292_, 0, v___x_3299_);
v___x_3304_ = v___x_3292_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v___f_3295_);
lean_ctor_set(v_reuseFailAlloc_3312_, 2, v___f_3302_);
lean_ctor_set(v_reuseFailAlloc_3312_, 3, v___f_3301_);
lean_ctor_set(v_reuseFailAlloc_3312_, 4, v___f_3300_);
v___x_3304_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
lean_object* v___x_3306_; 
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 1, v___f_3296_);
lean_ctor_set(v___x_3285_, 0, v___x_3304_);
v___x_3306_ = v___x_3285_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3304_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v___f_3296_);
v___x_3306_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
size_t v_sz_3307_; size_t v___x_3308_; lean_object* v___x_129__overap_3309_; lean_object* v___x_3310_; 
v_sz_3307_ = lean_array_size(v_a_3260_);
v___x_3308_ = ((size_t)0ULL);
v___x_129__overap_3309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3306_, v___f_3294_, v_sz_3307_, v___x_3308_, v_a_3260_);
lean_inc(v_a_3264_);
lean_inc_ref(v_a_3263_);
lean_inc(v_a_3262_);
lean_inc_ref(v_a_3261_);
v___x_3310_ = lean_apply_5(v___x_129__overap_3309_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, lean_box(0));
return v___x_3310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___boxed(lean_object* v_inst_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_Compiler_LCNF_Probe_toString___redArg(v_inst_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString(lean_object* v_00_u03b1_3325_, lean_object* v_inst_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_){
_start:
{
lean_object* v___x_3333_; lean_object* v_toApplicative_3334_; lean_object* v_toFunctor_3335_; lean_object* v_toSeq_3336_; lean_object* v_toSeqLeft_3337_; lean_object* v_toSeqRight_3338_; lean_object* v___f_3339_; lean_object* v___f_3340_; lean_object* v___f_3341_; lean_object* v___f_3342_; lean_object* v___x_3343_; lean_object* v___f_3344_; lean_object* v___f_3345_; lean_object* v___f_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v_toApplicative_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3382_; 
v___x_3333_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3334_ = lean_ctor_get(v___x_3333_, 0);
v_toFunctor_3335_ = lean_ctor_get(v_toApplicative_3334_, 0);
v_toSeq_3336_ = lean_ctor_get(v_toApplicative_3334_, 2);
v_toSeqLeft_3337_ = lean_ctor_get(v_toApplicative_3334_, 3);
v_toSeqRight_3338_ = lean_ctor_get(v_toApplicative_3334_, 4);
v___f_3339_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3340_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3335_, 2);
v___f_3341_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3341_, 0, v_toFunctor_3335_);
v___f_3342_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3342_, 0, v_toFunctor_3335_);
v___x_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___f_3341_);
lean_ctor_set(v___x_3343_, 1, v___f_3342_);
lean_inc(v_toSeqRight_3338_);
v___f_3344_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3344_, 0, v_toSeqRight_3338_);
lean_inc(v_toSeqLeft_3337_);
v___f_3345_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3345_, 0, v_toSeqLeft_3337_);
lean_inc(v_toSeq_3336_);
v___f_3346_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3346_, 0, v_toSeq_3336_);
v___x_3347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3343_);
lean_ctor_set(v___x_3347_, 1, v___f_3339_);
lean_ctor_set(v___x_3347_, 2, v___f_3346_);
lean_ctor_set(v___x_3347_, 3, v___f_3345_);
lean_ctor_set(v___x_3347_, 4, v___f_3344_);
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
lean_ctor_set(v___x_3348_, 1, v___f_3340_);
v___x_3349_ = l_StateRefT_x27_instMonad___redArg(v___x_3348_);
v_toApplicative_3350_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3382_ == 0)
{
lean_object* v_unused_3383_; 
v_unused_3383_ = lean_ctor_get(v___x_3349_, 1);
lean_dec(v_unused_3383_);
v___x_3352_ = v___x_3349_;
v_isShared_3353_ = v_isSharedCheck_3382_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_toApplicative_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3382_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v_toFunctor_3354_; lean_object* v_toSeq_3355_; lean_object* v_toSeqLeft_3356_; lean_object* v_toSeqRight_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3380_; 
v_toFunctor_3354_ = lean_ctor_get(v_toApplicative_3350_, 0);
v_toSeq_3355_ = lean_ctor_get(v_toApplicative_3350_, 2);
v_toSeqLeft_3356_ = lean_ctor_get(v_toApplicative_3350_, 3);
v_toSeqRight_3357_ = lean_ctor_get(v_toApplicative_3350_, 4);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_toApplicative_3350_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v_toApplicative_3350_, 1);
lean_dec(v_unused_3381_);
v___x_3359_ = v_toApplicative_3350_;
v_isShared_3360_ = v_isSharedCheck_3380_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_toSeqRight_3357_);
lean_inc(v_toSeqLeft_3356_);
lean_inc(v_toSeq_3355_);
lean_inc(v_toFunctor_3354_);
lean_dec(v_toApplicative_3350_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3380_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___f_3361_; lean_object* v___f_3362_; lean_object* v___f_3363_; lean_object* v___f_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; lean_object* v___f_3367_; lean_object* v___f_3368_; lean_object* v___f_3369_; lean_object* v___x_3371_; 
v___f_3361_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3361_, 0, v_inst_3326_);
v___f_3362_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3363_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3354_);
v___f_3364_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3364_, 0, v_toFunctor_3354_);
v___f_3365_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3365_, 0, v_toFunctor_3354_);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___f_3364_);
lean_ctor_set(v___x_3366_, 1, v___f_3365_);
v___f_3367_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3367_, 0, v_toSeqRight_3357_);
v___f_3368_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3368_, 0, v_toSeqLeft_3356_);
v___f_3369_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3369_, 0, v_toSeq_3355_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 4, v___f_3367_);
lean_ctor_set(v___x_3359_, 3, v___f_3368_);
lean_ctor_set(v___x_3359_, 2, v___f_3369_);
lean_ctor_set(v___x_3359_, 1, v___f_3362_);
lean_ctor_set(v___x_3359_, 0, v___x_3366_);
v___x_3371_ = v___x_3359_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v___f_3362_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v___f_3369_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v___f_3368_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v___f_3367_);
v___x_3371_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3373_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 1, v___f_3363_);
lean_ctor_set(v___x_3352_, 0, v___x_3371_);
v___x_3373_ = v___x_3352_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3371_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v___f_3363_);
v___x_3373_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
size_t v_sz_3374_; size_t v___x_3375_; lean_object* v___x_190__overap_3376_; lean_object* v___x_3377_; 
v_sz_3374_ = lean_array_size(v_a_3327_);
v___x_3375_ = ((size_t)0ULL);
v___x_190__overap_3376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3373_, v___f_3361_, v_sz_3374_, v___x_3375_, v_a_3327_);
lean_inc(v_a_3331_);
lean_inc_ref(v_a_3330_);
lean_inc(v_a_3329_);
lean_inc_ref(v_a_3328_);
v___x_3377_ = lean_apply_5(v___x_190__overap_3376_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, lean_box(0));
return v___x_3377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___boxed(lean_object* v_00_u03b1_3384_, lean_object* v_inst_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Compiler_LCNF_Probe_toString(v_00_u03b1_3384_, v_inst_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg(lean_object* v_data_3393_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3395_ = lean_array_get_size(v_data_3393_);
v___x_3396_ = lean_unsigned_to_nat(1u);
v___x_3397_ = lean_mk_empty_array_with_capacity(v___x_3396_);
v___x_3398_ = lean_array_push(v___x_3397_, v___x_3395_);
v___x_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg___boxed(lean_object* v_data_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_Compiler_LCNF_Probe_count___redArg(v_data_3400_);
lean_dec_ref(v_data_3400_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count(lean_object* v_00_u03b1_3403_, lean_object* v_data_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3410_ = lean_array_get_size(v_data_3404_);
v___x_3411_ = lean_unsigned_to_nat(1u);
v___x_3412_ = lean_mk_empty_array_with_capacity(v___x_3411_);
v___x_3413_ = lean_array_push(v___x_3412_, v___x_3410_);
v___x_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___boxed(lean_object* v_00_u03b1_3415_, lean_object* v_data_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Compiler_LCNF_Probe_count(v_00_u03b1_3415_, v_data_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec_ref(v_data_3416_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg(lean_object* v_data_3424_){
_start:
{
lean_object* v___y_3427_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = lean_array_get_size(v_data_3424_);
v___x_3434_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3435_ = lean_nat_dec_lt(v___x_3432_, v___x_3433_);
if (v___x_3435_ == 0)
{
lean_dec_ref(v_data_3424_);
v___y_3427_ = v___x_3432_;
goto v___jp_3426_;
}
else
{
lean_object* v___f_3436_; uint8_t v___x_3437_; 
v___f_3436_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3437_ = lean_nat_dec_le(v___x_3433_, v___x_3433_);
if (v___x_3437_ == 0)
{
if (v___x_3435_ == 0)
{
lean_dec_ref(v_data_3424_);
v___y_3427_ = v___x_3432_;
goto v___jp_3426_;
}
else
{
size_t v___x_3438_; size_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = ((size_t)0ULL);
v___x_3439_ = lean_usize_of_nat(v___x_3433_);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3434_, v___f_3436_, v_data_3424_, v___x_3438_, v___x_3439_, v___x_3432_);
v___y_3427_ = v___x_3440_;
goto v___jp_3426_;
}
}
else
{
size_t v___x_3441_; size_t v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = ((size_t)0ULL);
v___x_3442_ = lean_usize_of_nat(v___x_3433_);
v___x_3443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3434_, v___f_3436_, v_data_3424_, v___x_3441_, v___x_3442_, v___x_3432_);
v___y_3427_ = v___x_3443_;
goto v___jp_3426_;
}
}
v___jp_3426_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3428_ = lean_unsigned_to_nat(1u);
v___x_3429_ = lean_mk_empty_array_with_capacity(v___x_3428_);
v___x_3430_ = lean_array_push(v___x_3429_, v___y_3427_);
v___x_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg___boxed(lean_object* v_data_3444_, lean_object* v_a_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_Compiler_LCNF_Probe_sum___redArg(v_data_3444_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum(lean_object* v_data_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_){
_start:
{
lean_object* v___y_3454_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v___x_3459_ = lean_unsigned_to_nat(0u);
v___x_3460_ = lean_array_get_size(v_data_3447_);
v___x_3461_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3462_ = lean_nat_dec_lt(v___x_3459_, v___x_3460_);
if (v___x_3462_ == 0)
{
lean_dec_ref(v_data_3447_);
v___y_3454_ = v___x_3459_;
goto v___jp_3453_;
}
else
{
lean_object* v___f_3463_; uint8_t v___x_3464_; 
v___f_3463_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3464_ = lean_nat_dec_le(v___x_3460_, v___x_3460_);
if (v___x_3464_ == 0)
{
if (v___x_3462_ == 0)
{
lean_dec_ref(v_data_3447_);
v___y_3454_ = v___x_3459_;
goto v___jp_3453_;
}
else
{
size_t v___x_3465_; size_t v___x_3466_; lean_object* v___x_3467_; 
v___x_3465_ = ((size_t)0ULL);
v___x_3466_ = lean_usize_of_nat(v___x_3460_);
v___x_3467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3461_, v___f_3463_, v_data_3447_, v___x_3465_, v___x_3466_, v___x_3459_);
v___y_3454_ = v___x_3467_;
goto v___jp_3453_;
}
}
else
{
size_t v___x_3468_; size_t v___x_3469_; lean_object* v___x_3470_; 
v___x_3468_ = ((size_t)0ULL);
v___x_3469_ = lean_usize_of_nat(v___x_3460_);
v___x_3470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3461_, v___f_3463_, v_data_3447_, v___x_3468_, v___x_3469_, v___x_3459_);
v___y_3454_ = v___x_3470_;
goto v___jp_3453_;
}
}
v___jp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3455_ = lean_unsigned_to_nat(1u);
v___x_3456_ = lean_mk_empty_array_with_capacity(v___x_3455_);
v___x_3457_ = lean_array_push(v___x_3456_, v___y_3454_);
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
return v___x_3458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___boxed(lean_object* v_data_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_Compiler_LCNF_Probe_sum(v_data_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg(lean_object* v_n_3478_, lean_object* v_data_3479_){
_start:
{
lean_object* v_lower_3482_; lean_object* v_upper_3483_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v___x_3487_ = lean_array_get_size(v_data_3479_);
v___x_3488_ = lean_nat_sub(v___x_3487_, v_n_3478_);
v___x_3489_ = lean_unsigned_to_nat(0u);
v___x_3490_ = lean_nat_dec_le(v___x_3488_, v___x_3489_);
if (v___x_3490_ == 0)
{
v_lower_3482_ = v___x_3488_;
v_upper_3483_ = v___x_3487_;
goto v___jp_3481_;
}
else
{
lean_dec(v___x_3488_);
v_lower_3482_ = v___x_3489_;
v_upper_3483_ = v___x_3487_;
goto v___jp_3481_;
}
v___jp_3481_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3484_ = l_Array_toSubarray___redArg(v_data_3479_, v_lower_3482_, v_upper_3483_);
v___x_3485_ = l_Subarray_copy___redArg(v___x_3484_);
v___x_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
return v___x_3486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg___boxed(lean_object* v_n_3491_, lean_object* v_data_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_Compiler_LCNF_Probe_tail___redArg(v_n_3491_, v_data_3492_);
lean_dec(v_n_3491_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail(lean_object* v_00_u03b1_3495_, lean_object* v_n_3496_, lean_object* v_data_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_){
_start:
{
lean_object* v_lower_3504_; lean_object* v_upper_3505_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3509_ = lean_array_get_size(v_data_3497_);
v___x_3510_ = lean_nat_sub(v___x_3509_, v_n_3496_);
v___x_3511_ = lean_unsigned_to_nat(0u);
v___x_3512_ = lean_nat_dec_le(v___x_3510_, v___x_3511_);
if (v___x_3512_ == 0)
{
v_lower_3504_ = v___x_3510_;
v_upper_3505_ = v___x_3509_;
goto v___jp_3503_;
}
else
{
lean_dec(v___x_3510_);
v_lower_3504_ = v___x_3511_;
v_upper_3505_ = v___x_3509_;
goto v___jp_3503_;
}
v___jp_3503_:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = l_Array_toSubarray___redArg(v_data_3497_, v_lower_3504_, v_upper_3505_);
v___x_3507_ = l_Subarray_copy___redArg(v___x_3506_);
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
return v___x_3508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___boxed(lean_object* v_00_u03b1_3513_, lean_object* v_n_3514_, lean_object* v_data_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_Lean_Compiler_LCNF_Probe_tail(v_00_u03b1_3513_, v_n_3514_, v_data_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_n_3514_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg(lean_object* v_n_3522_, lean_object* v_data_3523_){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3525_ = lean_unsigned_to_nat(0u);
v___x_3526_ = l_Array_toSubarray___redArg(v_data_3523_, v___x_3525_, v_n_3522_);
v___x_3527_ = l_Subarray_copy___redArg(v___x_3526_);
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg___boxed(lean_object* v_n_3529_, lean_object* v_data_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_Compiler_LCNF_Probe_head___redArg(v_n_3529_, v_data_3530_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head(lean_object* v_00_u03b1_3533_, lean_object* v_n_3534_, lean_object* v_data_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3541_ = lean_unsigned_to_nat(0u);
v___x_3542_ = l_Array_toSubarray___redArg(v_data_3535_, v___x_3541_, v_n_3534_);
v___x_3543_ = l_Subarray_copy___redArg(v___x_3542_);
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___boxed(lean_object* v_00_u03b1_3545_, lean_object* v_n_3546_, lean_object* v_data_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_Compiler_LCNF_Probe_head(v_00_u03b1_3545_, v_n_3546_, v_data_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(lean_object* v_probe_3562_, lean_object* v___x_3563_, lean_object* v___x_3564_, lean_object* v___f_3565_, lean_object* v_inst_3566_, lean_object* v___x_3567_, lean_object* v___x_3568_, lean_object* v_decls_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v___x_3575_; 
lean_inc(v___y_3573_);
lean_inc_ref(v___y_3572_);
lean_inc(v___y_3571_);
lean_inc_ref(v___y_3570_);
lean_inc_ref(v_decls_3569_);
v___x_3575_ = lean_apply_6(v_probe_3562_, v_decls_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, lean_box(0));
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_options_3576_; uint8_t v_hasTrace_3577_; 
v_options_3576_ = lean_ctor_get(v___y_3572_, 2);
v_hasTrace_3577_ = lean_ctor_get_uint8(v_options_3576_, sizeof(void*)*1);
if (v_hasTrace_3577_ == 0)
{
lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref(v___x_3568_);
lean_dec_ref(v___x_3567_);
lean_dec_ref(v_inst_3566_);
lean_dec(v___f_3565_);
lean_dec(v___x_3564_);
lean_dec_ref(v___x_3563_);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3584_ == 0)
{
lean_object* v_unused_3585_; 
v_unused_3585_ = lean_ctor_get(v___x_3575_, 0);
lean_dec(v_unused_3585_);
v___x_3579_ = v___x_3575_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_dec(v___x_3575_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 0, v_decls_3569_);
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_decls_3569_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3630_; 
v_a_3586_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3588_ = v___x_3575_;
v_isShared_3589_ = v_isSharedCheck_3630_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3575_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3630_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v_inheritedTraceOptions_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v_inheritedTraceOptions_3590_ = lean_ctor_get(v___y_3572_, 13);
v___x_3591_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0));
v___x_3592_ = l_Lean_Name_mkStr2(v___x_3591_, v___x_3563_);
v___x_3593_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2));
lean_inc(v___x_3592_);
v___x_3594_ = l_Lean_Name_append(v___x_3593_, v___x_3592_);
v___x_3595_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3590_, v_options_3576_, v___x_3594_);
lean_dec(v___x_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3597_; 
lean_dec(v___x_3592_);
lean_dec(v_a_3586_);
lean_dec_ref(v___x_3568_);
lean_dec_ref(v___x_3567_);
lean_dec_ref(v_inst_3566_);
lean_dec(v___f_3565_);
lean_dec(v___x_3564_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v_decls_3569_);
v___x_3597_ = v___x_3588_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_decls_3569_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
else
{
lean_object* v___f_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v_toMonadRef_3604_; lean_object* v___f_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_1077__overap_3612_; lean_object* v___x_3613_; 
lean_del_object(v___x_3588_);
v___f_3599_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3));
v___x_3600_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4));
v___x_3601_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_3602_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3600_, v___x_3564_, v___x_3601_);
v___x_3603_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3599_, v___f_3565_, v___x_3602_);
v_toMonadRef_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc_ref(v_toMonadRef_3604_);
lean_dec_ref(v___x_3603_);
v___f_3605_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__5));
v___x_3606_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__6));
v___x_3607_ = lean_array_to_list(v_a_3586_);
v___x_3608_ = l_List_toString___redArg(v_inst_3566_, v___x_3607_);
v___x_3609_ = lean_string_append(v___x_3606_, v___x_3608_);
lean_dec_ref(v___x_3608_);
v___x_3610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
v___x_3611_ = l_Lean_MessageData_ofFormat(v___x_3610_);
v___x_1077__overap_3612_ = l_Lean_addTrace___redArg(v___x_3567_, v___x_3568_, v_toMonadRef_3604_, v___f_3605_, v___x_3592_, v___x_3611_);
lean_inc(v___y_3573_);
lean_inc_ref(v___y_3572_);
lean_inc(v___y_3571_);
lean_inc_ref(v___y_3570_);
v___x_3613_ = lean_apply_5(v___x_1077__overap_3612_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, lean_box(0));
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3620_; 
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v___x_3613_, 0);
lean_dec(v_unused_3621_);
v___x_3615_ = v___x_3613_;
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
else
{
lean_dec(v___x_3613_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3620_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v_decls_3569_);
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_decls_3569_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec_ref(v_decls_3569_);
v_a_3622_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3613_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3613_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec_ref(v_decls_3569_);
lean_dec_ref(v___x_3568_);
lean_dec_ref(v___x_3567_);
lean_dec_ref(v_inst_3566_);
lean_dec(v___f_3565_);
lean_dec(v___x_3564_);
lean_dec_ref(v___x_3563_);
v_a_3631_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3575_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3575_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed(lean_object* v_probe_3639_, lean_object* v___x_3640_, lean_object* v___x_3641_, lean_object* v___f_3642_, lean_object* v_inst_3643_, lean_object* v___x_3644_, lean_object* v___x_3645_, lean_object* v_decls_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(v_probe_3639_, v___x_3640_, v___x_3641_, v___f_3642_, v_inst_3643_, v___x_3644_, v___x_3645_, v_decls_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
return v_res_3652_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = l_Lean_Core_instMonadTraceCoreM;
v___x_3656_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3657_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3656_, v___x_3655_);
return v___x_3657_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; 
v___x_3658_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2);
v___f_3659_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___x_3660_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3659_, v___x_3658_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg(lean_object* v_inst_3664_, uint8_t v_phase_3665_, lean_object* v_probe_3666_){
_start:
{
lean_object* v___x_3667_; lean_object* v_toApplicative_3668_; lean_object* v_toFunctor_3669_; lean_object* v_toSeq_3670_; lean_object* v_toSeqLeft_3671_; lean_object* v_toSeqRight_3672_; lean_object* v___f_3673_; lean_object* v___f_3674_; lean_object* v___f_3675_; lean_object* v___f_3676_; lean_object* v___x_3677_; lean_object* v___f_3678_; lean_object* v___f_3679_; lean_object* v___f_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v_toApplicative_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3720_; 
v___x_3667_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3668_ = lean_ctor_get(v___x_3667_, 0);
v_toFunctor_3669_ = lean_ctor_get(v_toApplicative_3668_, 0);
v_toSeq_3670_ = lean_ctor_get(v_toApplicative_3668_, 2);
v_toSeqLeft_3671_ = lean_ctor_get(v_toApplicative_3668_, 3);
v_toSeqRight_3672_ = lean_ctor_get(v_toApplicative_3668_, 4);
v___f_3673_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3674_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3669_, 2);
v___f_3675_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3675_, 0, v_toFunctor_3669_);
v___f_3676_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3676_, 0, v_toFunctor_3669_);
v___x_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___f_3675_);
lean_ctor_set(v___x_3677_, 1, v___f_3676_);
lean_inc(v_toSeqRight_3672_);
v___f_3678_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3678_, 0, v_toSeqRight_3672_);
lean_inc(v_toSeqLeft_3671_);
v___f_3679_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3679_, 0, v_toSeqLeft_3671_);
lean_inc(v_toSeq_3670_);
v___f_3680_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3680_, 0, v_toSeq_3670_);
v___x_3681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3677_);
lean_ctor_set(v___x_3681_, 1, v___f_3673_);
lean_ctor_set(v___x_3681_, 2, v___f_3680_);
lean_ctor_set(v___x_3681_, 3, v___f_3679_);
lean_ctor_set(v___x_3681_, 4, v___f_3678_);
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
lean_ctor_set(v___x_3682_, 1, v___f_3674_);
v___x_3683_ = l_StateRefT_x27_instMonad___redArg(v___x_3682_);
v_toApplicative_3684_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3720_ == 0)
{
lean_object* v_unused_3721_; 
v_unused_3721_ = lean_ctor_get(v___x_3683_, 1);
lean_dec(v_unused_3721_);
v___x_3686_ = v___x_3683_;
v_isShared_3687_ = v_isSharedCheck_3720_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_toApplicative_3684_);
lean_dec(v___x_3683_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3720_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v_toFunctor_3688_; lean_object* v_toSeq_3689_; lean_object* v_toSeqLeft_3690_; lean_object* v_toSeqRight_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3718_; 
v_toFunctor_3688_ = lean_ctor_get(v_toApplicative_3684_, 0);
v_toSeq_3689_ = lean_ctor_get(v_toApplicative_3684_, 2);
v_toSeqLeft_3690_ = lean_ctor_get(v_toApplicative_3684_, 3);
v_toSeqRight_3691_ = lean_ctor_get(v_toApplicative_3684_, 4);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_toApplicative_3684_);
if (v_isSharedCheck_3718_ == 0)
{
lean_object* v_unused_3719_; 
v_unused_3719_ = lean_ctor_get(v_toApplicative_3684_, 1);
lean_dec(v_unused_3719_);
v___x_3693_ = v_toApplicative_3684_;
v_isShared_3694_ = v_isSharedCheck_3718_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_toSeqRight_3691_);
lean_inc(v_toSeqLeft_3690_);
lean_inc(v_toSeq_3689_);
lean_inc(v_toFunctor_3688_);
lean_dec(v_toApplicative_3684_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3718_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___f_3695_; lean_object* v___f_3696_; lean_object* v___f_3697_; lean_object* v___f_3698_; lean_object* v___x_3699_; lean_object* v___f_3700_; lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___x_3704_; 
v___f_3695_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3696_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3688_);
v___f_3697_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3697_, 0, v_toFunctor_3688_);
v___f_3698_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3698_, 0, v_toFunctor_3688_);
v___x_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___f_3697_);
lean_ctor_set(v___x_3699_, 1, v___f_3698_);
v___f_3700_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3700_, 0, v_toSeqRight_3691_);
v___f_3701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3701_, 0, v_toSeqLeft_3690_);
v___f_3702_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3702_, 0, v_toSeq_3689_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 4, v___f_3700_);
lean_ctor_set(v___x_3693_, 3, v___f_3701_);
lean_ctor_set(v___x_3693_, 2, v___f_3702_);
lean_ctor_set(v___x_3693_, 1, v___f_3695_);
lean_ctor_set(v___x_3693_, 0, v___x_3699_);
v___x_3704_ = v___x_3693_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v___f_3695_);
lean_ctor_set(v_reuseFailAlloc_3717_, 2, v___f_3702_);
lean_ctor_set(v_reuseFailAlloc_3717_, 3, v___f_3701_);
lean_ctor_set(v_reuseFailAlloc_3717_, 4, v___f_3700_);
v___x_3704_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3706_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v___f_3696_);
lean_ctor_set(v___x_3686_, 0, v___x_3704_);
v___x_3706_ = v___x_3686_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v___f_3696_);
v___x_3706_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___f_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; lean_object* v___f_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___f_3707_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___x_3708_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3709_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3);
v___x_3710_ = lean_unsigned_to_nat(0u);
v___x_3711_ = 0;
v___x_3712_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4));
v___f_3713_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_3713_, 0, v_probe_3666_);
lean_closure_set(v___f_3713_, 1, v___x_3712_);
lean_closure_set(v___f_3713_, 2, v___x_3708_);
lean_closure_set(v___f_3713_, 3, v___f_3707_);
lean_closure_set(v___f_3713_, 4, v_inst_3664_);
lean_closure_set(v___f_3713_, 5, v___x_3706_);
lean_closure_set(v___f_3713_, 6, v___x_3709_);
v___x_3714_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5));
v___x_3715_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3715_, 0, v___x_3710_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
lean_ctor_set(v___x_3715_, 2, v___f_3713_);
lean_ctor_set_uint8(v___x_3715_, sizeof(void*)*3, v_phase_3665_);
lean_ctor_set_uint8(v___x_3715_, sizeof(void*)*3 + 1, v_phase_3665_);
lean_ctor_set_uint8(v___x_3715_, sizeof(void*)*3 + 2, v___x_3711_);
return v___x_3715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(lean_object* v_inst_3722_, lean_object* v_phase_3723_, lean_object* v_probe_3724_){
_start:
{
uint8_t v_phase_boxed_3725_; lean_object* v_res_3726_; 
v_phase_boxed_3725_ = lean_unbox(v_phase_3723_);
v_res_3726_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3722_, v_phase_boxed_3725_, v_probe_3724_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass(lean_object* v_00_u03b2_3727_, lean_object* v_inst_3728_, uint8_t v_phase_3729_, lean_object* v_probe_3730_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3728_, v_phase_3729_, v_probe_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___boxed(lean_object* v_00_u03b2_3732_, lean_object* v_inst_3733_, lean_object* v_phase_3734_, lean_object* v_probe_3735_){
_start:
{
uint8_t v_phase_boxed_3736_; lean_object* v_res_3737_; 
v_phase_boxed_3736_ = lean_unbox(v_phase_3734_);
v_res_3737_ = l_Lean_Compiler_LCNF_Probe_toPass(v_00_u03b2_3732_, v_inst_3733_, v_phase_boxed_3736_, v_probe_3735_);
return v_res_3737_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = lean_unsigned_to_nat(4008565020u);
v___x_3797_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3798_ = l_Lean_Name_num___override(v___x_3797_, v___x_3796_);
return v___x_3798_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3800_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3801_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3802_ = l_Lean_Name_str___override(v___x_3801_, v___x_3800_);
return v___x_3802_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3805_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3806_ = l_Lean_Name_str___override(v___x_3805_, v___x_3804_);
return v___x_3806_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_unsigned_to_nat(2u);
v___x_3808_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3809_ = l_Lean_Name_num___override(v___x_3808_, v___x_3807_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3811_; uint8_t v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3811_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3812_ = 1;
v___x_3813_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3814_ = l_Lean_registerTraceClass(v___x_3811_, v___x_3812_, v___x_3813_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2____boxed(lean_object* v_a_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
return v_res_3816_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Probing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Probing(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Probing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Probing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Probing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Probing(builtin);
}
#ifdef __cplusplus
}
#endif
