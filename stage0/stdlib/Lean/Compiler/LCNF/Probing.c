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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__1, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__2, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__0_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1_value;
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
lean_object* v___x_532_; 
lean_inc(v_a_524_);
lean_inc_ref(v_inst_523_);
lean_inc_ref(v_inst_522_);
v___x_532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_522_, v_inst_523_, v___y_526_, v_a_524_);
if (lean_obj_tag(v___x_532_) == 1)
{
lean_object* v_val_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_544_; 
v_val_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_544_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_val_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_544_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_val_533_, v___x_537_);
lean_dec(v_val_533_);
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_522_, v_inst_523_, v___y_526_, v_a_524_, v___x_538_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_539_);
v___x_541_ = v___x_535_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_539_);
v___x_541_ = v_reuseFailAlloc_543_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; 
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v___x_532_);
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_522_, v_inst_523_, v___y_526_, v_a_524_, v___x_545_);
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed(lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_a_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(v_inst_549_, v_inst_550_, v_a_551_, v_x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__1(lean_object* v_x1_560_, lean_object* v_x2_561_, lean_object* v_x3_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_x2_561_);
lean_ctor_set(v___x_563_, 1, v_x3_562_);
v___x_564_ = lean_array_push(v_x1_560_, v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__2(lean_object* v___x_565_, lean_object* v___f_566_, lean_object* v_acc_567_, lean_object* v_l_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_565_, v___f_566_, v_acc_567_, v_l_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg(lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_data_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_582_; lean_object* v_toApplicative_583_; lean_object* v_toFunctor_584_; lean_object* v_toSeq_585_; lean_object* v_toSeqLeft_586_; lean_object* v_toSeqRight_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_toApplicative_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_678_; 
v___x_582_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_583_ = lean_ctor_get(v___x_582_, 0);
v_toFunctor_584_ = lean_ctor_get(v_toApplicative_583_, 0);
v_toSeq_585_ = lean_ctor_get(v_toApplicative_583_, 2);
v_toSeqLeft_586_ = lean_ctor_get(v_toApplicative_583_, 3);
v_toSeqRight_587_ = lean_ctor_get(v_toApplicative_583_, 4);
v___f_588_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_589_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_584_, 2);
v___f_590_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_590_, 0, v_toFunctor_584_);
v___f_591_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_591_, 0, v_toFunctor_584_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___f_590_);
lean_ctor_set(v___x_592_, 1, v___f_591_);
lean_inc(v_toSeqRight_587_);
v___f_593_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_593_, 0, v_toSeqRight_587_);
lean_inc(v_toSeqLeft_586_);
v___f_594_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_594_, 0, v_toSeqLeft_586_);
lean_inc(v_toSeq_585_);
v___f_595_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_595_, 0, v_toSeq_585_);
v___x_596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_596_, 0, v___x_592_);
lean_ctor_set(v___x_596_, 1, v___f_588_);
lean_ctor_set(v___x_596_, 2, v___f_595_);
lean_ctor_set(v___x_596_, 3, v___f_594_);
lean_ctor_set(v___x_596_, 4, v___f_593_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___f_589_);
v___x_598_ = l_StateRefT_x27_instMonad___redArg(v___x_597_);
v_toApplicative_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_678_ == 0)
{
lean_object* v_unused_679_; 
v_unused_679_ = lean_ctor_get(v___x_598_, 1);
lean_dec(v_unused_679_);
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_678_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_toApplicative_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_678_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_toFunctor_603_; lean_object* v_toSeq_604_; lean_object* v_toSeqLeft_605_; lean_object* v_toSeqRight_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_676_; 
v_toFunctor_603_ = lean_ctor_get(v_toApplicative_599_, 0);
v_toSeq_604_ = lean_ctor_get(v_toApplicative_599_, 2);
v_toSeqLeft_605_ = lean_ctor_get(v_toApplicative_599_, 3);
v_toSeqRight_606_ = lean_ctor_get(v_toApplicative_599_, 4);
v_isSharedCheck_676_ = !lean_is_exclusive(v_toApplicative_599_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v_toApplicative_599_, 1);
lean_dec(v_unused_677_);
v___x_608_ = v_toApplicative_599_;
v_isShared_609_ = v_isSharedCheck_676_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_toSeqRight_606_);
lean_inc(v_toSeqLeft_605_);
lean_inc(v_toSeq_604_);
lean_inc(v_toFunctor_603_);
lean_dec(v_toApplicative_599_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_676_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___f_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___x_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___x_620_; 
v___f_610_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_610_, 0, v_inst_574_);
lean_closure_set(v___f_610_, 1, v_inst_575_);
v___f_611_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_612_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_603_);
v___f_613_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_613_, 0, v_toFunctor_603_);
v___f_614_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_614_, 0, v_toFunctor_603_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___f_613_);
lean_ctor_set(v___x_615_, 1, v___f_614_);
v___f_616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_616_, 0, v_toSeqRight_606_);
v___f_617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_617_, 0, v_toSeqLeft_605_);
v___f_618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_618_, 0, v_toSeq_604_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 4, v___f_616_);
lean_ctor_set(v___x_608_, 3, v___f_617_);
lean_ctor_set(v___x_608_, 2, v___f_618_);
lean_ctor_set(v___x_608_, 1, v___f_611_);
lean_ctor_set(v___x_608_, 0, v___x_615_);
v___x_620_ = v___x_608_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___f_611_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v___f_618_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v___f_617_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v___f_616_);
v___x_620_ = v_reuseFailAlloc_675_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_622_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 1, v___f_612_);
lean_ctor_set(v___x_601_, 0, v___x_620_);
v___x_622_ = v___x_601_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___f_612_);
v___x_622_ = v_reuseFailAlloc_674_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_map_632_; size_t v_sz_633_; size_t v___x_634_; lean_object* v___x_747__overap_635_; lean_object* v___x_636_; 
v___x_623_ = lean_array_get_size(v_data_576_);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_unsigned_to_nat(4u);
v___x_626_ = lean_nat_mul(v___x_623_, v___x_625_);
v___x_627_ = lean_unsigned_to_nat(3u);
v___x_628_ = lean_nat_div(v___x_626_, v___x_627_);
lean_dec(v___x_626_);
v___x_629_ = l_Nat_nextPowerOfTwo(v___x_628_);
lean_dec(v___x_628_);
v___x_630_ = lean_box(0);
v___x_631_ = lean_mk_array(v___x_629_, v___x_630_);
v_map_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_map_632_, 0, v___x_624_);
lean_ctor_set(v_map_632_, 1, v___x_631_);
v_sz_633_ = lean_array_size(v_data_576_);
v___x_634_ = ((size_t)0ULL);
v___x_747__overap_635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_622_, v_data_576_, v___f_610_, v_sz_633_, v___x_634_, v_map_632_);
lean_inc(v_a_580_);
lean_inc_ref(v_a_579_);
lean_inc(v_a_578_);
lean_inc_ref(v_a_577_);
v___x_636_ = lean_apply_5(v___x_747__overap_635_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, lean_box(0));
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_665_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_665_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_665_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_665_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v_size_641_; lean_object* v_buckets_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_size_641_ = lean_ctor_get(v_a_637_, 0);
lean_inc(v_size_641_);
v_buckets_642_ = lean_ctor_get(v_a_637_, 1);
lean_inc_ref(v_buckets_642_);
lean_dec(v_a_637_);
v___x_643_ = lean_mk_empty_array_with_capacity(v_size_641_);
lean_dec(v_size_641_);
v___x_644_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_645_ = lean_array_get_size(v_buckets_642_);
v___x_646_ = lean_nat_dec_lt(v___x_624_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_648_; 
lean_dec_ref(v_buckets_642_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_643_);
v___x_648_ = v___x_639_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
else
{
lean_object* v___f_650_; uint8_t v___x_651_; 
v___f_650_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1));
v___x_651_ = lean_nat_dec_le(v___x_645_, v___x_645_);
if (v___x_651_ == 0)
{
if (v___x_646_ == 0)
{
lean_object* v___x_653_; 
lean_dec_ref(v_buckets_642_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_643_);
v___x_653_ = v___x_639_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_643_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
size_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_655_ = lean_usize_of_nat(v___x_645_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_644_, v___f_650_, v_buckets_642_, v___x_634_, v___x_655_, v___x_643_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_656_);
v___x_658_ = v___x_639_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
size_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_660_ = lean_usize_of_nat(v___x_645_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_644_, v___f_650_, v_buckets_642_, v___x_634_, v___x_660_, v___x_643_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_661_);
v___x_663_ = v___x_639_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_636_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_636_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___boxed(lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_data_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_680_, v_inst_681_, v_data_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique(lean_object* v_00_u03b1_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_data_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_691_, v_inst_692_, v_data_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___boxed(lean_object* v_00_u03b1_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_data_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Compiler_LCNF_Probe_countUnique(v_00_u03b1_700_, v_inst_701_, v_inst_702_, v_inst_703_, v_data_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_inst_701_);
return v_res_710_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(lean_object* v_l_711_, lean_object* v_r_712_){
_start:
{
lean_object* v_snd_713_; lean_object* v_snd_714_; uint8_t v___x_715_; 
v_snd_713_ = lean_ctor_get(v_l_711_, 1);
v_snd_714_ = lean_ctor_get(v_r_712_, 1);
v___x_715_ = lean_nat_dec_lt(v_snd_713_, v_snd_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0___boxed(lean_object* v_l_716_, lean_object* v_r_717_){
_start:
{
uint8_t v_res_718_; lean_object* v_r_719_; 
v_res_718_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(v_l_716_, v_r_717_);
lean_dec_ref(v_r_717_);
lean_dec_ref(v_l_716_);
v_r_719_ = lean_box(v_res_718_);
return v_r_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_721_, v_inst_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
v___x_731_ = lean_array_get_size(v_a_730_);
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_nat_dec_eq(v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_751_; 
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; 
v_unused_752_ = lean_ctor_get(v___x_729_, 0);
lean_dec(v_unused_752_);
v___x_735_ = v___x_729_;
v_isShared_736_ = v_isSharedCheck_751_;
goto v_resetjp_734_;
}
else
{
lean_dec(v___x_729_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_751_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___f_737_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___y_748_; uint8_t v___x_750_; 
v___f_737_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_sub(v___x_731_, v___x_745_);
v___x_750_ = lean_nat_dec_le(v___x_732_, v___x_746_);
if (v___x_750_ == 0)
{
lean_inc(v___x_746_);
v___y_748_ = v___x_746_;
goto v___jp_747_;
}
else
{
v___y_748_ = v___x_732_;
goto v___jp_747_;
}
v___jp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_737_, v___x_731_, v_a_730_, v___y_739_, v___y_740_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_740_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_741_);
v___x_743_ = v___x_735_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
v___jp_747_:
{
uint8_t v___x_749_; 
v___x_749_ = lean_nat_dec_le(v___y_748_, v___x_746_);
if (v___x_749_ == 0)
{
lean_dec(v___x_746_);
lean_inc(v___y_748_);
v___y_739_ = v___y_748_;
v___y_740_ = v___y_748_;
goto v___jp_738_;
}
else
{
v___y_739_ = v___y_748_;
v___y_740_ = v___x_746_;
goto v___jp_738_;
}
}
}
}
else
{
lean_dec(v_a_730_);
return v___x_729_;
}
}
else
{
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___boxed(lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(v_inst_753_, v_inst_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted(lean_object* v_00_u03b1_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_764_, v_inst_765_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
v___x_775_ = lean_array_get_size(v_a_774_);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_nat_dec_eq(v___x_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_795_; 
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v___x_773_, 0);
lean_dec(v_unused_796_);
v___x_779_ = v___x_773_;
v_isShared_780_ = v_isSharedCheck_795_;
goto v_resetjp_778_;
}
else
{
lean_dec(v___x_773_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_795_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___f_781_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___y_792_; uint8_t v___x_794_; 
v___f_781_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_sub(v___x_775_, v___x_789_);
v___x_794_ = lean_nat_dec_le(v___x_776_, v___x_790_);
if (v___x_794_ == 0)
{
lean_inc(v___x_790_);
v___y_792_ = v___x_790_;
goto v___jp_791_;
}
else
{
v___y_792_ = v___x_776_;
goto v___jp_791_;
}
v___jp_782_:
{
lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_785_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_781_, v___x_775_, v_a_774_, v___y_783_, v___y_784_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_784_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_785_);
v___x_787_ = v___x_779_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
v___jp_791_:
{
uint8_t v___x_793_; 
v___x_793_ = lean_nat_dec_le(v___y_792_, v___x_790_);
if (v___x_793_ == 0)
{
lean_dec(v___x_790_);
lean_inc(v___y_792_);
v___y_783_ = v___y_792_;
v___y_784_ = v___y_792_;
goto v___jp_782_;
}
else
{
v___y_783_ = v___y_792_;
v___y_784_ = v___x_790_;
goto v___jp_782_;
}
}
}
}
else
{
lean_dec(v_a_774_);
return v___x_773_;
}
}
else
{
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___boxed(lean_object* v_00_u03b1_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted(v_00_u03b1_797_, v_inst_798_, v_inst_799_, v_inst_800_, v_inst_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_inst_801_);
lean_dec_ref(v_inst_798_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(uint8_t v_pu_809_, lean_object* v_c_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
switch(lean_obj_tag(v_c_810_))
{
case 0:
{
lean_object* v_decl_817_; lean_object* v_k_818_; lean_object* v___x_819_; lean_object* v_value_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_decl_817_ = lean_ctor_get(v_c_810_, 0);
lean_inc_ref(v_decl_817_);
v_k_818_ = lean_ctor_get(v_c_810_, 1);
lean_inc_ref(v_k_818_);
lean_dec_ref(v_c_810_);
v___x_819_ = lean_st_ref_take(v_a_811_);
v_value_820_ = lean_ctor_get(v_decl_817_, 3);
lean_inc(v_value_820_);
lean_dec_ref(v_decl_817_);
v___x_821_ = lean_array_push(v___x_819_, v_value_820_);
v___x_822_ = lean_st_ref_set(v_a_811_, v___x_821_);
v_c_810_ = v_k_818_;
goto _start;
}
case 1:
{
lean_object* v_decl_824_; lean_object* v_k_825_; lean_object* v_value_826_; lean_object* v___x_827_; 
v_decl_824_ = lean_ctor_get(v_c_810_, 0);
lean_inc_ref(v_decl_824_);
v_k_825_ = lean_ctor_get(v_c_810_, 1);
lean_inc_ref(v_k_825_);
lean_dec_ref(v_c_810_);
v_value_826_ = lean_ctor_get(v_decl_824_, 4);
lean_inc_ref(v_value_826_);
lean_dec_ref(v_decl_824_);
v___x_827_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_809_, v_value_826_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_dec_ref(v___x_827_);
v_c_810_ = v_k_825_;
goto _start;
}
else
{
lean_dec_ref(v_k_825_);
return v___x_827_;
}
}
case 2:
{
lean_object* v_decl_829_; lean_object* v_k_830_; lean_object* v_value_831_; lean_object* v___x_832_; 
v_decl_829_ = lean_ctor_get(v_c_810_, 0);
lean_inc_ref(v_decl_829_);
v_k_830_ = lean_ctor_get(v_c_810_, 1);
lean_inc_ref(v_k_830_);
lean_dec_ref(v_c_810_);
v_value_831_ = lean_ctor_get(v_decl_829_, 4);
lean_inc_ref(v_value_831_);
lean_dec_ref(v_decl_829_);
v___x_832_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_809_, v_value_831_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_dec_ref(v___x_832_);
v_c_810_ = v_k_830_;
goto _start;
}
else
{
lean_dec_ref(v_k_830_);
return v___x_832_;
}
}
case 4:
{
lean_object* v_cases_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_856_; 
v_cases_834_ = lean_ctor_get(v_c_810_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_c_810_);
if (v_isSharedCheck_856_ == 0)
{
v___x_836_ = v_c_810_;
v_isShared_837_ = v_isSharedCheck_856_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_cases_834_);
lean_dec(v_c_810_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_856_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_alts_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_alts_838_ = lean_ctor_get(v_cases_834_, 3);
lean_inc_ref(v_alts_838_);
lean_dec_ref(v_cases_834_);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_array_get_size(v_alts_838_);
v___x_841_ = lean_box(0);
v___x_842_ = lean_nat_dec_lt(v___x_839_, v___x_840_);
if (v___x_842_ == 0)
{
lean_object* v___x_844_; 
lean_dec_ref(v_alts_838_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
lean_ctor_set(v___x_836_, 0, v___x_841_);
v___x_844_ = v___x_836_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_841_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
uint8_t v___x_846_; 
v___x_846_ = lean_nat_dec_le(v___x_840_, v___x_840_);
if (v___x_846_ == 0)
{
if (v___x_842_ == 0)
{
lean_object* v___x_848_; 
lean_dec_ref(v_alts_838_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
lean_ctor_set(v___x_836_, 0, v___x_841_);
v___x_848_ = v___x_836_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_841_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
else
{
size_t v___x_850_; size_t v___x_851_; lean_object* v___x_852_; 
lean_del_object(v___x_836_);
v___x_850_ = ((size_t)0ULL);
v___x_851_ = lean_usize_of_nat(v___x_840_);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_809_, v_alts_838_, v___x_850_, v___x_851_, v___x_841_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec_ref(v_alts_838_);
return v___x_852_;
}
}
else
{
size_t v___x_853_; size_t v___x_854_; lean_object* v___x_855_; 
lean_del_object(v___x_836_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = lean_usize_of_nat(v___x_840_);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_809_, v_alts_838_, v___x_853_, v___x_854_, v___x_841_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec_ref(v_alts_838_);
return v___x_855_;
}
}
}
}
case 7:
{
lean_object* v_k_857_; 
v_k_857_ = lean_ctor_get(v_c_810_, 3);
lean_inc_ref(v_k_857_);
lean_dec_ref(v_c_810_);
v_c_810_ = v_k_857_;
goto _start;
}
case 8:
{
lean_object* v_k_859_; 
v_k_859_ = lean_ctor_get(v_c_810_, 3);
lean_inc_ref(v_k_859_);
lean_dec_ref(v_c_810_);
v_c_810_ = v_k_859_;
goto _start;
}
case 9:
{
lean_object* v_k_861_; 
v_k_861_ = lean_ctor_get(v_c_810_, 5);
lean_inc_ref(v_k_861_);
lean_dec_ref(v_c_810_);
v_c_810_ = v_k_861_;
goto _start;
}
case 10:
{
lean_object* v_k_863_; 
v_k_863_ = lean_ctor_get(v_c_810_, 2);
lean_inc_ref(v_k_863_);
lean_dec_ref(v_c_810_);
v_c_810_ = v_k_863_;
goto _start;
}
case 11:
{
lean_object* v_k_865_; 
v_k_865_ = lean_ctor_get(v_c_810_, 2);
lean_inc_ref(v_k_865_);
lean_dec_ref(v_c_810_);
v_c_810_ = v_k_865_;
goto _start;
}
case 12:
{
lean_object* v_k_867_; 
v_k_867_ = lean_ctor_get(v_c_810_, 2);
lean_inc_ref(v_k_867_);
lean_dec_ref(v_c_810_);
v_c_810_ = v_k_867_;
goto _start;
}
case 13:
{
lean_object* v_k_869_; 
v_k_869_ = lean_ctor_get(v_c_810_, 1);
lean_inc_ref(v_k_869_);
lean_dec_ref(v_c_810_);
v_c_810_ = v_k_869_;
goto _start;
}
default: 
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v_c_810_);
v___x_871_ = lean_box(0);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(uint8_t v_pu_873_, lean_object* v_as_874_, size_t v_i_875_, size_t v_stop_876_, lean_object* v_b_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___y_885_; uint8_t v___x_891_; 
v___x_891_ = lean_usize_dec_eq(v_i_875_, v_stop_876_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
v___x_892_ = lean_array_uget_borrowed(v_as_874_, v_i_875_);
switch(lean_obj_tag(v___x_892_))
{
case 0:
{
lean_object* v_code_893_; 
v_code_893_ = lean_ctor_get(v___x_892_, 2);
lean_inc_ref(v_code_893_);
v___y_885_ = v_code_893_;
goto v___jp_884_;
}
case 1:
{
lean_object* v_code_894_; 
v_code_894_ = lean_ctor_get(v___x_892_, 1);
lean_inc_ref(v_code_894_);
v___y_885_ = v_code_894_;
goto v___jp_884_;
}
default: 
{
lean_object* v_code_895_; 
v_code_895_ = lean_ctor_get(v___x_892_, 0);
lean_inc_ref(v_code_895_);
v___y_885_ = v_code_895_;
goto v___jp_884_;
}
}
}
else
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v_b_877_);
return v___x_896_;
}
v___jp_884_:
{
lean_object* v___x_886_; 
v___x_886_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_873_, v___y_885_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; size_t v___x_888_; size_t v___x_889_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v___x_886_);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_add(v_i_875_, v___x_888_);
v_i_875_ = v___x_889_;
v_b_877_ = v_a_887_;
goto _start;
}
else
{
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0___boxed(lean_object* v_pu_897_, lean_object* v_as_898_, lean_object* v_i_899_, lean_object* v_stop_900_, lean_object* v_b_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
uint8_t v_pu_boxed_908_; size_t v_i_boxed_909_; size_t v_stop_boxed_910_; lean_object* v_res_911_; 
v_pu_boxed_908_ = lean_unbox(v_pu_897_);
v_i_boxed_909_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_stop_boxed_910_ = lean_unbox_usize(v_stop_900_);
lean_dec(v_stop_900_);
v_res_911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_boxed_908_, v_as_898_, v_i_boxed_909_, v_stop_boxed_910_, v_b_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v_as_898_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed(lean_object* v_pu_912_, lean_object* v_c_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
uint8_t v_pu_boxed_920_; lean_object* v_res_921_; 
v_pu_boxed_920_ = lean_unbox(v_pu_912_);
v_res_921_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_boxed_920_, v_c_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(lean_object* v_f_922_, lean_object* v_v_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
if (lean_obj_tag(v_v_923_) == 0)
{
lean_object* v_code_930_; lean_object* v___x_931_; 
v_code_930_ = lean_ctor_get(v_v_923_, 0);
lean_inc_ref(v_code_930_);
lean_dec_ref(v_v_923_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc_ref(v___y_925_);
lean_inc(v___y_924_);
v___x_931_ = lean_apply_7(v_f_922_, v_code_930_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
return v___x_931_;
}
else
{
lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v_f_922_);
v_isSharedCheck_939_ = !lean_is_exclusive(v_v_923_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v_v_923_, 0);
lean_dec(v_unused_940_);
v___x_933_ = v_v_923_;
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
else
{
lean_dec(v_v_923_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_939_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_box(0);
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 0);
lean_ctor_set(v___x_933_, 0, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg___boxed(lean_object* v_f_941_, lean_object* v_v_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_941_, v_v_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(uint8_t v_pu_950_, lean_object* v_f_951_, lean_object* v_v_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_951_, v_v_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___boxed(lean_object* v_pu_960_, lean_object* v_f_961_, lean_object* v_v_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
uint8_t v_pu_boxed_969_; lean_object* v_res_970_; 
v_pu_boxed_969_ = lean_unbox(v_pu_960_);
v_res_970_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(v_pu_boxed_969_, v_f_961_, v_v_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(uint8_t v_pu_971_, lean_object* v_as_972_, size_t v_i_973_, size_t v_stop_974_, lean_object* v_b_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
uint8_t v___x_982_; 
v___x_982_ = lean_usize_dec_eq(v_i_973_, v_stop_974_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v_value_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_983_ = lean_array_uget_borrowed(v_as_972_, v_i_973_);
v_value_984_ = lean_ctor_get(v___x_983_, 1);
v___x_985_ = lean_box(v_pu_971_);
v___x_986_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed), 8, 1);
lean_closure_set(v___x_986_, 0, v___x_985_);
lean_inc_ref(v_value_984_);
v___x_987_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v___x_986_, v_value_984_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; size_t v___x_989_; size_t v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v___x_987_);
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_add(v_i_973_, v___x_989_);
v_i_973_ = v___x_990_;
v_b_975_ = v_a_988_;
goto _start;
}
else
{
return v___x_987_;
}
}
else
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_b_975_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1___boxed(lean_object* v_pu_993_, lean_object* v_as_994_, lean_object* v_i_995_, lean_object* v_stop_996_, lean_object* v_b_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v_pu_boxed_1004_; size_t v_i_boxed_1005_; size_t v_stop_boxed_1006_; lean_object* v_res_1007_; 
v_pu_boxed_1004_ = lean_unbox(v_pu_993_);
v_i_boxed_1005_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_stop_boxed_1006_ = lean_unbox_usize(v_stop_996_);
lean_dec(v_stop_996_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_boxed_1004_, v_as_994_, v_i_boxed_1005_, v_stop_boxed_1006_, v_b_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v_as_994_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(uint8_t v_pu_1008_, lean_object* v_decls_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_array_get_size(v_decls_1009_);
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_nat_dec_lt(v___x_1016_, v___x_1017_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
return v___x_1020_;
}
else
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_nat_dec_le(v___x_1017_, v___x_1017_);
if (v___x_1021_ == 0)
{
if (v___x_1019_ == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1018_);
return v___x_1022_;
}
else
{
size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = lean_usize_of_nat(v___x_1017_);
v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_1008_, v_decls_1009_, v___x_1023_, v___x_1024_, v___x_1018_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
return v___x_1025_;
}
}
else
{
size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = lean_usize_of_nat(v___x_1017_);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_1008_, v_decls_1009_, v___x_1026_, v___x_1027_, v___x_1018_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start___boxed(lean_object* v_pu_1029_, lean_object* v_decls_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
uint8_t v_pu_boxed_1037_; lean_object* v_res_1038_; 
v_pu_boxed_1037_ = lean_unbox(v_pu_1029_);
v_res_1038_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_boxed_1037_, v_decls_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_decls_1030_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues(uint8_t v_pu_1041_, lean_object* v_decls_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0));
v___x_1049_ = lean_st_mk_ref(v___x_1048_);
v___x_1050_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_1041_, v_decls_1042_, v___x_1049_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1058_; 
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; 
v_unused_1059_ = lean_ctor_get(v___x_1050_, 0);
lean_dec(v_unused_1059_);
v___x_1052_ = v___x_1050_;
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
else
{
lean_dec(v___x_1050_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1054_ = lean_st_ref_get(v___x_1049_);
lean_dec(v___x_1049_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1054_);
v___x_1056_ = v___x_1052_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v___x_1049_);
v_a_1060_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1050_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1050_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues___boxed(lean_object* v_pu_1068_, lean_object* v_decls_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
uint8_t v_pu_boxed_1075_; lean_object* v_res_1076_; 
v_pu_boxed_1075_ = lean_unbox(v_pu_1068_);
v_res_1076_ = l_Lean_Compiler_LCNF_Probe_getLetValues(v_pu_boxed_1075_, v_decls_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec_ref(v_decls_1069_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(uint8_t v_pu_1077_, lean_object* v_code_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
switch(lean_obj_tag(v_code_1078_))
{
case 0:
{
lean_object* v_k_1085_; 
v_k_1085_ = lean_ctor_get(v_code_1078_, 1);
lean_inc_ref(v_k_1085_);
lean_dec_ref(v_code_1078_);
v_code_1078_ = v_k_1085_;
goto _start;
}
case 1:
{
lean_object* v_decl_1087_; lean_object* v_k_1088_; lean_object* v_value_1089_; lean_object* v___x_1090_; 
v_decl_1087_ = lean_ctor_get(v_code_1078_, 0);
lean_inc_ref(v_decl_1087_);
v_k_1088_ = lean_ctor_get(v_code_1078_, 1);
lean_inc_ref(v_k_1088_);
lean_dec_ref(v_code_1078_);
v_value_1089_ = lean_ctor_get(v_decl_1087_, 4);
lean_inc_ref(v_value_1089_);
lean_dec_ref(v_decl_1087_);
v___x_1090_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1077_, v_value_1089_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_dec_ref(v___x_1090_);
v_code_1078_ = v_k_1088_;
goto _start;
}
else
{
lean_dec_ref(v_k_1088_);
return v___x_1090_;
}
}
case 2:
{
lean_object* v_decl_1092_; lean_object* v_k_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v_value_1097_; lean_object* v___x_1098_; 
v_decl_1092_ = lean_ctor_get(v_code_1078_, 0);
lean_inc_ref_n(v_decl_1092_, 2);
v_k_1093_ = lean_ctor_get(v_code_1078_, 1);
lean_inc_ref(v_k_1093_);
lean_dec_ref(v_code_1078_);
v___x_1094_ = lean_st_ref_take(v_a_1079_);
v___x_1095_ = lean_array_push(v___x_1094_, v_decl_1092_);
v___x_1096_ = lean_st_ref_set(v_a_1079_, v___x_1095_);
v_value_1097_ = lean_ctor_get(v_decl_1092_, 4);
lean_inc_ref(v_value_1097_);
lean_dec_ref(v_decl_1092_);
v___x_1098_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1077_, v_value_1097_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_dec_ref(v___x_1098_);
v_code_1078_ = v_k_1093_;
goto _start;
}
else
{
lean_dec_ref(v_k_1093_);
return v___x_1098_;
}
}
case 4:
{
lean_object* v_cases_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1122_; 
v_cases_1100_ = lean_ctor_get(v_code_1078_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_code_1078_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1102_ = v_code_1078_;
v_isShared_1103_ = v_isSharedCheck_1122_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_cases_1100_);
lean_dec(v_code_1078_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1122_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_alts_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_alts_1104_ = lean_ctor_get(v_cases_1100_, 3);
lean_inc_ref(v_alts_1104_);
lean_dec_ref(v_cases_1100_);
v___x_1105_ = lean_unsigned_to_nat(0u);
v___x_1106_ = lean_array_get_size(v_alts_1104_);
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_nat_dec_lt(v___x_1105_, v___x_1106_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref(v_alts_1104_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1107_);
v___x_1110_ = v___x_1102_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1107_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
else
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_nat_dec_le(v___x_1106_, v___x_1106_);
if (v___x_1112_ == 0)
{
if (v___x_1108_ == 0)
{
lean_object* v___x_1114_; 
lean_dec_ref(v_alts_1104_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1107_);
v___x_1114_ = v___x_1102_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1107_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
else
{
size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
lean_del_object(v___x_1102_);
v___x_1116_ = ((size_t)0ULL);
v___x_1117_ = lean_usize_of_nat(v___x_1106_);
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1077_, v_alts_1104_, v___x_1116_, v___x_1117_, v___x_1107_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec_ref(v_alts_1104_);
return v___x_1118_;
}
}
else
{
size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
lean_del_object(v___x_1102_);
v___x_1119_ = ((size_t)0ULL);
v___x_1120_ = lean_usize_of_nat(v___x_1106_);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1077_, v_alts_1104_, v___x_1119_, v___x_1120_, v___x_1107_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec_ref(v_alts_1104_);
return v___x_1121_;
}
}
}
}
case 7:
{
lean_object* v_k_1123_; 
v_k_1123_ = lean_ctor_get(v_code_1078_, 3);
lean_inc_ref(v_k_1123_);
lean_dec_ref(v_code_1078_);
v_code_1078_ = v_k_1123_;
goto _start;
}
case 8:
{
lean_object* v_k_1125_; 
v_k_1125_ = lean_ctor_get(v_code_1078_, 3);
lean_inc_ref(v_k_1125_);
lean_dec_ref(v_code_1078_);
v_code_1078_ = v_k_1125_;
goto _start;
}
case 9:
{
lean_object* v_k_1127_; 
v_k_1127_ = lean_ctor_get(v_code_1078_, 5);
lean_inc_ref(v_k_1127_);
lean_dec_ref(v_code_1078_);
v_code_1078_ = v_k_1127_;
goto _start;
}
case 10:
{
lean_object* v_k_1129_; 
v_k_1129_ = lean_ctor_get(v_code_1078_, 2);
lean_inc_ref(v_k_1129_);
lean_dec_ref(v_code_1078_);
v_code_1078_ = v_k_1129_;
goto _start;
}
case 11:
{
lean_object* v_k_1131_; 
v_k_1131_ = lean_ctor_get(v_code_1078_, 2);
lean_inc_ref(v_k_1131_);
lean_dec_ref(v_code_1078_);
v_code_1078_ = v_k_1131_;
goto _start;
}
case 12:
{
lean_object* v_k_1133_; 
v_k_1133_ = lean_ctor_get(v_code_1078_, 2);
lean_inc_ref(v_k_1133_);
lean_dec_ref(v_code_1078_);
v_code_1078_ = v_k_1133_;
goto _start;
}
case 13:
{
lean_object* v_k_1135_; 
v_k_1135_ = lean_ctor_get(v_code_1078_, 1);
lean_inc_ref(v_k_1135_);
lean_dec_ref(v_code_1078_);
v_code_1078_ = v_k_1135_;
goto _start;
}
default: 
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec_ref(v_code_1078_);
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(uint8_t v_pu_1139_, lean_object* v_as_1140_, size_t v_i_1141_, size_t v_stop_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___y_1151_; uint8_t v___x_1157_; 
v___x_1157_ = lean_usize_dec_eq(v_i_1141_, v_stop_1142_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_array_uget_borrowed(v_as_1140_, v_i_1141_);
switch(lean_obj_tag(v___x_1158_))
{
case 0:
{
lean_object* v_code_1159_; 
v_code_1159_ = lean_ctor_get(v___x_1158_, 2);
lean_inc_ref(v_code_1159_);
v___y_1151_ = v_code_1159_;
goto v___jp_1150_;
}
case 1:
{
lean_object* v_code_1160_; 
v_code_1160_ = lean_ctor_get(v___x_1158_, 1);
lean_inc_ref(v_code_1160_);
v___y_1151_ = v_code_1160_;
goto v___jp_1150_;
}
default: 
{
lean_object* v_code_1161_; 
v_code_1161_ = lean_ctor_get(v___x_1158_, 0);
lean_inc_ref(v_code_1161_);
v___y_1151_ = v_code_1161_;
goto v___jp_1150_;
}
}
}
else
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_b_1143_);
return v___x_1162_;
}
v___jp_1150_:
{
lean_object* v___x_1152_; 
v___x_1152_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1139_, v___y_1151_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; size_t v___x_1154_; size_t v___x_1155_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = ((size_t)1ULL);
v___x_1155_ = lean_usize_add(v_i_1141_, v___x_1154_);
v_i_1141_ = v___x_1155_;
v_b_1143_ = v_a_1153_;
goto _start;
}
else
{
return v___x_1152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0___boxed(lean_object* v_pu_1163_, lean_object* v_as_1164_, lean_object* v_i_1165_, lean_object* v_stop_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v_pu_boxed_1174_; size_t v_i_boxed_1175_; size_t v_stop_boxed_1176_; lean_object* v_res_1177_; 
v_pu_boxed_1174_ = lean_unbox(v_pu_1163_);
v_i_boxed_1175_ = lean_unbox_usize(v_i_1165_);
lean_dec(v_i_1165_);
v_stop_boxed_1176_ = lean_unbox_usize(v_stop_1166_);
lean_dec(v_stop_1166_);
v_res_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_boxed_1174_, v_as_1164_, v_i_boxed_1175_, v_stop_boxed_1176_, v_b_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v_as_1164_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed(lean_object* v_pu_1178_, lean_object* v_code_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
uint8_t v_pu_boxed_1186_; lean_object* v_res_1187_; 
v_pu_boxed_1186_ = lean_unbox(v_pu_1178_);
v_res_1187_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_boxed_1186_, v_code_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(lean_object* v_f_1188_, lean_object* v_v_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
if (lean_obj_tag(v_v_1189_) == 0)
{
lean_object* v_code_1196_; lean_object* v___x_1197_; 
v_code_1196_ = lean_ctor_get(v_v_1189_, 0);
lean_inc_ref(v_code_1196_);
lean_dec_ref(v_v_1189_);
lean_inc(v___y_1194_);
lean_inc_ref(v___y_1193_);
lean_inc(v___y_1192_);
lean_inc_ref(v___y_1191_);
lean_inc(v___y_1190_);
v___x_1197_ = lean_apply_7(v_f_1188_, v_code_1196_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, lean_box(0));
return v___x_1197_;
}
else
{
lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1205_; 
lean_dec_ref(v_f_1188_);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_v_1189_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v_v_1189_, 0);
lean_dec(v_unused_1206_);
v___x_1199_ = v_v_1189_;
v_isShared_1200_ = v_isSharedCheck_1205_;
goto v_resetjp_1198_;
}
else
{
lean_dec(v_v_1189_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1205_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_box(0);
if (v_isShared_1200_ == 0)
{
lean_ctor_set_tag(v___x_1199_, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg___boxed(lean_object* v_f_1207_, lean_object* v_v_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1207_, v_v_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(uint8_t v_pu_1216_, lean_object* v_f_1217_, lean_object* v_v_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1217_, v_v_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___boxed(lean_object* v_pu_1226_, lean_object* v_f_1227_, lean_object* v_v_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v_pu_boxed_1235_; lean_object* v_res_1236_; 
v_pu_boxed_1235_ = lean_unbox(v_pu_1226_);
v_res_1236_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(v_pu_boxed_1235_, v_f_1227_, v_v_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(uint8_t v_pu_1237_, lean_object* v_as_1238_, size_t v_i_1239_, size_t v_stop_1240_, lean_object* v_b_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_usize_dec_eq(v_i_1239_, v_stop_1240_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v_value_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1249_ = lean_array_uget_borrowed(v_as_1238_, v_i_1239_);
v_value_1250_ = lean_ctor_get(v___x_1249_, 1);
v___x_1251_ = lean_box(v_pu_1237_);
v___x_1252_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed), 8, 1);
lean_closure_set(v___x_1252_, 0, v___x_1251_);
lean_inc_ref(v_value_1250_);
v___x_1253_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v___x_1252_, v_value_1250_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; size_t v___x_1255_; size_t v___x_1256_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_add(v_i_1239_, v___x_1255_);
v_i_1239_ = v___x_1256_;
v_b_1241_ = v_a_1254_;
goto _start;
}
else
{
return v___x_1253_;
}
}
else
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_b_1241_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1___boxed(lean_object* v_pu_1259_, lean_object* v_as_1260_, lean_object* v_i_1261_, lean_object* v_stop_1262_, lean_object* v_b_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
uint8_t v_pu_boxed_1270_; size_t v_i_boxed_1271_; size_t v_stop_boxed_1272_; lean_object* v_res_1273_; 
v_pu_boxed_1270_ = lean_unbox(v_pu_1259_);
v_i_boxed_1271_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_stop_boxed_1272_ = lean_unbox_usize(v_stop_1262_);
lean_dec(v_stop_1262_);
v_res_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_boxed_1270_, v_as_1260_, v_i_boxed_1271_, v_stop_boxed_1272_, v_b_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v_as_1260_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(uint8_t v_pu_1274_, lean_object* v_decls_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = lean_array_get_size(v_decls_1275_);
v___x_1284_ = lean_box(0);
v___x_1285_ = lean_nat_dec_lt(v___x_1282_, v___x_1283_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
return v___x_1286_;
}
else
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_le(v___x_1283_, v___x_1283_);
if (v___x_1287_ == 0)
{
if (v___x_1285_ == 0)
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1284_);
return v___x_1288_;
}
else
{
size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = lean_usize_of_nat(v___x_1283_);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1274_, v_decls_1275_, v___x_1289_, v___x_1290_, v___x_1284_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
return v___x_1291_;
}
}
else
{
size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = lean_usize_of_nat(v___x_1283_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1274_, v_decls_1275_, v___x_1292_, v___x_1293_, v___x_1284_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
return v___x_1294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start___boxed(lean_object* v_pu_1295_, lean_object* v_decls_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
uint8_t v_pu_boxed_1303_; lean_object* v_res_1304_; 
v_pu_boxed_1303_ = lean_unbox(v_pu_1295_);
v_res_1304_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_boxed_1303_, v_decls_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_decls_1296_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps(uint8_t v_pu_1307_, lean_object* v_decls_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getJps___closed__0));
v___x_1315_ = lean_st_mk_ref(v___x_1314_);
v___x_1316_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_1307_, v_decls_1308_, v___x_1315_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v___x_1316_, 0);
lean_dec(v_unused_1325_);
v___x_1318_ = v___x_1316_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v___x_1316_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_st_ref_get(v___x_1315_);
lean_dec(v___x_1315_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v___x_1315_);
v_a_1326_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1316_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1316_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps___boxed(lean_object* v_pu_1334_, lean_object* v_decls_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
uint8_t v_pu_boxed_1341_; lean_object* v_res_1342_; 
v_pu_boxed_1341_ = lean_unbox(v_pu_1334_);
v_res_1342_ = l_Lean_Compiler_LCNF_Probe_getJps(v_pu_boxed_1341_, v_decls_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec_ref(v_decls_1335_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(uint8_t v_pu_1343_, lean_object* v_f_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
switch(lean_obj_tag(v_a_1345_))
{
case 0:
{
lean_object* v_decl_1351_; lean_object* v_k_1352_; lean_object* v___x_1353_; 
v_decl_1351_ = lean_ctor_get(v_a_1345_, 0);
lean_inc_ref(v_decl_1351_);
v_k_1352_ = lean_ctor_get(v_a_1345_, 1);
lean_inc_ref(v_k_1352_);
lean_dec_ref(v_a_1345_);
lean_inc_ref(v_f_1344_);
lean_inc(v_a_1349_);
lean_inc_ref(v_a_1348_);
lean_inc(v_a_1347_);
lean_inc_ref(v_a_1346_);
v___x_1353_ = lean_apply_6(v_f_1344_, v_decl_1351_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, lean_box(0));
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; uint8_t v___x_1355_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
v___x_1355_ = lean_unbox(v_a_1354_);
lean_dec(v_a_1354_);
if (v___x_1355_ == 0)
{
lean_dec_ref(v___x_1353_);
v_a_1345_ = v_k_1352_;
goto _start;
}
else
{
lean_dec_ref(v_k_1352_);
lean_dec_ref(v_f_1344_);
return v___x_1353_;
}
}
else
{
lean_dec_ref(v_k_1352_);
lean_dec_ref(v_f_1344_);
return v___x_1353_;
}
}
case 1:
{
lean_object* v_decl_1357_; lean_object* v_k_1358_; lean_object* v_value_1359_; lean_object* v___x_1360_; 
v_decl_1357_ = lean_ctor_get(v_a_1345_, 0);
lean_inc_ref(v_decl_1357_);
v_k_1358_ = lean_ctor_get(v_a_1345_, 1);
lean_inc_ref(v_k_1358_);
lean_dec_ref(v_a_1345_);
v_value_1359_ = lean_ctor_get(v_decl_1357_, 4);
lean_inc_ref(v_value_1359_);
lean_dec_ref(v_decl_1357_);
lean_inc_ref(v_f_1344_);
v___x_1360_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1343_, v_f_1344_, v_value_1359_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; uint8_t v___x_1362_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
v___x_1362_ = lean_unbox(v_a_1361_);
lean_dec(v_a_1361_);
if (v___x_1362_ == 0)
{
lean_dec_ref(v___x_1360_);
v_a_1345_ = v_k_1358_;
goto _start;
}
else
{
lean_dec_ref(v_k_1358_);
lean_dec_ref(v_f_1344_);
return v___x_1360_;
}
}
else
{
lean_dec_ref(v_k_1358_);
lean_dec_ref(v_f_1344_);
return v___x_1360_;
}
}
case 2:
{
lean_object* v_decl_1364_; lean_object* v_k_1365_; lean_object* v_value_1366_; lean_object* v___x_1367_; 
v_decl_1364_ = lean_ctor_get(v_a_1345_, 0);
lean_inc_ref(v_decl_1364_);
v_k_1365_ = lean_ctor_get(v_a_1345_, 1);
lean_inc_ref(v_k_1365_);
lean_dec_ref(v_a_1345_);
v_value_1366_ = lean_ctor_get(v_decl_1364_, 4);
lean_inc_ref(v_value_1366_);
lean_dec_ref(v_decl_1364_);
lean_inc_ref(v_f_1344_);
v___x_1367_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1343_, v_f_1344_, v_value_1366_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; uint8_t v___x_1369_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
v___x_1369_ = lean_unbox(v_a_1368_);
lean_dec(v_a_1368_);
if (v___x_1369_ == 0)
{
lean_dec_ref(v___x_1367_);
v_a_1345_ = v_k_1365_;
goto _start;
}
else
{
lean_dec_ref(v_k_1365_);
lean_dec_ref(v_f_1344_);
return v___x_1367_;
}
}
else
{
lean_dec_ref(v_k_1365_);
lean_dec_ref(v_f_1344_);
return v___x_1367_;
}
}
case 4:
{
lean_object* v_cases_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1390_; 
v_cases_1371_ = lean_ctor_get(v_a_1345_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_a_1345_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1373_ = v_a_1345_;
v_isShared_1374_ = v_isSharedCheck_1390_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_cases_1371_);
lean_dec(v_a_1345_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1390_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_alts_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v_alts_1375_ = lean_ctor_get(v_cases_1371_, 3);
lean_inc_ref(v_alts_1375_);
lean_dec_ref(v_cases_1371_);
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = lean_array_get_size(v_alts_1375_);
v___x_1378_ = lean_nat_dec_lt(v___x_1376_, v___x_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_dec_ref(v_alts_1375_);
lean_dec_ref(v_f_1344_);
v___x_1379_ = lean_box(v___x_1378_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1379_);
v___x_1381_ = v___x_1373_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
else
{
if (v___x_1378_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
lean_dec_ref(v_alts_1375_);
lean_dec_ref(v_f_1344_);
v___x_1383_ = lean_box(v___x_1378_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1383_);
v___x_1385_ = v___x_1373_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
else
{
size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
lean_del_object(v___x_1373_);
v___x_1387_ = ((size_t)0ULL);
v___x_1388_ = lean_usize_of_nat(v___x_1377_);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_1343_, v_f_1344_, v_alts_1375_, v___x_1387_, v___x_1388_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec_ref(v_alts_1375_);
return v___x_1389_;
}
}
}
}
case 7:
{
lean_object* v_k_1391_; 
v_k_1391_ = lean_ctor_get(v_a_1345_, 3);
lean_inc_ref(v_k_1391_);
lean_dec_ref(v_a_1345_);
v_a_1345_ = v_k_1391_;
goto _start;
}
case 8:
{
lean_object* v_k_1393_; 
v_k_1393_ = lean_ctor_get(v_a_1345_, 3);
lean_inc_ref(v_k_1393_);
lean_dec_ref(v_a_1345_);
v_a_1345_ = v_k_1393_;
goto _start;
}
case 9:
{
lean_object* v_k_1395_; 
v_k_1395_ = lean_ctor_get(v_a_1345_, 5);
lean_inc_ref(v_k_1395_);
lean_dec_ref(v_a_1345_);
v_a_1345_ = v_k_1395_;
goto _start;
}
case 10:
{
lean_object* v_k_1397_; 
v_k_1397_ = lean_ctor_get(v_a_1345_, 2);
lean_inc_ref(v_k_1397_);
lean_dec_ref(v_a_1345_);
v_a_1345_ = v_k_1397_;
goto _start;
}
case 11:
{
lean_object* v_k_1399_; 
v_k_1399_ = lean_ctor_get(v_a_1345_, 2);
lean_inc_ref(v_k_1399_);
lean_dec_ref(v_a_1345_);
v_a_1345_ = v_k_1399_;
goto _start;
}
case 12:
{
lean_object* v_k_1401_; 
v_k_1401_ = lean_ctor_get(v_a_1345_, 2);
lean_inc_ref(v_k_1401_);
lean_dec_ref(v_a_1345_);
v_a_1345_ = v_k_1401_;
goto _start;
}
case 13:
{
lean_object* v_k_1403_; 
v_k_1403_ = lean_ctor_get(v_a_1345_, 1);
lean_inc_ref(v_k_1403_);
lean_dec_ref(v_a_1345_);
v_a_1345_ = v_k_1403_;
goto _start;
}
default: 
{
uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_f_1344_);
v___x_1405_ = 0;
v___x_1406_ = lean_box(v___x_1405_);
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(uint8_t v_pu_1408_, lean_object* v_f_1409_, lean_object* v_as_1410_, size_t v_i_1411_, size_t v_stop_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_usize_dec_eq(v_i_1411_, v_stop_1412_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; lean_object* v___y_1421_; lean_object* v___x_1436_; 
v___x_1419_ = 1;
v___x_1436_ = lean_array_uget_borrowed(v_as_1410_, v_i_1411_);
switch(lean_obj_tag(v___x_1436_))
{
case 0:
{
lean_object* v_code_1437_; 
v_code_1437_ = lean_ctor_get(v___x_1436_, 2);
lean_inc_ref(v_code_1437_);
v___y_1421_ = v_code_1437_;
goto v___jp_1420_;
}
case 1:
{
lean_object* v_code_1438_; 
v_code_1438_ = lean_ctor_get(v___x_1436_, 1);
lean_inc_ref(v_code_1438_);
v___y_1421_ = v_code_1438_;
goto v___jp_1420_;
}
default: 
{
lean_object* v_code_1439_; 
v_code_1439_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_ref(v_code_1439_);
v___y_1421_ = v_code_1439_;
goto v___jp_1420_;
}
}
v___jp_1420_:
{
lean_object* v___x_1422_; 
lean_inc_ref(v_f_1409_);
v___x_1422_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1408_, v_f_1409_, v___y_1421_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1435_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1435_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1435_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_unbox(v_a_1423_);
lean_dec(v_a_1423_);
if (v___x_1427_ == 0)
{
size_t v___x_1428_; size_t v___x_1429_; 
lean_del_object(v___x_1425_);
v___x_1428_ = ((size_t)1ULL);
v___x_1429_ = lean_usize_add(v_i_1411_, v___x_1428_);
v_i_1411_ = v___x_1429_;
goto _start;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
lean_dec_ref(v_f_1409_);
v___x_1431_ = lean_box(v___x_1419_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1431_);
v___x_1433_ = v___x_1425_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_dec_ref(v_f_1409_);
return v___x_1422_;
}
}
}
else
{
uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec_ref(v_f_1409_);
v___x_1440_ = 0;
v___x_1441_ = lean_box(v___x_1440_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0___boxed(lean_object* v_pu_1443_, lean_object* v_f_1444_, lean_object* v_as_1445_, lean_object* v_i_1446_, lean_object* v_stop_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
uint8_t v_pu_boxed_1453_; size_t v_i_boxed_1454_; size_t v_stop_boxed_1455_; lean_object* v_res_1456_; 
v_pu_boxed_1453_ = lean_unbox(v_pu_1443_);
v_i_boxed_1454_ = lean_unbox_usize(v_i_1446_);
lean_dec(v_i_1446_);
v_stop_boxed_1455_ = lean_unbox_usize(v_stop_1447_);
lean_dec(v_stop_1447_);
v_res_1456_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_boxed_1453_, v_f_1444_, v_as_1445_, v_i_boxed_1454_, v_stop_boxed_1455_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec_ref(v_as_1445_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed(lean_object* v_pu_1457_, lean_object* v_f_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
uint8_t v_pu_boxed_1465_; lean_object* v_res_1466_; 
v_pu_boxed_1465_ = lean_unbox(v_pu_1457_);
v_res_1466_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_boxed_1465_, v_f_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec(v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(lean_object* v_v_1467_, lean_object* v_f_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
if (lean_obj_tag(v_v_1467_) == 0)
{
lean_object* v_code_1474_; lean_object* v___x_1475_; 
v_code_1474_ = lean_ctor_get(v_v_1467_, 0);
lean_inc_ref(v_code_1474_);
lean_dec_ref(v_v_1467_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
v___x_1475_ = lean_apply_6(v_f_1468_, v_code_1474_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, lean_box(0));
return v___x_1475_;
}
else
{
lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v_f_1468_);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_v_1467_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v_v_1467_, 0);
lean_dec(v_unused_1485_);
v___x_1477_ = v_v_1467_;
v_isShared_1478_ = v_isSharedCheck_1484_;
goto v_resetjp_1476_;
}
else
{
lean_dec(v_v_1467_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1484_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
uint8_t v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1479_ = 0;
v___x_1480_ = lean_box(v___x_1479_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1480_);
v___x_1482_ = v___x_1477_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg___boxed(lean_object* v_v_1486_, lean_object* v_f_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1486_, v_f_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(uint8_t v_pu_1494_, lean_object* v_v_1495_, lean_object* v_f_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1495_, v_f_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___boxed(lean_object* v_pu_1503_, lean_object* v_v_1504_, lean_object* v_f_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
uint8_t v_pu_boxed_1511_; lean_object* v_res_1512_; 
v_pu_boxed_1511_ = lean_unbox(v_pu_1503_);
v_res_1512_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(v_pu_boxed_1511_, v_v_1504_, v_f_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(uint8_t v_pu_1513_, lean_object* v_f_1514_, lean_object* v_as_1515_, size_t v_i_1516_, size_t v_stop_1517_, lean_object* v_b_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_usize_dec_eq(v_i_1516_, v_stop_1517_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v_value_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1525_ = lean_array_uget_borrowed(v_as_1515_, v_i_1516_);
v_value_1526_ = lean_ctor_get(v___x_1525_, 1);
v___x_1527_ = lean_box(v_pu_1513_);
lean_inc_ref(v_f_1514_);
v___x_1528_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed), 8, 2);
lean_closure_set(v___x_1528_, 0, v___x_1527_);
lean_closure_set(v___x_1528_, 1, v_f_1514_);
lean_inc_ref(v_value_1526_);
v___x_1529_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1526_, v___x_1528_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v_a_1532_; uint8_t v___x_1536_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v___x_1536_ = lean_unbox(v_a_1530_);
lean_dec(v_a_1530_);
if (v___x_1536_ == 0)
{
v_a_1532_ = v_b_1518_;
goto v___jp_1531_;
}
else
{
lean_object* v___x_1537_; 
lean_inc(v___x_1525_);
v___x_1537_ = lean_array_push(v_b_1518_, v___x_1525_);
v_a_1532_ = v___x_1537_;
goto v___jp_1531_;
}
v___jp_1531_:
{
size_t v___x_1533_; size_t v___x_1534_; 
v___x_1533_ = ((size_t)1ULL);
v___x_1534_ = lean_usize_add(v_i_1516_, v___x_1533_);
v_i_1516_ = v___x_1534_;
v_b_1518_ = v_a_1532_;
goto _start;
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref(v_b_1518_);
lean_dec_ref(v_f_1514_);
v_a_1538_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1529_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1529_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_object* v___x_1546_; 
lean_dec_ref(v_f_1514_);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v_b_1518_);
return v___x_1546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1___boxed(lean_object* v_pu_1547_, lean_object* v_f_1548_, lean_object* v_as_1549_, lean_object* v_i_1550_, lean_object* v_stop_1551_, lean_object* v_b_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v_pu_boxed_1558_; size_t v_i_boxed_1559_; size_t v_stop_boxed_1560_; lean_object* v_res_1561_; 
v_pu_boxed_1558_ = lean_unbox(v_pu_1547_);
v_i_boxed_1559_ = lean_unbox_usize(v_i_1550_);
lean_dec(v_i_1550_);
v_stop_boxed_1560_ = lean_unbox_usize(v_stop_1551_);
lean_dec(v_stop_1551_);
v_res_1561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_boxed_1558_, v_f_1548_, v_as_1549_, v_i_boxed_1559_, v_stop_boxed_1560_, v_b_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v_as_1549_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet(uint8_t v_pu_1564_, lean_object* v_f_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_array_get_size(v_a_1566_);
v___x_1574_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1575_ = lean_nat_dec_lt(v___x_1572_, v___x_1573_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref(v_f_1565_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
return v___x_1576_;
}
else
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_nat_dec_le(v___x_1573_, v___x_1573_);
if (v___x_1577_ == 0)
{
if (v___x_1575_ == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref(v_f_1565_);
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1574_);
return v___x_1578_;
}
else
{
size_t v___x_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = lean_usize_of_nat(v___x_1573_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1564_, v_f_1565_, v_a_1566_, v___x_1579_, v___x_1580_, v___x_1574_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
return v___x_1581_;
}
}
else
{
size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = lean_usize_of_nat(v___x_1573_);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1564_, v_f_1565_, v_a_1566_, v___x_1582_, v___x_1583_, v___x_1574_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
return v___x_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet___boxed(lean_object* v_pu_1585_, lean_object* v_f_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
uint8_t v_pu_boxed_1593_; lean_object* v_res_1594_; 
v_pu_boxed_1593_ = lean_unbox(v_pu_1585_);
v_res_1594_ = l_Lean_Compiler_LCNF_Probe_filterByLet(v_pu_boxed_1593_, v_f_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec_ref(v_a_1587_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(uint8_t v_pu_1595_, lean_object* v_f_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
switch(lean_obj_tag(v_a_1597_))
{
case 0:
{
lean_object* v_k_1603_; 
v_k_1603_ = lean_ctor_get(v_a_1597_, 1);
lean_inc_ref(v_k_1603_);
lean_dec_ref(v_a_1597_);
v_a_1597_ = v_k_1603_;
goto _start;
}
case 1:
{
lean_object* v_decl_1605_; lean_object* v_k_1606_; lean_object* v___x_1607_; 
v_decl_1605_ = lean_ctor_get(v_a_1597_, 0);
lean_inc_ref_n(v_decl_1605_, 2);
v_k_1606_ = lean_ctor_get(v_a_1597_, 1);
lean_inc_ref(v_k_1606_);
lean_dec_ref(v_a_1597_);
lean_inc_ref(v_f_1596_);
lean_inc(v_a_1601_);
lean_inc_ref(v_a_1600_);
lean_inc(v_a_1599_);
lean_inc_ref(v_a_1598_);
v___x_1607_ = lean_apply_6(v_f_1596_, v_decl_1605_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, lean_box(0));
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; uint8_t v___x_1609_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
v___x_1609_ = lean_unbox(v_a_1608_);
lean_dec(v_a_1608_);
if (v___x_1609_ == 0)
{
lean_object* v_value_1610_; lean_object* v___x_1611_; 
lean_dec_ref(v___x_1607_);
v_value_1610_ = lean_ctor_get(v_decl_1605_, 4);
lean_inc_ref(v_value_1610_);
lean_dec_ref(v_decl_1605_);
lean_inc_ref(v_f_1596_);
v___x_1611_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1595_, v_f_1596_, v_value_1610_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; uint8_t v___x_1613_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
v___x_1613_ = lean_unbox(v_a_1612_);
lean_dec(v_a_1612_);
if (v___x_1613_ == 0)
{
lean_dec_ref(v___x_1611_);
v_a_1597_ = v_k_1606_;
goto _start;
}
else
{
lean_dec_ref(v_k_1606_);
lean_dec_ref(v_f_1596_);
return v___x_1611_;
}
}
else
{
lean_dec_ref(v_k_1606_);
lean_dec_ref(v_f_1596_);
return v___x_1611_;
}
}
else
{
lean_dec_ref(v_k_1606_);
lean_dec_ref(v_decl_1605_);
lean_dec_ref(v_f_1596_);
return v___x_1607_;
}
}
else
{
lean_dec_ref(v_k_1606_);
lean_dec_ref(v_decl_1605_);
lean_dec_ref(v_f_1596_);
return v___x_1607_;
}
}
case 2:
{
lean_object* v_k_1615_; 
v_k_1615_ = lean_ctor_get(v_a_1597_, 1);
lean_inc_ref(v_k_1615_);
lean_dec_ref(v_a_1597_);
v_a_1597_ = v_k_1615_;
goto _start;
}
case 4:
{
lean_object* v_cases_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1636_; 
v_cases_1617_ = lean_ctor_get(v_a_1597_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_a_1597_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1619_ = v_a_1597_;
v_isShared_1620_ = v_isSharedCheck_1636_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_cases_1617_);
lean_dec(v_a_1597_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1636_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_alts_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v_alts_1621_ = lean_ctor_get(v_cases_1617_, 3);
lean_inc_ref(v_alts_1621_);
lean_dec_ref(v_cases_1617_);
v___x_1622_ = lean_unsigned_to_nat(0u);
v___x_1623_ = lean_array_get_size(v_alts_1621_);
v___x_1624_ = lean_nat_dec_lt(v___x_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_dec_ref(v_alts_1621_);
lean_dec_ref(v_f_1596_);
v___x_1625_ = lean_box(v___x_1624_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set_tag(v___x_1619_, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1625_);
v___x_1627_ = v___x_1619_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
else
{
if (v___x_1624_ == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
lean_dec_ref(v_alts_1621_);
lean_dec_ref(v_f_1596_);
v___x_1629_ = lean_box(v___x_1624_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set_tag(v___x_1619_, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1629_);
v___x_1631_ = v___x_1619_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
else
{
size_t v___x_1633_; size_t v___x_1634_; lean_object* v___x_1635_; 
lean_del_object(v___x_1619_);
v___x_1633_ = ((size_t)0ULL);
v___x_1634_ = lean_usize_of_nat(v___x_1623_);
v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_1595_, v_f_1596_, v_alts_1621_, v___x_1633_, v___x_1634_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec_ref(v_alts_1621_);
return v___x_1635_;
}
}
}
}
case 7:
{
lean_object* v_k_1637_; 
v_k_1637_ = lean_ctor_get(v_a_1597_, 3);
lean_inc_ref(v_k_1637_);
lean_dec_ref(v_a_1597_);
v_a_1597_ = v_k_1637_;
goto _start;
}
case 8:
{
lean_object* v_k_1639_; 
v_k_1639_ = lean_ctor_get(v_a_1597_, 3);
lean_inc_ref(v_k_1639_);
lean_dec_ref(v_a_1597_);
v_a_1597_ = v_k_1639_;
goto _start;
}
case 9:
{
lean_object* v_k_1641_; 
v_k_1641_ = lean_ctor_get(v_a_1597_, 5);
lean_inc_ref(v_k_1641_);
lean_dec_ref(v_a_1597_);
v_a_1597_ = v_k_1641_;
goto _start;
}
case 10:
{
lean_object* v_k_1643_; 
v_k_1643_ = lean_ctor_get(v_a_1597_, 2);
lean_inc_ref(v_k_1643_);
lean_dec_ref(v_a_1597_);
v_a_1597_ = v_k_1643_;
goto _start;
}
case 11:
{
lean_object* v_k_1645_; 
v_k_1645_ = lean_ctor_get(v_a_1597_, 2);
lean_inc_ref(v_k_1645_);
lean_dec_ref(v_a_1597_);
v_a_1597_ = v_k_1645_;
goto _start;
}
case 12:
{
lean_object* v_k_1647_; 
v_k_1647_ = lean_ctor_get(v_a_1597_, 2);
lean_inc_ref(v_k_1647_);
lean_dec_ref(v_a_1597_);
v_a_1597_ = v_k_1647_;
goto _start;
}
case 13:
{
lean_object* v_k_1649_; 
v_k_1649_ = lean_ctor_get(v_a_1597_, 1);
lean_inc_ref(v_k_1649_);
lean_dec_ref(v_a_1597_);
v_a_1597_ = v_k_1649_;
goto _start;
}
default: 
{
uint8_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec_ref(v_a_1597_);
lean_dec_ref(v_f_1596_);
v___x_1651_ = 0;
v___x_1652_ = lean_box(v___x_1651_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
return v___x_1653_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(uint8_t v_pu_1654_, lean_object* v_f_1655_, lean_object* v_as_1656_, size_t v_i_1657_, size_t v_stop_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
uint8_t v___x_1664_; 
v___x_1664_ = lean_usize_dec_eq(v_i_1657_, v_stop_1658_);
if (v___x_1664_ == 0)
{
uint8_t v___x_1665_; lean_object* v___y_1667_; lean_object* v___x_1682_; 
v___x_1665_ = 1;
v___x_1682_ = lean_array_uget_borrowed(v_as_1656_, v_i_1657_);
switch(lean_obj_tag(v___x_1682_))
{
case 0:
{
lean_object* v_code_1683_; 
v_code_1683_ = lean_ctor_get(v___x_1682_, 2);
lean_inc_ref(v_code_1683_);
v___y_1667_ = v_code_1683_;
goto v___jp_1666_;
}
case 1:
{
lean_object* v_code_1684_; 
v_code_1684_ = lean_ctor_get(v___x_1682_, 1);
lean_inc_ref(v_code_1684_);
v___y_1667_ = v_code_1684_;
goto v___jp_1666_;
}
default: 
{
lean_object* v_code_1685_; 
v_code_1685_ = lean_ctor_get(v___x_1682_, 0);
lean_inc_ref(v_code_1685_);
v___y_1667_ = v_code_1685_;
goto v___jp_1666_;
}
}
v___jp_1666_:
{
lean_object* v___x_1668_; 
lean_inc_ref(v_f_1655_);
v___x_1668_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1654_, v_f_1655_, v___y_1667_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1681_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1681_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1681_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_unbox(v_a_1669_);
lean_dec(v_a_1669_);
if (v___x_1673_ == 0)
{
size_t v___x_1674_; size_t v___x_1675_; 
lean_del_object(v___x_1671_);
v___x_1674_ = ((size_t)1ULL);
v___x_1675_ = lean_usize_add(v_i_1657_, v___x_1674_);
v_i_1657_ = v___x_1675_;
goto _start;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
lean_dec_ref(v_f_1655_);
v___x_1677_ = lean_box(v___x_1665_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1677_);
v___x_1679_ = v___x_1671_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_dec_ref(v_f_1655_);
return v___x_1668_;
}
}
}
else
{
uint8_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec_ref(v_f_1655_);
v___x_1686_ = 0;
v___x_1687_ = lean_box(v___x_1686_);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0___boxed(lean_object* v_pu_1689_, lean_object* v_f_1690_, lean_object* v_as_1691_, lean_object* v_i_1692_, lean_object* v_stop_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
uint8_t v_pu_boxed_1699_; size_t v_i_boxed_1700_; size_t v_stop_boxed_1701_; lean_object* v_res_1702_; 
v_pu_boxed_1699_ = lean_unbox(v_pu_1689_);
v_i_boxed_1700_ = lean_unbox_usize(v_i_1692_);
lean_dec(v_i_1692_);
v_stop_boxed_1701_ = lean_unbox_usize(v_stop_1693_);
lean_dec(v_stop_1693_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_boxed_1699_, v_f_1690_, v_as_1691_, v_i_boxed_1700_, v_stop_boxed_1701_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec_ref(v_as_1691_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed(lean_object* v_pu_1703_, lean_object* v_f_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
uint8_t v_pu_boxed_1711_; lean_object* v_res_1712_; 
v_pu_boxed_1711_ = lean_unbox(v_pu_1703_);
v_res_1712_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_boxed_1711_, v_f_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(uint8_t v_pu_1713_, lean_object* v_f_1714_, lean_object* v_as_1715_, size_t v_i_1716_, size_t v_stop_1717_, lean_object* v_b_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_usize_dec_eq(v_i_1716_, v_stop_1717_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v_value_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1725_ = lean_array_uget_borrowed(v_as_1715_, v_i_1716_);
v_value_1726_ = lean_ctor_get(v___x_1725_, 1);
v___x_1727_ = lean_box(v_pu_1713_);
lean_inc_ref(v_f_1714_);
v___x_1728_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed), 8, 2);
lean_closure_set(v___x_1728_, 0, v___x_1727_);
lean_closure_set(v___x_1728_, 1, v_f_1714_);
lean_inc_ref(v_value_1726_);
v___x_1729_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1726_, v___x_1728_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v_a_1732_; uint8_t v___x_1736_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref(v___x_1729_);
v___x_1736_ = lean_unbox(v_a_1730_);
lean_dec(v_a_1730_);
if (v___x_1736_ == 0)
{
v_a_1732_ = v_b_1718_;
goto v___jp_1731_;
}
else
{
lean_object* v___x_1737_; 
lean_inc(v___x_1725_);
v___x_1737_ = lean_array_push(v_b_1718_, v___x_1725_);
v_a_1732_ = v___x_1737_;
goto v___jp_1731_;
}
v___jp_1731_:
{
size_t v___x_1733_; size_t v___x_1734_; 
v___x_1733_ = ((size_t)1ULL);
v___x_1734_ = lean_usize_add(v_i_1716_, v___x_1733_);
v_i_1716_ = v___x_1734_;
v_b_1718_ = v_a_1732_;
goto _start;
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
lean_dec_ref(v_b_1718_);
lean_dec_ref(v_f_1714_);
v_a_1738_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v___x_1729_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1729_);
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
else
{
lean_object* v___x_1746_; 
lean_dec_ref(v_f_1714_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_b_1718_);
return v___x_1746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0___boxed(lean_object* v_pu_1747_, lean_object* v_f_1748_, lean_object* v_as_1749_, lean_object* v_i_1750_, lean_object* v_stop_1751_, lean_object* v_b_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
uint8_t v_pu_boxed_1758_; size_t v_i_boxed_1759_; size_t v_stop_boxed_1760_; lean_object* v_res_1761_; 
v_pu_boxed_1758_ = lean_unbox(v_pu_1747_);
v_i_boxed_1759_ = lean_unbox_usize(v_i_1750_);
lean_dec(v_i_1750_);
v_stop_boxed_1760_ = lean_unbox_usize(v_stop_1751_);
lean_dec(v_stop_1751_);
v_res_1761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_boxed_1758_, v_f_1748_, v_as_1749_, v_i_boxed_1759_, v_stop_boxed_1760_, v_b_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec_ref(v_as_1749_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun(uint8_t v_pu_1762_, lean_object* v_f_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_array_get_size(v_a_1764_);
v___x_1772_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1773_ = lean_nat_dec_lt(v___x_1770_, v___x_1771_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_dec_ref(v_f_1763_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
return v___x_1774_;
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_nat_dec_le(v___x_1771_, v___x_1771_);
if (v___x_1775_ == 0)
{
if (v___x_1773_ == 0)
{
lean_object* v___x_1776_; 
lean_dec_ref(v_f_1763_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1772_);
return v___x_1776_;
}
else
{
size_t v___x_1777_; size_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = ((size_t)0ULL);
v___x_1778_ = lean_usize_of_nat(v___x_1771_);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1762_, v_f_1763_, v_a_1764_, v___x_1777_, v___x_1778_, v___x_1772_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
return v___x_1779_;
}
}
else
{
size_t v___x_1780_; size_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = lean_usize_of_nat(v___x_1771_);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1762_, v_f_1763_, v_a_1764_, v___x_1780_, v___x_1781_, v___x_1772_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_);
return v___x_1782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun___boxed(lean_object* v_pu_1783_, lean_object* v_f_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
uint8_t v_pu_boxed_1791_; lean_object* v_res_1792_; 
v_pu_boxed_1791_ = lean_unbox(v_pu_1783_);
v_res_1792_ = l_Lean_Compiler_LCNF_Probe_filterByFun(v_pu_boxed_1791_, v_f_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(uint8_t v_pu_1793_, lean_object* v_f_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
switch(lean_obj_tag(v_a_1795_))
{
case 0:
{
lean_object* v_k_1801_; 
v_k_1801_ = lean_ctor_get(v_a_1795_, 1);
lean_inc_ref(v_k_1801_);
lean_dec_ref(v_a_1795_);
v_a_1795_ = v_k_1801_;
goto _start;
}
case 1:
{
lean_object* v_decl_1803_; lean_object* v_k_1804_; lean_object* v_value_1805_; lean_object* v___x_1806_; 
v_decl_1803_ = lean_ctor_get(v_a_1795_, 0);
lean_inc_ref(v_decl_1803_);
v_k_1804_ = lean_ctor_get(v_a_1795_, 1);
lean_inc_ref(v_k_1804_);
lean_dec_ref(v_a_1795_);
v_value_1805_ = lean_ctor_get(v_decl_1803_, 4);
lean_inc_ref(v_value_1805_);
lean_dec_ref(v_decl_1803_);
lean_inc_ref(v_f_1794_);
v___x_1806_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1793_, v_f_1794_, v_value_1805_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; uint8_t v___x_1808_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
v___x_1808_ = lean_unbox(v_a_1807_);
lean_dec(v_a_1807_);
if (v___x_1808_ == 0)
{
lean_dec_ref(v___x_1806_);
v_a_1795_ = v_k_1804_;
goto _start;
}
else
{
lean_dec_ref(v_k_1804_);
lean_dec_ref(v_f_1794_);
return v___x_1806_;
}
}
else
{
lean_dec_ref(v_k_1804_);
lean_dec_ref(v_f_1794_);
return v___x_1806_;
}
}
case 2:
{
lean_object* v_decl_1810_; lean_object* v_k_1811_; lean_object* v___x_1812_; 
v_decl_1810_ = lean_ctor_get(v_a_1795_, 0);
lean_inc_ref_n(v_decl_1810_, 2);
v_k_1811_ = lean_ctor_get(v_a_1795_, 1);
lean_inc_ref(v_k_1811_);
lean_dec_ref(v_a_1795_);
lean_inc_ref(v_f_1794_);
lean_inc(v_a_1799_);
lean_inc_ref(v_a_1798_);
lean_inc(v_a_1797_);
lean_inc_ref(v_a_1796_);
v___x_1812_ = lean_apply_6(v_f_1794_, v_decl_1810_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, lean_box(0));
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; uint8_t v___x_1814_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
v___x_1814_ = lean_unbox(v_a_1813_);
lean_dec(v_a_1813_);
if (v___x_1814_ == 0)
{
lean_object* v_value_1815_; lean_object* v___x_1816_; 
lean_dec_ref(v___x_1812_);
v_value_1815_ = lean_ctor_get(v_decl_1810_, 4);
lean_inc_ref(v_value_1815_);
lean_dec_ref(v_decl_1810_);
lean_inc_ref(v_f_1794_);
v___x_1816_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1793_, v_f_1794_, v_value_1815_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; uint8_t v___x_1818_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
v___x_1818_ = lean_unbox(v_a_1817_);
lean_dec(v_a_1817_);
if (v___x_1818_ == 0)
{
lean_dec_ref(v___x_1816_);
v_a_1795_ = v_k_1811_;
goto _start;
}
else
{
lean_dec_ref(v_k_1811_);
lean_dec_ref(v_f_1794_);
return v___x_1816_;
}
}
else
{
lean_dec_ref(v_k_1811_);
lean_dec_ref(v_f_1794_);
return v___x_1816_;
}
}
else
{
lean_dec_ref(v_k_1811_);
lean_dec_ref(v_decl_1810_);
lean_dec_ref(v_f_1794_);
return v___x_1812_;
}
}
else
{
lean_dec_ref(v_k_1811_);
lean_dec_ref(v_decl_1810_);
lean_dec_ref(v_f_1794_);
return v___x_1812_;
}
}
case 4:
{
lean_object* v_cases_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1839_; 
v_cases_1820_ = lean_ctor_get(v_a_1795_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_a_1795_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1822_ = v_a_1795_;
v_isShared_1823_ = v_isSharedCheck_1839_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_cases_1820_);
lean_dec(v_a_1795_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1839_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_alts_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v_alts_1824_ = lean_ctor_get(v_cases_1820_, 3);
lean_inc_ref(v_alts_1824_);
lean_dec_ref(v_cases_1820_);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_array_get_size(v_alts_1824_);
v___x_1827_ = lean_nat_dec_lt(v___x_1825_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
lean_dec_ref(v_alts_1824_);
lean_dec_ref(v_f_1794_);
v___x_1828_ = lean_box(v___x_1827_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1828_);
v___x_1830_ = v___x_1822_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
else
{
if (v___x_1827_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
lean_dec_ref(v_alts_1824_);
lean_dec_ref(v_f_1794_);
v___x_1832_ = lean_box(v___x_1827_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1832_);
v___x_1834_ = v___x_1822_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
else
{
size_t v___x_1836_; size_t v___x_1837_; lean_object* v___x_1838_; 
lean_del_object(v___x_1822_);
v___x_1836_ = ((size_t)0ULL);
v___x_1837_ = lean_usize_of_nat(v___x_1826_);
v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_1793_, v_f_1794_, v_alts_1824_, v___x_1836_, v___x_1837_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec_ref(v_alts_1824_);
return v___x_1838_;
}
}
}
}
case 7:
{
lean_object* v_k_1840_; 
v_k_1840_ = lean_ctor_get(v_a_1795_, 3);
lean_inc_ref(v_k_1840_);
lean_dec_ref(v_a_1795_);
v_a_1795_ = v_k_1840_;
goto _start;
}
case 8:
{
lean_object* v_k_1842_; 
v_k_1842_ = lean_ctor_get(v_a_1795_, 3);
lean_inc_ref(v_k_1842_);
lean_dec_ref(v_a_1795_);
v_a_1795_ = v_k_1842_;
goto _start;
}
case 9:
{
lean_object* v_k_1844_; 
v_k_1844_ = lean_ctor_get(v_a_1795_, 5);
lean_inc_ref(v_k_1844_);
lean_dec_ref(v_a_1795_);
v_a_1795_ = v_k_1844_;
goto _start;
}
case 10:
{
lean_object* v_k_1846_; 
v_k_1846_ = lean_ctor_get(v_a_1795_, 2);
lean_inc_ref(v_k_1846_);
lean_dec_ref(v_a_1795_);
v_a_1795_ = v_k_1846_;
goto _start;
}
case 11:
{
lean_object* v_k_1848_; 
v_k_1848_ = lean_ctor_get(v_a_1795_, 2);
lean_inc_ref(v_k_1848_);
lean_dec_ref(v_a_1795_);
v_a_1795_ = v_k_1848_;
goto _start;
}
case 12:
{
lean_object* v_k_1850_; 
v_k_1850_ = lean_ctor_get(v_a_1795_, 2);
lean_inc_ref(v_k_1850_);
lean_dec_ref(v_a_1795_);
v_a_1795_ = v_k_1850_;
goto _start;
}
case 13:
{
lean_object* v_k_1852_; 
v_k_1852_ = lean_ctor_get(v_a_1795_, 1);
lean_inc_ref(v_k_1852_);
lean_dec_ref(v_a_1795_);
v_a_1795_ = v_k_1852_;
goto _start;
}
default: 
{
uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec_ref(v_a_1795_);
lean_dec_ref(v_f_1794_);
v___x_1854_ = 0;
v___x_1855_ = lean_box(v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(uint8_t v_pu_1857_, lean_object* v_f_1858_, lean_object* v_as_1859_, size_t v_i_1860_, size_t v_stop_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
uint8_t v___x_1867_; 
v___x_1867_ = lean_usize_dec_eq(v_i_1860_, v_stop_1861_);
if (v___x_1867_ == 0)
{
uint8_t v___x_1868_; lean_object* v___y_1870_; lean_object* v___x_1885_; 
v___x_1868_ = 1;
v___x_1885_ = lean_array_uget_borrowed(v_as_1859_, v_i_1860_);
switch(lean_obj_tag(v___x_1885_))
{
case 0:
{
lean_object* v_code_1886_; 
v_code_1886_ = lean_ctor_get(v___x_1885_, 2);
lean_inc_ref(v_code_1886_);
v___y_1870_ = v_code_1886_;
goto v___jp_1869_;
}
case 1:
{
lean_object* v_code_1887_; 
v_code_1887_ = lean_ctor_get(v___x_1885_, 1);
lean_inc_ref(v_code_1887_);
v___y_1870_ = v_code_1887_;
goto v___jp_1869_;
}
default: 
{
lean_object* v_code_1888_; 
v_code_1888_ = lean_ctor_get(v___x_1885_, 0);
lean_inc_ref(v_code_1888_);
v___y_1870_ = v_code_1888_;
goto v___jp_1869_;
}
}
v___jp_1869_:
{
lean_object* v___x_1871_; 
lean_inc_ref(v_f_1858_);
v___x_1871_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1857_, v_f_1858_, v___y_1870_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1884_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1884_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1884_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
uint8_t v___x_1876_; 
v___x_1876_ = lean_unbox(v_a_1872_);
lean_dec(v_a_1872_);
if (v___x_1876_ == 0)
{
size_t v___x_1877_; size_t v___x_1878_; 
lean_del_object(v___x_1874_);
v___x_1877_ = ((size_t)1ULL);
v___x_1878_ = lean_usize_add(v_i_1860_, v___x_1877_);
v_i_1860_ = v___x_1878_;
goto _start;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
lean_dec_ref(v_f_1858_);
v___x_1880_ = lean_box(v___x_1868_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1880_);
v___x_1882_ = v___x_1874_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_dec_ref(v_f_1858_);
return v___x_1871_;
}
}
}
else
{
uint8_t v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec_ref(v_f_1858_);
v___x_1889_ = 0;
v___x_1890_ = lean_box(v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0___boxed(lean_object* v_pu_1892_, lean_object* v_f_1893_, lean_object* v_as_1894_, lean_object* v_i_1895_, lean_object* v_stop_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
uint8_t v_pu_boxed_1902_; size_t v_i_boxed_1903_; size_t v_stop_boxed_1904_; lean_object* v_res_1905_; 
v_pu_boxed_1902_ = lean_unbox(v_pu_1892_);
v_i_boxed_1903_ = lean_unbox_usize(v_i_1895_);
lean_dec(v_i_1895_);
v_stop_boxed_1904_ = lean_unbox_usize(v_stop_1896_);
lean_dec(v_stop_1896_);
v_res_1905_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_boxed_1902_, v_f_1893_, v_as_1894_, v_i_boxed_1903_, v_stop_boxed_1904_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec_ref(v_as_1894_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed(lean_object* v_pu_1906_, lean_object* v_f_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
uint8_t v_pu_boxed_1914_; lean_object* v_res_1915_; 
v_pu_boxed_1914_ = lean_unbox(v_pu_1906_);
v_res_1915_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_boxed_1914_, v_f_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(uint8_t v_pu_1916_, lean_object* v_f_1917_, lean_object* v_as_1918_, size_t v_i_1919_, size_t v_stop_1920_, lean_object* v_b_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
uint8_t v___x_1927_; 
v___x_1927_ = lean_usize_dec_eq(v_i_1919_, v_stop_1920_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v_value_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1928_ = lean_array_uget_borrowed(v_as_1918_, v_i_1919_);
v_value_1929_ = lean_ctor_get(v___x_1928_, 1);
v___x_1930_ = lean_box(v_pu_1916_);
lean_inc_ref(v_f_1917_);
v___x_1931_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed), 8, 2);
lean_closure_set(v___x_1931_, 0, v___x_1930_);
lean_closure_set(v___x_1931_, 1, v_f_1917_);
lean_inc_ref(v_value_1929_);
v___x_1932_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1929_, v___x_1931_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v_a_1935_; uint8_t v___x_1939_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
v___x_1939_ = lean_unbox(v_a_1933_);
lean_dec(v_a_1933_);
if (v___x_1939_ == 0)
{
v_a_1935_ = v_b_1921_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1940_; 
lean_inc(v___x_1928_);
v___x_1940_ = lean_array_push(v_b_1921_, v___x_1928_);
v_a_1935_ = v___x_1940_;
goto v___jp_1934_;
}
v___jp_1934_:
{
size_t v___x_1936_; size_t v___x_1937_; 
v___x_1936_ = ((size_t)1ULL);
v___x_1937_ = lean_usize_add(v_i_1919_, v___x_1936_);
v_i_1919_ = v___x_1937_;
v_b_1921_ = v_a_1935_;
goto _start;
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v_b_1921_);
lean_dec_ref(v_f_1917_);
v_a_1941_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1932_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1932_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v___x_1949_; 
lean_dec_ref(v_f_1917_);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_b_1921_);
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0___boxed(lean_object* v_pu_1950_, lean_object* v_f_1951_, lean_object* v_as_1952_, lean_object* v_i_1953_, lean_object* v_stop_1954_, lean_object* v_b_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
uint8_t v_pu_boxed_1961_; size_t v_i_boxed_1962_; size_t v_stop_boxed_1963_; lean_object* v_res_1964_; 
v_pu_boxed_1961_ = lean_unbox(v_pu_1950_);
v_i_boxed_1962_ = lean_unbox_usize(v_i_1953_);
lean_dec(v_i_1953_);
v_stop_boxed_1963_ = lean_unbox_usize(v_stop_1954_);
lean_dec(v_stop_1954_);
v_res_1964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_boxed_1961_, v_f_1951_, v_as_1952_, v_i_boxed_1962_, v_stop_boxed_1963_, v_b_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec_ref(v_as_1952_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp(uint8_t v_pu_1965_, lean_object* v_f_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1973_ = lean_unsigned_to_nat(0u);
v___x_1974_ = lean_array_get_size(v_a_1967_);
v___x_1975_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1976_ = lean_nat_dec_lt(v___x_1973_, v___x_1974_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_dec_ref(v_f_1966_);
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
return v___x_1977_;
}
else
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_nat_dec_le(v___x_1974_, v___x_1974_);
if (v___x_1978_ == 0)
{
if (v___x_1976_ == 0)
{
lean_object* v___x_1979_; 
lean_dec_ref(v_f_1966_);
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1975_);
return v___x_1979_;
}
else
{
size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = lean_usize_of_nat(v___x_1974_);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_1965_, v_f_1966_, v_a_1967_, v___x_1980_, v___x_1981_, v___x_1975_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
return v___x_1982_;
}
}
else
{
size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = ((size_t)0ULL);
v___x_1984_ = lean_usize_of_nat(v___x_1974_);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_1965_, v_f_1966_, v_a_1967_, v___x_1983_, v___x_1984_, v___x_1975_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
return v___x_1985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp___boxed(lean_object* v_pu_1986_, lean_object* v_f_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
uint8_t v_pu_boxed_1994_; lean_object* v_res_1995_; 
v_pu_boxed_1994_ = lean_unbox(v_pu_1986_);
v_res_1995_ = l_Lean_Compiler_LCNF_Probe_filterByJp(v_pu_boxed_1994_, v_f_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec_ref(v_a_1988_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(uint8_t v_pu_1996_, lean_object* v_f_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
switch(lean_obj_tag(v_a_1998_))
{
case 0:
{
lean_object* v_k_2004_; 
v_k_2004_ = lean_ctor_get(v_a_1998_, 1);
lean_inc_ref(v_k_2004_);
lean_dec_ref(v_a_1998_);
v_a_1998_ = v_k_2004_;
goto _start;
}
case 1:
{
lean_object* v_decl_2006_; lean_object* v_k_2007_; lean_object* v___x_2008_; 
v_decl_2006_ = lean_ctor_get(v_a_1998_, 0);
lean_inc_ref_n(v_decl_2006_, 2);
v_k_2007_ = lean_ctor_get(v_a_1998_, 1);
lean_inc_ref(v_k_2007_);
lean_dec_ref(v_a_1998_);
lean_inc_ref(v_f_1997_);
lean_inc(v_a_2002_);
lean_inc_ref(v_a_2001_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
v___x_2008_ = lean_apply_6(v_f_1997_, v_decl_2006_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, lean_box(0));
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; uint8_t v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
v___x_2010_ = lean_unbox(v_a_2009_);
lean_dec(v_a_2009_);
if (v___x_2010_ == 0)
{
lean_object* v_value_2011_; lean_object* v___x_2012_; 
lean_dec_ref(v___x_2008_);
v_value_2011_ = lean_ctor_get(v_decl_2006_, 4);
lean_inc_ref(v_value_2011_);
lean_dec_ref(v_decl_2006_);
lean_inc_ref(v_f_1997_);
v___x_2012_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_1996_, v_f_1997_, v_value_2011_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; uint8_t v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
v___x_2014_ = lean_unbox(v_a_2013_);
lean_dec(v_a_2013_);
if (v___x_2014_ == 0)
{
lean_dec_ref(v___x_2012_);
v_a_1998_ = v_k_2007_;
goto _start;
}
else
{
lean_dec_ref(v_k_2007_);
lean_dec_ref(v_f_1997_);
return v___x_2012_;
}
}
else
{
lean_dec_ref(v_k_2007_);
lean_dec_ref(v_f_1997_);
return v___x_2012_;
}
}
else
{
lean_dec_ref(v_k_2007_);
lean_dec_ref(v_decl_2006_);
lean_dec_ref(v_f_1997_);
return v___x_2008_;
}
}
else
{
lean_dec_ref(v_k_2007_);
lean_dec_ref(v_decl_2006_);
lean_dec_ref(v_f_1997_);
return v___x_2008_;
}
}
case 2:
{
lean_object* v_decl_2016_; lean_object* v_k_2017_; lean_object* v___x_2018_; 
v_decl_2016_ = lean_ctor_get(v_a_1998_, 0);
lean_inc_ref_n(v_decl_2016_, 2);
v_k_2017_ = lean_ctor_get(v_a_1998_, 1);
lean_inc_ref(v_k_2017_);
lean_dec_ref(v_a_1998_);
lean_inc_ref(v_f_1997_);
lean_inc(v_a_2002_);
lean_inc_ref(v_a_2001_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
v___x_2018_ = lean_apply_6(v_f_1997_, v_decl_2016_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, lean_box(0));
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; uint8_t v___x_2020_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
v___x_2020_ = lean_unbox(v_a_2019_);
lean_dec(v_a_2019_);
if (v___x_2020_ == 0)
{
lean_object* v_value_2021_; lean_object* v___x_2022_; 
lean_dec_ref(v___x_2018_);
v_value_2021_ = lean_ctor_get(v_decl_2016_, 4);
lean_inc_ref(v_value_2021_);
lean_dec_ref(v_decl_2016_);
lean_inc_ref(v_f_1997_);
v___x_2022_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_1996_, v_f_1997_, v_value_2021_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; uint8_t v___x_2024_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
v___x_2024_ = lean_unbox(v_a_2023_);
lean_dec(v_a_2023_);
if (v___x_2024_ == 0)
{
lean_dec_ref(v___x_2022_);
v_a_1998_ = v_k_2017_;
goto _start;
}
else
{
lean_dec_ref(v_k_2017_);
lean_dec_ref(v_f_1997_);
return v___x_2022_;
}
}
else
{
lean_dec_ref(v_k_2017_);
lean_dec_ref(v_f_1997_);
return v___x_2022_;
}
}
else
{
lean_dec_ref(v_k_2017_);
lean_dec_ref(v_decl_2016_);
lean_dec_ref(v_f_1997_);
return v___x_2018_;
}
}
else
{
lean_dec_ref(v_k_2017_);
lean_dec_ref(v_decl_2016_);
lean_dec_ref(v_f_1997_);
return v___x_2018_;
}
}
case 4:
{
lean_object* v_cases_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2045_; 
v_cases_2026_ = lean_ctor_get(v_a_1998_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2028_ = v_a_1998_;
v_isShared_2029_ = v_isSharedCheck_2045_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_cases_2026_);
lean_dec(v_a_1998_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2045_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v_alts_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_alts_2030_ = lean_ctor_get(v_cases_2026_, 3);
lean_inc_ref(v_alts_2030_);
lean_dec_ref(v_cases_2026_);
v___x_2031_ = lean_unsigned_to_nat(0u);
v___x_2032_ = lean_array_get_size(v_alts_2030_);
v___x_2033_ = lean_nat_dec_lt(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
lean_dec_ref(v_alts_2030_);
lean_dec_ref(v_f_1997_);
v___x_2034_ = lean_box(v___x_2033_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2034_);
v___x_2036_ = v___x_2028_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
else
{
if (v___x_2033_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
lean_dec_ref(v_alts_2030_);
lean_dec_ref(v_f_1997_);
v___x_2038_ = lean_box(v___x_2033_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2038_);
v___x_2040_ = v___x_2028_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
else
{
size_t v___x_2042_; size_t v___x_2043_; lean_object* v___x_2044_; 
lean_del_object(v___x_2028_);
v___x_2042_ = ((size_t)0ULL);
v___x_2043_ = lean_usize_of_nat(v___x_2032_);
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_1996_, v_f_1997_, v_alts_2030_, v___x_2042_, v___x_2043_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
lean_dec_ref(v_alts_2030_);
return v___x_2044_;
}
}
}
}
case 7:
{
lean_object* v_k_2046_; 
v_k_2046_ = lean_ctor_get(v_a_1998_, 3);
lean_inc_ref(v_k_2046_);
lean_dec_ref(v_a_1998_);
v_a_1998_ = v_k_2046_;
goto _start;
}
case 8:
{
lean_object* v_k_2048_; 
v_k_2048_ = lean_ctor_get(v_a_1998_, 3);
lean_inc_ref(v_k_2048_);
lean_dec_ref(v_a_1998_);
v_a_1998_ = v_k_2048_;
goto _start;
}
case 9:
{
lean_object* v_k_2050_; 
v_k_2050_ = lean_ctor_get(v_a_1998_, 5);
lean_inc_ref(v_k_2050_);
lean_dec_ref(v_a_1998_);
v_a_1998_ = v_k_2050_;
goto _start;
}
case 10:
{
lean_object* v_k_2052_; 
v_k_2052_ = lean_ctor_get(v_a_1998_, 2);
lean_inc_ref(v_k_2052_);
lean_dec_ref(v_a_1998_);
v_a_1998_ = v_k_2052_;
goto _start;
}
case 11:
{
lean_object* v_k_2054_; 
v_k_2054_ = lean_ctor_get(v_a_1998_, 2);
lean_inc_ref(v_k_2054_);
lean_dec_ref(v_a_1998_);
v_a_1998_ = v_k_2054_;
goto _start;
}
case 12:
{
lean_object* v_k_2056_; 
v_k_2056_ = lean_ctor_get(v_a_1998_, 2);
lean_inc_ref(v_k_2056_);
lean_dec_ref(v_a_1998_);
v_a_1998_ = v_k_2056_;
goto _start;
}
case 13:
{
lean_object* v_k_2058_; 
v_k_2058_ = lean_ctor_get(v_a_1998_, 1);
lean_inc_ref(v_k_2058_);
lean_dec_ref(v_a_1998_);
v_a_1998_ = v_k_2058_;
goto _start;
}
default: 
{
uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec_ref(v_a_1998_);
lean_dec_ref(v_f_1997_);
v___x_2060_ = 0;
v___x_2061_ = lean_box(v___x_2060_);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(uint8_t v_pu_2063_, lean_object* v_f_2064_, lean_object* v_as_2065_, size_t v_i_2066_, size_t v_stop_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
uint8_t v___x_2073_; 
v___x_2073_ = lean_usize_dec_eq(v_i_2066_, v_stop_2067_);
if (v___x_2073_ == 0)
{
uint8_t v___x_2074_; lean_object* v___y_2076_; lean_object* v___x_2091_; 
v___x_2074_ = 1;
v___x_2091_ = lean_array_uget_borrowed(v_as_2065_, v_i_2066_);
switch(lean_obj_tag(v___x_2091_))
{
case 0:
{
lean_object* v_code_2092_; 
v_code_2092_ = lean_ctor_get(v___x_2091_, 2);
lean_inc_ref(v_code_2092_);
v___y_2076_ = v_code_2092_;
goto v___jp_2075_;
}
case 1:
{
lean_object* v_code_2093_; 
v_code_2093_ = lean_ctor_get(v___x_2091_, 1);
lean_inc_ref(v_code_2093_);
v___y_2076_ = v_code_2093_;
goto v___jp_2075_;
}
default: 
{
lean_object* v_code_2094_; 
v_code_2094_ = lean_ctor_get(v___x_2091_, 0);
lean_inc_ref(v_code_2094_);
v___y_2076_ = v_code_2094_;
goto v___jp_2075_;
}
}
v___jp_2075_:
{
lean_object* v___x_2077_; 
lean_inc_ref(v_f_2064_);
v___x_2077_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2063_, v_f_2064_, v___y_2076_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2090_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2090_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2090_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_unbox(v_a_2078_);
lean_dec(v_a_2078_);
if (v___x_2082_ == 0)
{
size_t v___x_2083_; size_t v___x_2084_; 
lean_del_object(v___x_2080_);
v___x_2083_ = ((size_t)1ULL);
v___x_2084_ = lean_usize_add(v_i_2066_, v___x_2083_);
v_i_2066_ = v___x_2084_;
goto _start;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_dec_ref(v_f_2064_);
v___x_2086_ = lean_box(v___x_2074_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2086_);
v___x_2088_ = v___x_2080_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
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
else
{
lean_dec_ref(v_f_2064_);
return v___x_2077_;
}
}
}
else
{
uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_dec_ref(v_f_2064_);
v___x_2095_ = 0;
v___x_2096_ = lean_box(v___x_2095_);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0___boxed(lean_object* v_pu_2098_, lean_object* v_f_2099_, lean_object* v_as_2100_, lean_object* v_i_2101_, lean_object* v_stop_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v_pu_boxed_2108_; size_t v_i_boxed_2109_; size_t v_stop_boxed_2110_; lean_object* v_res_2111_; 
v_pu_boxed_2108_ = lean_unbox(v_pu_2098_);
v_i_boxed_2109_ = lean_unbox_usize(v_i_2101_);
lean_dec(v_i_2101_);
v_stop_boxed_2110_ = lean_unbox_usize(v_stop_2102_);
lean_dec(v_stop_2102_);
v_res_2111_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_boxed_2108_, v_f_2099_, v_as_2100_, v_i_boxed_2109_, v_stop_boxed_2110_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec_ref(v_as_2100_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed(lean_object* v_pu_2112_, lean_object* v_f_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
uint8_t v_pu_boxed_2120_; lean_object* v_res_2121_; 
v_pu_boxed_2120_ = lean_unbox(v_pu_2112_);
v_res_2121_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_boxed_2120_, v_f_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(uint8_t v_pu_2122_, lean_object* v_f_2123_, lean_object* v_as_2124_, size_t v_i_2125_, size_t v_stop_2126_, lean_object* v_b_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_usize_dec_eq(v_i_2125_, v_stop_2126_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; lean_object* v_value_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2134_ = lean_array_uget_borrowed(v_as_2124_, v_i_2125_);
v_value_2135_ = lean_ctor_get(v___x_2134_, 1);
v___x_2136_ = lean_box(v_pu_2122_);
lean_inc_ref(v_f_2123_);
v___x_2137_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed), 8, 2);
lean_closure_set(v___x_2137_, 0, v___x_2136_);
lean_closure_set(v___x_2137_, 1, v_f_2123_);
lean_inc_ref(v_value_2135_);
v___x_2138_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2135_, v___x_2137_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v_a_2141_; uint8_t v___x_2145_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2138_);
v___x_2145_ = lean_unbox(v_a_2139_);
lean_dec(v_a_2139_);
if (v___x_2145_ == 0)
{
v_a_2141_ = v_b_2127_;
goto v___jp_2140_;
}
else
{
lean_object* v___x_2146_; 
lean_inc(v___x_2134_);
v___x_2146_ = lean_array_push(v_b_2127_, v___x_2134_);
v_a_2141_ = v___x_2146_;
goto v___jp_2140_;
}
v___jp_2140_:
{
size_t v___x_2142_; size_t v___x_2143_; 
v___x_2142_ = ((size_t)1ULL);
v___x_2143_ = lean_usize_add(v_i_2125_, v___x_2142_);
v_i_2125_ = v___x_2143_;
v_b_2127_ = v_a_2141_;
goto _start;
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v_b_2127_);
lean_dec_ref(v_f_2123_);
v_a_2147_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2138_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2138_);
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
else
{
lean_object* v___x_2155_; 
lean_dec_ref(v_f_2123_);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_b_2127_);
return v___x_2155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0___boxed(lean_object* v_pu_2156_, lean_object* v_f_2157_, lean_object* v_as_2158_, lean_object* v_i_2159_, lean_object* v_stop_2160_, lean_object* v_b_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v_pu_boxed_2167_; size_t v_i_boxed_2168_; size_t v_stop_boxed_2169_; lean_object* v_res_2170_; 
v_pu_boxed_2167_ = lean_unbox(v_pu_2156_);
v_i_boxed_2168_ = lean_unbox_usize(v_i_2159_);
lean_dec(v_i_2159_);
v_stop_boxed_2169_ = lean_unbox_usize(v_stop_2160_);
lean_dec(v_stop_2160_);
v_res_2170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_boxed_2167_, v_f_2157_, v_as_2158_, v_i_boxed_2168_, v_stop_boxed_2169_, v_b_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec_ref(v_as_2158_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl(uint8_t v_pu_2171_, lean_object* v_f_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = lean_array_get_size(v_a_2173_);
v___x_2181_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2182_ = lean_nat_dec_lt(v___x_2179_, v___x_2180_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
lean_dec_ref(v_f_2172_);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
return v___x_2183_;
}
else
{
uint8_t v___x_2184_; 
v___x_2184_ = lean_nat_dec_le(v___x_2180_, v___x_2180_);
if (v___x_2184_ == 0)
{
if (v___x_2182_ == 0)
{
lean_object* v___x_2185_; 
lean_dec_ref(v_f_2172_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2181_);
return v___x_2185_;
}
else
{
size_t v___x_2186_; size_t v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = ((size_t)0ULL);
v___x_2187_ = lean_usize_of_nat(v___x_2180_);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2171_, v_f_2172_, v_a_2173_, v___x_2186_, v___x_2187_, v___x_2181_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
return v___x_2188_;
}
}
else
{
size_t v___x_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = ((size_t)0ULL);
v___x_2190_ = lean_usize_of_nat(v___x_2180_);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2171_, v_f_2172_, v_a_2173_, v___x_2189_, v___x_2190_, v___x_2181_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
return v___x_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl___boxed(lean_object* v_pu_2192_, lean_object* v_f_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
uint8_t v_pu_boxed_2200_; lean_object* v_res_2201_; 
v_pu_boxed_2200_ = lean_unbox(v_pu_2192_);
v_res_2201_ = l_Lean_Compiler_LCNF_Probe_filterByFunDecl(v_pu_boxed_2200_, v_f_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec_ref(v_a_2194_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(uint8_t v_pu_2202_, lean_object* v_f_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
switch(lean_obj_tag(v_a_2204_))
{
case 0:
{
lean_object* v_k_2210_; 
v_k_2210_ = lean_ctor_get(v_a_2204_, 1);
lean_inc_ref(v_k_2210_);
lean_dec_ref(v_a_2204_);
v_a_2204_ = v_k_2210_;
goto _start;
}
case 1:
{
lean_object* v_decl_2212_; lean_object* v_k_2213_; lean_object* v_value_2214_; lean_object* v___x_2215_; 
v_decl_2212_ = lean_ctor_get(v_a_2204_, 0);
lean_inc_ref(v_decl_2212_);
v_k_2213_ = lean_ctor_get(v_a_2204_, 1);
lean_inc_ref(v_k_2213_);
lean_dec_ref(v_a_2204_);
v_value_2214_ = lean_ctor_get(v_decl_2212_, 4);
lean_inc_ref(v_value_2214_);
lean_dec_ref(v_decl_2212_);
lean_inc_ref(v_f_2203_);
v___x_2215_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2202_, v_f_2203_, v_value_2214_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; uint8_t v___x_2217_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
v___x_2217_ = lean_unbox(v_a_2216_);
lean_dec(v_a_2216_);
if (v___x_2217_ == 0)
{
lean_dec_ref(v___x_2215_);
v_a_2204_ = v_k_2213_;
goto _start;
}
else
{
lean_dec_ref(v_k_2213_);
lean_dec_ref(v_f_2203_);
return v___x_2215_;
}
}
else
{
lean_dec_ref(v_k_2213_);
lean_dec_ref(v_f_2203_);
return v___x_2215_;
}
}
case 2:
{
lean_object* v_decl_2219_; lean_object* v_k_2220_; lean_object* v_value_2221_; lean_object* v___x_2222_; 
v_decl_2219_ = lean_ctor_get(v_a_2204_, 0);
lean_inc_ref(v_decl_2219_);
v_k_2220_ = lean_ctor_get(v_a_2204_, 1);
lean_inc_ref(v_k_2220_);
lean_dec_ref(v_a_2204_);
v_value_2221_ = lean_ctor_get(v_decl_2219_, 4);
lean_inc_ref(v_value_2221_);
lean_dec_ref(v_decl_2219_);
lean_inc_ref(v_f_2203_);
v___x_2222_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2202_, v_f_2203_, v_value_2221_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; uint8_t v___x_2224_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
v___x_2224_ = lean_unbox(v_a_2223_);
lean_dec(v_a_2223_);
if (v___x_2224_ == 0)
{
lean_dec_ref(v___x_2222_);
v_a_2204_ = v_k_2220_;
goto _start;
}
else
{
lean_dec_ref(v_k_2220_);
lean_dec_ref(v_f_2203_);
return v___x_2222_;
}
}
else
{
lean_dec_ref(v_k_2220_);
lean_dec_ref(v_f_2203_);
return v___x_2222_;
}
}
case 4:
{
lean_object* v_cases_2226_; lean_object* v___x_2227_; 
v_cases_2226_ = lean_ctor_get(v_a_2204_, 0);
lean_inc_ref_n(v_cases_2226_, 2);
lean_dec_ref(v_a_2204_);
lean_inc_ref(v_f_2203_);
lean_inc(v_a_2208_);
lean_inc_ref(v_a_2207_);
lean_inc(v_a_2206_);
lean_inc_ref(v_a_2205_);
v___x_2227_ = lean_apply_6(v_f_2203_, v_cases_2226_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, lean_box(0));
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; uint8_t v___x_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
v___x_2229_ = lean_unbox(v_a_2228_);
lean_dec(v_a_2228_);
if (v___x_2229_ == 0)
{
lean_object* v_alts_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v_alts_2230_ = lean_ctor_get(v_cases_2226_, 3);
lean_inc_ref(v_alts_2230_);
lean_dec_ref(v_cases_2226_);
v___x_2231_ = lean_unsigned_to_nat(0u);
v___x_2232_ = lean_array_get_size(v_alts_2230_);
v___x_2233_ = lean_nat_dec_lt(v___x_2231_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_dec_ref(v_alts_2230_);
lean_dec_ref(v_f_2203_);
return v___x_2227_;
}
else
{
if (v___x_2233_ == 0)
{
lean_dec_ref(v_alts_2230_);
lean_dec_ref(v_f_2203_);
return v___x_2227_;
}
else
{
size_t v___x_2234_; size_t v___x_2235_; lean_object* v___x_2236_; 
lean_dec_ref(v___x_2227_);
v___x_2234_ = ((size_t)0ULL);
v___x_2235_ = lean_usize_of_nat(v___x_2232_);
v___x_2236_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_2202_, v_f_2203_, v_alts_2230_, v___x_2234_, v___x_2235_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
lean_dec_ref(v_alts_2230_);
return v___x_2236_;
}
}
}
else
{
lean_dec_ref(v_cases_2226_);
lean_dec_ref(v_f_2203_);
return v___x_2227_;
}
}
else
{
lean_dec_ref(v_cases_2226_);
lean_dec_ref(v_f_2203_);
return v___x_2227_;
}
}
case 7:
{
lean_object* v_k_2237_; 
v_k_2237_ = lean_ctor_get(v_a_2204_, 3);
lean_inc_ref(v_k_2237_);
lean_dec_ref(v_a_2204_);
v_a_2204_ = v_k_2237_;
goto _start;
}
case 8:
{
lean_object* v_k_2239_; 
v_k_2239_ = lean_ctor_get(v_a_2204_, 3);
lean_inc_ref(v_k_2239_);
lean_dec_ref(v_a_2204_);
v_a_2204_ = v_k_2239_;
goto _start;
}
case 9:
{
lean_object* v_k_2241_; 
v_k_2241_ = lean_ctor_get(v_a_2204_, 5);
lean_inc_ref(v_k_2241_);
lean_dec_ref(v_a_2204_);
v_a_2204_ = v_k_2241_;
goto _start;
}
case 10:
{
lean_object* v_k_2243_; 
v_k_2243_ = lean_ctor_get(v_a_2204_, 2);
lean_inc_ref(v_k_2243_);
lean_dec_ref(v_a_2204_);
v_a_2204_ = v_k_2243_;
goto _start;
}
case 11:
{
lean_object* v_k_2245_; 
v_k_2245_ = lean_ctor_get(v_a_2204_, 2);
lean_inc_ref(v_k_2245_);
lean_dec_ref(v_a_2204_);
v_a_2204_ = v_k_2245_;
goto _start;
}
case 12:
{
lean_object* v_k_2247_; 
v_k_2247_ = lean_ctor_get(v_a_2204_, 2);
lean_inc_ref(v_k_2247_);
lean_dec_ref(v_a_2204_);
v_a_2204_ = v_k_2247_;
goto _start;
}
case 13:
{
lean_object* v_k_2249_; 
v_k_2249_ = lean_ctor_get(v_a_2204_, 1);
lean_inc_ref(v_k_2249_);
lean_dec_ref(v_a_2204_);
v_a_2204_ = v_k_2249_;
goto _start;
}
default: 
{
uint8_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec_ref(v_a_2204_);
lean_dec_ref(v_f_2203_);
v___x_2251_ = 0;
v___x_2252_ = lean_box(v___x_2251_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(uint8_t v_pu_2254_, lean_object* v_f_2255_, lean_object* v_as_2256_, size_t v_i_2257_, size_t v_stop_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
uint8_t v___x_2264_; 
v___x_2264_ = lean_usize_dec_eq(v_i_2257_, v_stop_2258_);
if (v___x_2264_ == 0)
{
uint8_t v___x_2265_; lean_object* v___y_2267_; lean_object* v___x_2282_; 
v___x_2265_ = 1;
v___x_2282_ = lean_array_uget_borrowed(v_as_2256_, v_i_2257_);
switch(lean_obj_tag(v___x_2282_))
{
case 0:
{
lean_object* v_code_2283_; 
v_code_2283_ = lean_ctor_get(v___x_2282_, 2);
lean_inc_ref(v_code_2283_);
v___y_2267_ = v_code_2283_;
goto v___jp_2266_;
}
case 1:
{
lean_object* v_code_2284_; 
v_code_2284_ = lean_ctor_get(v___x_2282_, 1);
lean_inc_ref(v_code_2284_);
v___y_2267_ = v_code_2284_;
goto v___jp_2266_;
}
default: 
{
lean_object* v_code_2285_; 
v_code_2285_ = lean_ctor_get(v___x_2282_, 0);
lean_inc_ref(v_code_2285_);
v___y_2267_ = v_code_2285_;
goto v___jp_2266_;
}
}
v___jp_2266_:
{
lean_object* v___x_2268_; 
lean_inc_ref(v_f_2255_);
v___x_2268_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2254_, v_f_2255_, v___y_2267_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2281_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2281_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2281_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
uint8_t v___x_2273_; 
v___x_2273_ = lean_unbox(v_a_2269_);
lean_dec(v_a_2269_);
if (v___x_2273_ == 0)
{
size_t v___x_2274_; size_t v___x_2275_; 
lean_del_object(v___x_2271_);
v___x_2274_ = ((size_t)1ULL);
v___x_2275_ = lean_usize_add(v_i_2257_, v___x_2274_);
v_i_2257_ = v___x_2275_;
goto _start;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2279_; 
lean_dec_ref(v_f_2255_);
v___x_2277_ = lean_box(v___x_2265_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2277_);
v___x_2279_ = v___x_2271_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_dec_ref(v_f_2255_);
return v___x_2268_;
}
}
}
else
{
uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec_ref(v_f_2255_);
v___x_2286_ = 0;
v___x_2287_ = lean_box(v___x_2286_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0___boxed(lean_object* v_pu_2289_, lean_object* v_f_2290_, lean_object* v_as_2291_, lean_object* v_i_2292_, lean_object* v_stop_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v_pu_boxed_2299_; size_t v_i_boxed_2300_; size_t v_stop_boxed_2301_; lean_object* v_res_2302_; 
v_pu_boxed_2299_ = lean_unbox(v_pu_2289_);
v_i_boxed_2300_ = lean_unbox_usize(v_i_2292_);
lean_dec(v_i_2292_);
v_stop_boxed_2301_ = lean_unbox_usize(v_stop_2293_);
lean_dec(v_stop_2293_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_boxed_2299_, v_f_2290_, v_as_2291_, v_i_boxed_2300_, v_stop_boxed_2301_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v_as_2291_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed(lean_object* v_pu_2303_, lean_object* v_f_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
uint8_t v_pu_boxed_2311_; lean_object* v_res_2312_; 
v_pu_boxed_2311_ = lean_unbox(v_pu_2303_);
v_res_2312_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_boxed_2311_, v_f_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(uint8_t v_pu_2313_, lean_object* v_f_2314_, lean_object* v_as_2315_, size_t v_i_2316_, size_t v_stop_2317_, lean_object* v_b_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
uint8_t v___x_2324_; 
v___x_2324_ = lean_usize_dec_eq(v_i_2316_, v_stop_2317_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v_value_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2325_ = lean_array_uget_borrowed(v_as_2315_, v_i_2316_);
v_value_2326_ = lean_ctor_get(v___x_2325_, 1);
v___x_2327_ = lean_box(v_pu_2313_);
lean_inc_ref(v_f_2314_);
v___x_2328_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed), 8, 2);
lean_closure_set(v___x_2328_, 0, v___x_2327_);
lean_closure_set(v___x_2328_, 1, v_f_2314_);
lean_inc_ref(v_value_2326_);
v___x_2329_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2326_, v___x_2328_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v_a_2332_; uint8_t v___x_2336_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2336_ = lean_unbox(v_a_2330_);
lean_dec(v_a_2330_);
if (v___x_2336_ == 0)
{
v_a_2332_ = v_b_2318_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2337_; 
lean_inc(v___x_2325_);
v___x_2337_ = lean_array_push(v_b_2318_, v___x_2325_);
v_a_2332_ = v___x_2337_;
goto v___jp_2331_;
}
v___jp_2331_:
{
size_t v___x_2333_; size_t v___x_2334_; 
v___x_2333_ = ((size_t)1ULL);
v___x_2334_ = lean_usize_add(v_i_2316_, v___x_2333_);
v_i_2316_ = v___x_2334_;
v_b_2318_ = v_a_2332_;
goto _start;
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v_b_2318_);
lean_dec_ref(v_f_2314_);
v_a_2338_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2329_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2329_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v___x_2346_; 
lean_dec_ref(v_f_2314_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v_b_2318_);
return v___x_2346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0___boxed(lean_object* v_pu_2347_, lean_object* v_f_2348_, lean_object* v_as_2349_, lean_object* v_i_2350_, lean_object* v_stop_2351_, lean_object* v_b_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
uint8_t v_pu_boxed_2358_; size_t v_i_boxed_2359_; size_t v_stop_boxed_2360_; lean_object* v_res_2361_; 
v_pu_boxed_2358_ = lean_unbox(v_pu_2347_);
v_i_boxed_2359_ = lean_unbox_usize(v_i_2350_);
lean_dec(v_i_2350_);
v_stop_boxed_2360_ = lean_unbox_usize(v_stop_2351_);
lean_dec(v_stop_2351_);
v_res_2361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_boxed_2358_, v_f_2348_, v_as_2349_, v_i_boxed_2359_, v_stop_boxed_2360_, v_b_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec_ref(v_as_2349_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases(uint8_t v_pu_2362_, lean_object* v_f_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2370_ = lean_unsigned_to_nat(0u);
v___x_2371_ = lean_array_get_size(v_a_2364_);
v___x_2372_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2373_ = lean_nat_dec_lt(v___x_2370_, v___x_2371_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; 
lean_dec_ref(v_f_2363_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
return v___x_2374_;
}
else
{
uint8_t v___x_2375_; 
v___x_2375_ = lean_nat_dec_le(v___x_2371_, v___x_2371_);
if (v___x_2375_ == 0)
{
if (v___x_2373_ == 0)
{
lean_object* v___x_2376_; 
lean_dec_ref(v_f_2363_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2372_);
return v___x_2376_;
}
else
{
size_t v___x_2377_; size_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = ((size_t)0ULL);
v___x_2378_ = lean_usize_of_nat(v___x_2371_);
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2362_, v_f_2363_, v_a_2364_, v___x_2377_, v___x_2378_, v___x_2372_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
return v___x_2379_;
}
}
else
{
size_t v___x_2380_; size_t v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = ((size_t)0ULL);
v___x_2381_ = lean_usize_of_nat(v___x_2371_);
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2362_, v_f_2363_, v_a_2364_, v___x_2380_, v___x_2381_, v___x_2372_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
return v___x_2382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases___boxed(lean_object* v_pu_2383_, lean_object* v_f_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
uint8_t v_pu_boxed_2391_; lean_object* v_res_2392_; 
v_pu_boxed_2391_ = lean_unbox(v_pu_2383_);
v_res_2392_ = l_Lean_Compiler_LCNF_Probe_filterByCases(v_pu_boxed_2391_, v_f_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec_ref(v_a_2385_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(uint8_t v_pu_2393_, lean_object* v_f_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
switch(lean_obj_tag(v_a_2395_))
{
case 0:
{
lean_object* v_k_2401_; 
v_k_2401_ = lean_ctor_get(v_a_2395_, 1);
lean_inc_ref(v_k_2401_);
lean_dec_ref(v_a_2395_);
v_a_2395_ = v_k_2401_;
goto _start;
}
case 1:
{
lean_object* v_decl_2403_; lean_object* v_k_2404_; lean_object* v_value_2405_; lean_object* v___x_2406_; 
v_decl_2403_ = lean_ctor_get(v_a_2395_, 0);
lean_inc_ref(v_decl_2403_);
v_k_2404_ = lean_ctor_get(v_a_2395_, 1);
lean_inc_ref(v_k_2404_);
lean_dec_ref(v_a_2395_);
v_value_2405_ = lean_ctor_get(v_decl_2403_, 4);
lean_inc_ref(v_value_2405_);
lean_dec_ref(v_decl_2403_);
lean_inc_ref(v_f_2394_);
v___x_2406_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2393_, v_f_2394_, v_value_2405_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; uint8_t v___x_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
v___x_2408_ = lean_unbox(v_a_2407_);
lean_dec(v_a_2407_);
if (v___x_2408_ == 0)
{
lean_dec_ref(v___x_2406_);
v_a_2395_ = v_k_2404_;
goto _start;
}
else
{
lean_dec_ref(v_k_2404_);
lean_dec_ref(v_f_2394_);
return v___x_2406_;
}
}
else
{
lean_dec_ref(v_k_2404_);
lean_dec_ref(v_f_2394_);
return v___x_2406_;
}
}
case 2:
{
lean_object* v_decl_2410_; lean_object* v_k_2411_; lean_object* v_value_2412_; lean_object* v___x_2413_; 
v_decl_2410_ = lean_ctor_get(v_a_2395_, 0);
lean_inc_ref(v_decl_2410_);
v_k_2411_ = lean_ctor_get(v_a_2395_, 1);
lean_inc_ref(v_k_2411_);
lean_dec_ref(v_a_2395_);
v_value_2412_ = lean_ctor_get(v_decl_2410_, 4);
lean_inc_ref(v_value_2412_);
lean_dec_ref(v_decl_2410_);
lean_inc_ref(v_f_2394_);
v___x_2413_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2393_, v_f_2394_, v_value_2412_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; uint8_t v___x_2415_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
v___x_2415_ = lean_unbox(v_a_2414_);
lean_dec(v_a_2414_);
if (v___x_2415_ == 0)
{
lean_dec_ref(v___x_2413_);
v_a_2395_ = v_k_2411_;
goto _start;
}
else
{
lean_dec_ref(v_k_2411_);
lean_dec_ref(v_f_2394_);
return v___x_2413_;
}
}
else
{
lean_dec_ref(v_k_2411_);
lean_dec_ref(v_f_2394_);
return v___x_2413_;
}
}
case 3:
{
lean_object* v_fvarId_2417_; lean_object* v_args_2418_; lean_object* v___x_2419_; 
v_fvarId_2417_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_fvarId_2417_);
v_args_2418_ = lean_ctor_get(v_a_2395_, 1);
lean_inc_ref(v_args_2418_);
lean_dec_ref(v_a_2395_);
lean_inc(v_a_2399_);
lean_inc_ref(v_a_2398_);
lean_inc(v_a_2397_);
lean_inc_ref(v_a_2396_);
v___x_2419_ = lean_apply_7(v_f_2394_, v_fvarId_2417_, v_args_2418_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, lean_box(0));
return v___x_2419_;
}
case 4:
{
lean_object* v_cases_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2439_; 
v_cases_2420_ = lean_ctor_get(v_a_2395_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_a_2395_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2422_ = v_a_2395_;
v_isShared_2423_ = v_isSharedCheck_2439_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_cases_2420_);
lean_dec(v_a_2395_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2439_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_alts_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v_alts_2424_ = lean_ctor_get(v_cases_2420_, 3);
lean_inc_ref(v_alts_2424_);
lean_dec_ref(v_cases_2420_);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_array_get_size(v_alts_2424_);
v___x_2427_ = lean_nat_dec_lt(v___x_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2430_; 
lean_dec_ref(v_alts_2424_);
lean_dec_ref(v_f_2394_);
v___x_2428_ = lean_box(v___x_2427_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2428_);
v___x_2430_ = v___x_2422_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
else
{
if (v___x_2427_ == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2434_; 
lean_dec_ref(v_alts_2424_);
lean_dec_ref(v_f_2394_);
v___x_2432_ = lean_box(v___x_2427_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set_tag(v___x_2422_, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2432_);
v___x_2434_ = v___x_2422_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
else
{
size_t v___x_2436_; size_t v___x_2437_; lean_object* v___x_2438_; 
lean_del_object(v___x_2422_);
v___x_2436_ = ((size_t)0ULL);
v___x_2437_ = lean_usize_of_nat(v___x_2426_);
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_2393_, v_f_2394_, v_alts_2424_, v___x_2436_, v___x_2437_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
lean_dec_ref(v_alts_2424_);
return v___x_2438_;
}
}
}
}
case 7:
{
lean_object* v_k_2440_; 
v_k_2440_ = lean_ctor_get(v_a_2395_, 3);
lean_inc_ref(v_k_2440_);
lean_dec_ref(v_a_2395_);
v_a_2395_ = v_k_2440_;
goto _start;
}
case 8:
{
lean_object* v_k_2442_; 
v_k_2442_ = lean_ctor_get(v_a_2395_, 3);
lean_inc_ref(v_k_2442_);
lean_dec_ref(v_a_2395_);
v_a_2395_ = v_k_2442_;
goto _start;
}
case 9:
{
lean_object* v_k_2444_; 
v_k_2444_ = lean_ctor_get(v_a_2395_, 5);
lean_inc_ref(v_k_2444_);
lean_dec_ref(v_a_2395_);
v_a_2395_ = v_k_2444_;
goto _start;
}
case 10:
{
lean_object* v_k_2446_; 
v_k_2446_ = lean_ctor_get(v_a_2395_, 2);
lean_inc_ref(v_k_2446_);
lean_dec_ref(v_a_2395_);
v_a_2395_ = v_k_2446_;
goto _start;
}
case 11:
{
lean_object* v_k_2448_; 
v_k_2448_ = lean_ctor_get(v_a_2395_, 2);
lean_inc_ref(v_k_2448_);
lean_dec_ref(v_a_2395_);
v_a_2395_ = v_k_2448_;
goto _start;
}
case 12:
{
lean_object* v_k_2450_; 
v_k_2450_ = lean_ctor_get(v_a_2395_, 2);
lean_inc_ref(v_k_2450_);
lean_dec_ref(v_a_2395_);
v_a_2395_ = v_k_2450_;
goto _start;
}
case 13:
{
lean_object* v_k_2452_; 
v_k_2452_ = lean_ctor_get(v_a_2395_, 1);
lean_inc_ref(v_k_2452_);
lean_dec_ref(v_a_2395_);
v_a_2395_ = v_k_2452_;
goto _start;
}
default: 
{
uint8_t v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
lean_dec_ref(v_a_2395_);
lean_dec_ref(v_f_2394_);
v___x_2454_ = 0;
v___x_2455_ = lean_box(v___x_2454_);
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(uint8_t v_pu_2457_, lean_object* v_f_2458_, lean_object* v_as_2459_, size_t v_i_2460_, size_t v_stop_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
uint8_t v___x_2467_; 
v___x_2467_ = lean_usize_dec_eq(v_i_2460_, v_stop_2461_);
if (v___x_2467_ == 0)
{
uint8_t v___x_2468_; lean_object* v___y_2470_; lean_object* v___x_2485_; 
v___x_2468_ = 1;
v___x_2485_ = lean_array_uget_borrowed(v_as_2459_, v_i_2460_);
switch(lean_obj_tag(v___x_2485_))
{
case 0:
{
lean_object* v_code_2486_; 
v_code_2486_ = lean_ctor_get(v___x_2485_, 2);
lean_inc_ref(v_code_2486_);
v___y_2470_ = v_code_2486_;
goto v___jp_2469_;
}
case 1:
{
lean_object* v_code_2487_; 
v_code_2487_ = lean_ctor_get(v___x_2485_, 1);
lean_inc_ref(v_code_2487_);
v___y_2470_ = v_code_2487_;
goto v___jp_2469_;
}
default: 
{
lean_object* v_code_2488_; 
v_code_2488_ = lean_ctor_get(v___x_2485_, 0);
lean_inc_ref(v_code_2488_);
v___y_2470_ = v_code_2488_;
goto v___jp_2469_;
}
}
v___jp_2469_:
{
lean_object* v___x_2471_; 
lean_inc_ref(v_f_2458_);
v___x_2471_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2457_, v_f_2458_, v___y_2470_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2484_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2484_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2484_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_unbox(v_a_2472_);
lean_dec(v_a_2472_);
if (v___x_2476_ == 0)
{
size_t v___x_2477_; size_t v___x_2478_; 
lean_del_object(v___x_2474_);
v___x_2477_ = ((size_t)1ULL);
v___x_2478_ = lean_usize_add(v_i_2460_, v___x_2477_);
v_i_2460_ = v___x_2478_;
goto _start;
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
lean_dec_ref(v_f_2458_);
v___x_2480_ = lean_box(v___x_2468_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2480_);
v___x_2482_ = v___x_2474_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_dec_ref(v_f_2458_);
return v___x_2471_;
}
}
}
else
{
uint8_t v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec_ref(v_f_2458_);
v___x_2489_ = 0;
v___x_2490_ = lean_box(v___x_2489_);
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
return v___x_2491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0___boxed(lean_object* v_pu_2492_, lean_object* v_f_2493_, lean_object* v_as_2494_, lean_object* v_i_2495_, lean_object* v_stop_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v_pu_boxed_2502_; size_t v_i_boxed_2503_; size_t v_stop_boxed_2504_; lean_object* v_res_2505_; 
v_pu_boxed_2502_ = lean_unbox(v_pu_2492_);
v_i_boxed_2503_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_stop_boxed_2504_ = lean_unbox_usize(v_stop_2496_);
lean_dec(v_stop_2496_);
v_res_2505_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_boxed_2502_, v_f_2493_, v_as_2494_, v_i_boxed_2503_, v_stop_boxed_2504_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec_ref(v_as_2494_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed(lean_object* v_pu_2506_, lean_object* v_f_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
uint8_t v_pu_boxed_2514_; lean_object* v_res_2515_; 
v_pu_boxed_2514_ = lean_unbox(v_pu_2506_);
v_res_2515_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_boxed_2514_, v_f_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(uint8_t v_pu_2516_, lean_object* v_f_2517_, lean_object* v_as_2518_, size_t v_i_2519_, size_t v_stop_2520_, lean_object* v_b_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_usize_dec_eq(v_i_2519_, v_stop_2520_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v_value_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2528_ = lean_array_uget_borrowed(v_as_2518_, v_i_2519_);
v_value_2529_ = lean_ctor_get(v___x_2528_, 1);
v___x_2530_ = lean_box(v_pu_2516_);
lean_inc_ref(v_f_2517_);
v___x_2531_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed), 8, 2);
lean_closure_set(v___x_2531_, 0, v___x_2530_);
lean_closure_set(v___x_2531_, 1, v_f_2517_);
lean_inc_ref(v_value_2529_);
v___x_2532_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2529_, v___x_2531_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v_a_2535_; uint8_t v___x_2539_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref(v___x_2532_);
v___x_2539_ = lean_unbox(v_a_2533_);
lean_dec(v_a_2533_);
if (v___x_2539_ == 0)
{
v_a_2535_ = v_b_2521_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2540_; 
lean_inc(v___x_2528_);
v___x_2540_ = lean_array_push(v_b_2521_, v___x_2528_);
v_a_2535_ = v___x_2540_;
goto v___jp_2534_;
}
v___jp_2534_:
{
size_t v___x_2536_; size_t v___x_2537_; 
v___x_2536_ = ((size_t)1ULL);
v___x_2537_ = lean_usize_add(v_i_2519_, v___x_2536_);
v_i_2519_ = v___x_2537_;
v_b_2521_ = v_a_2535_;
goto _start;
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec_ref(v_b_2521_);
lean_dec_ref(v_f_2517_);
v_a_2541_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2532_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2532_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v___x_2549_; 
lean_dec_ref(v_f_2517_);
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_b_2521_);
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0___boxed(lean_object* v_pu_2550_, lean_object* v_f_2551_, lean_object* v_as_2552_, lean_object* v_i_2553_, lean_object* v_stop_2554_, lean_object* v_b_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
uint8_t v_pu_boxed_2561_; size_t v_i_boxed_2562_; size_t v_stop_boxed_2563_; lean_object* v_res_2564_; 
v_pu_boxed_2561_ = lean_unbox(v_pu_2550_);
v_i_boxed_2562_ = lean_unbox_usize(v_i_2553_);
lean_dec(v_i_2553_);
v_stop_boxed_2563_ = lean_unbox_usize(v_stop_2554_);
lean_dec(v_stop_2554_);
v_res_2564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_boxed_2561_, v_f_2551_, v_as_2552_, v_i_boxed_2562_, v_stop_boxed_2563_, v_b_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec_ref(v_as_2552_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp(uint8_t v_pu_2565_, lean_object* v_f_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = lean_array_get_size(v_a_2567_);
v___x_2575_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2576_ = lean_nat_dec_lt(v___x_2573_, v___x_2574_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; 
lean_dec_ref(v_f_2566_);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
return v___x_2577_;
}
else
{
uint8_t v___x_2578_; 
v___x_2578_ = lean_nat_dec_le(v___x_2574_, v___x_2574_);
if (v___x_2578_ == 0)
{
if (v___x_2576_ == 0)
{
lean_object* v___x_2579_; 
lean_dec_ref(v_f_2566_);
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2575_);
return v___x_2579_;
}
else
{
size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = ((size_t)0ULL);
v___x_2581_ = lean_usize_of_nat(v___x_2574_);
v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2565_, v_f_2566_, v_a_2567_, v___x_2580_, v___x_2581_, v___x_2575_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
return v___x_2582_;
}
}
else
{
size_t v___x_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = ((size_t)0ULL);
v___x_2584_ = lean_usize_of_nat(v___x_2574_);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2565_, v_f_2566_, v_a_2567_, v___x_2583_, v___x_2584_, v___x_2575_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
return v___x_2585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp___boxed(lean_object* v_pu_2586_, lean_object* v_f_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
uint8_t v_pu_boxed_2594_; lean_object* v_res_2595_; 
v_pu_boxed_2594_ = lean_unbox(v_pu_2586_);
v_res_2595_ = l_Lean_Compiler_LCNF_Probe_filterByJmp(v_pu_boxed_2594_, v_f_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec_ref(v_a_2588_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(uint8_t v_pu_2596_, lean_object* v_f_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
switch(lean_obj_tag(v_a_2598_))
{
case 0:
{
lean_object* v_k_2604_; 
v_k_2604_ = lean_ctor_get(v_a_2598_, 1);
lean_inc_ref(v_k_2604_);
lean_dec_ref(v_a_2598_);
v_a_2598_ = v_k_2604_;
goto _start;
}
case 1:
{
lean_object* v_decl_2606_; lean_object* v_k_2607_; lean_object* v_value_2608_; lean_object* v___x_2609_; 
v_decl_2606_ = lean_ctor_get(v_a_2598_, 0);
lean_inc_ref(v_decl_2606_);
v_k_2607_ = lean_ctor_get(v_a_2598_, 1);
lean_inc_ref(v_k_2607_);
lean_dec_ref(v_a_2598_);
v_value_2608_ = lean_ctor_get(v_decl_2606_, 4);
lean_inc_ref(v_value_2608_);
lean_dec_ref(v_decl_2606_);
lean_inc_ref(v_f_2597_);
v___x_2609_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2596_, v_f_2597_, v_value_2608_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; uint8_t v___x_2611_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
v___x_2611_ = lean_unbox(v_a_2610_);
lean_dec(v_a_2610_);
if (v___x_2611_ == 0)
{
lean_dec_ref(v___x_2609_);
v_a_2598_ = v_k_2607_;
goto _start;
}
else
{
lean_dec_ref(v_k_2607_);
lean_dec_ref(v_f_2597_);
return v___x_2609_;
}
}
else
{
lean_dec_ref(v_k_2607_);
lean_dec_ref(v_f_2597_);
return v___x_2609_;
}
}
case 2:
{
lean_object* v_decl_2613_; lean_object* v_k_2614_; lean_object* v_value_2615_; lean_object* v___x_2616_; 
v_decl_2613_ = lean_ctor_get(v_a_2598_, 0);
lean_inc_ref(v_decl_2613_);
v_k_2614_ = lean_ctor_get(v_a_2598_, 1);
lean_inc_ref(v_k_2614_);
lean_dec_ref(v_a_2598_);
v_value_2615_ = lean_ctor_get(v_decl_2613_, 4);
lean_inc_ref(v_value_2615_);
lean_dec_ref(v_decl_2613_);
lean_inc_ref(v_f_2597_);
v___x_2616_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2596_, v_f_2597_, v_value_2615_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; uint8_t v___x_2618_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
v___x_2618_ = lean_unbox(v_a_2617_);
lean_dec(v_a_2617_);
if (v___x_2618_ == 0)
{
lean_dec_ref(v___x_2616_);
v_a_2598_ = v_k_2614_;
goto _start;
}
else
{
lean_dec_ref(v_k_2614_);
lean_dec_ref(v_f_2597_);
return v___x_2616_;
}
}
else
{
lean_dec_ref(v_k_2614_);
lean_dec_ref(v_f_2597_);
return v___x_2616_;
}
}
case 4:
{
lean_object* v_cases_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2639_; 
v_cases_2620_ = lean_ctor_get(v_a_2598_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_a_2598_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2622_ = v_a_2598_;
v_isShared_2623_ = v_isSharedCheck_2639_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_cases_2620_);
lean_dec(v_a_2598_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2639_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v_alts_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v_alts_2624_ = lean_ctor_get(v_cases_2620_, 3);
lean_inc_ref(v_alts_2624_);
lean_dec_ref(v_cases_2620_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = lean_array_get_size(v_alts_2624_);
v___x_2627_ = lean_nat_dec_lt(v___x_2625_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2630_; 
lean_dec_ref(v_alts_2624_);
lean_dec_ref(v_f_2597_);
v___x_2628_ = lean_box(v___x_2627_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2628_);
v___x_2630_ = v___x_2622_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
else
{
if (v___x_2627_ == 0)
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
lean_dec_ref(v_alts_2624_);
lean_dec_ref(v_f_2597_);
v___x_2632_ = lean_box(v___x_2627_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2632_);
v___x_2634_ = v___x_2622_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
else
{
size_t v___x_2636_; size_t v___x_2637_; lean_object* v___x_2638_; 
lean_del_object(v___x_2622_);
v___x_2636_ = ((size_t)0ULL);
v___x_2637_ = lean_usize_of_nat(v___x_2626_);
v___x_2638_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_2596_, v_f_2597_, v_alts_2624_, v___x_2636_, v___x_2637_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
lean_dec_ref(v_alts_2624_);
return v___x_2638_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2640_; lean_object* v___x_2641_; 
v_fvarId_2640_ = lean_ctor_get(v_a_2598_, 0);
lean_inc(v_fvarId_2640_);
lean_dec_ref(v_a_2598_);
lean_inc(v_a_2602_);
lean_inc_ref(v_a_2601_);
lean_inc(v_a_2600_);
lean_inc_ref(v_a_2599_);
v___x_2641_ = lean_apply_6(v_f_2597_, v_fvarId_2640_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, lean_box(0));
return v___x_2641_;
}
case 7:
{
lean_object* v_k_2642_; 
v_k_2642_ = lean_ctor_get(v_a_2598_, 3);
lean_inc_ref(v_k_2642_);
lean_dec_ref(v_a_2598_);
v_a_2598_ = v_k_2642_;
goto _start;
}
case 8:
{
lean_object* v_k_2644_; 
v_k_2644_ = lean_ctor_get(v_a_2598_, 3);
lean_inc_ref(v_k_2644_);
lean_dec_ref(v_a_2598_);
v_a_2598_ = v_k_2644_;
goto _start;
}
case 9:
{
lean_object* v_k_2646_; 
v_k_2646_ = lean_ctor_get(v_a_2598_, 5);
lean_inc_ref(v_k_2646_);
lean_dec_ref(v_a_2598_);
v_a_2598_ = v_k_2646_;
goto _start;
}
case 10:
{
lean_object* v_k_2648_; 
v_k_2648_ = lean_ctor_get(v_a_2598_, 2);
lean_inc_ref(v_k_2648_);
lean_dec_ref(v_a_2598_);
v_a_2598_ = v_k_2648_;
goto _start;
}
case 11:
{
lean_object* v_k_2650_; 
v_k_2650_ = lean_ctor_get(v_a_2598_, 2);
lean_inc_ref(v_k_2650_);
lean_dec_ref(v_a_2598_);
v_a_2598_ = v_k_2650_;
goto _start;
}
case 12:
{
lean_object* v_k_2652_; 
v_k_2652_ = lean_ctor_get(v_a_2598_, 2);
lean_inc_ref(v_k_2652_);
lean_dec_ref(v_a_2598_);
v_a_2598_ = v_k_2652_;
goto _start;
}
case 13:
{
lean_object* v_k_2654_; 
v_k_2654_ = lean_ctor_get(v_a_2598_, 1);
lean_inc_ref(v_k_2654_);
lean_dec_ref(v_a_2598_);
v_a_2598_ = v_k_2654_;
goto _start;
}
default: 
{
uint8_t v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_dec_ref(v_a_2598_);
lean_dec_ref(v_f_2597_);
v___x_2656_ = 0;
v___x_2657_ = lean_box(v___x_2656_);
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
return v___x_2658_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(uint8_t v_pu_2659_, lean_object* v_f_2660_, lean_object* v_as_2661_, size_t v_i_2662_, size_t v_stop_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
uint8_t v___x_2669_; 
v___x_2669_ = lean_usize_dec_eq(v_i_2662_, v_stop_2663_);
if (v___x_2669_ == 0)
{
uint8_t v___x_2670_; lean_object* v___y_2672_; lean_object* v___x_2687_; 
v___x_2670_ = 1;
v___x_2687_ = lean_array_uget_borrowed(v_as_2661_, v_i_2662_);
switch(lean_obj_tag(v___x_2687_))
{
case 0:
{
lean_object* v_code_2688_; 
v_code_2688_ = lean_ctor_get(v___x_2687_, 2);
lean_inc_ref(v_code_2688_);
v___y_2672_ = v_code_2688_;
goto v___jp_2671_;
}
case 1:
{
lean_object* v_code_2689_; 
v_code_2689_ = lean_ctor_get(v___x_2687_, 1);
lean_inc_ref(v_code_2689_);
v___y_2672_ = v_code_2689_;
goto v___jp_2671_;
}
default: 
{
lean_object* v_code_2690_; 
v_code_2690_ = lean_ctor_get(v___x_2687_, 0);
lean_inc_ref(v_code_2690_);
v___y_2672_ = v_code_2690_;
goto v___jp_2671_;
}
}
v___jp_2671_:
{
lean_object* v___x_2673_; 
lean_inc_ref(v_f_2660_);
v___x_2673_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2659_, v_f_2660_, v___y_2672_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2686_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2676_ = v___x_2673_;
v_isShared_2677_ = v_isSharedCheck_2686_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2686_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_unbox(v_a_2674_);
lean_dec(v_a_2674_);
if (v___x_2678_ == 0)
{
size_t v___x_2679_; size_t v___x_2680_; 
lean_del_object(v___x_2676_);
v___x_2679_ = ((size_t)1ULL);
v___x_2680_ = lean_usize_add(v_i_2662_, v___x_2679_);
v_i_2662_ = v___x_2680_;
goto _start;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_dec_ref(v_f_2660_);
v___x_2682_ = lean_box(v___x_2670_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2682_);
v___x_2684_ = v___x_2676_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_dec_ref(v_f_2660_);
return v___x_2673_;
}
}
}
else
{
uint8_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec_ref(v_f_2660_);
v___x_2691_ = 0;
v___x_2692_ = lean_box(v___x_2691_);
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
return v___x_2693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0___boxed(lean_object* v_pu_2694_, lean_object* v_f_2695_, lean_object* v_as_2696_, lean_object* v_i_2697_, lean_object* v_stop_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
uint8_t v_pu_boxed_2704_; size_t v_i_boxed_2705_; size_t v_stop_boxed_2706_; lean_object* v_res_2707_; 
v_pu_boxed_2704_ = lean_unbox(v_pu_2694_);
v_i_boxed_2705_ = lean_unbox_usize(v_i_2697_);
lean_dec(v_i_2697_);
v_stop_boxed_2706_ = lean_unbox_usize(v_stop_2698_);
lean_dec(v_stop_2698_);
v_res_2707_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_boxed_2704_, v_f_2695_, v_as_2696_, v_i_boxed_2705_, v_stop_boxed_2706_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec_ref(v_as_2696_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed(lean_object* v_pu_2708_, lean_object* v_f_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
uint8_t v_pu_boxed_2716_; lean_object* v_res_2717_; 
v_pu_boxed_2716_ = lean_unbox(v_pu_2708_);
v_res_2717_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_boxed_2716_, v_f_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(uint8_t v_pu_2718_, lean_object* v_f_2719_, lean_object* v_as_2720_, size_t v_i_2721_, size_t v_stop_2722_, lean_object* v_b_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
uint8_t v___x_2729_; 
v___x_2729_ = lean_usize_dec_eq(v_i_2721_, v_stop_2722_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; lean_object* v_value_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2730_ = lean_array_uget_borrowed(v_as_2720_, v_i_2721_);
v_value_2731_ = lean_ctor_get(v___x_2730_, 1);
v___x_2732_ = lean_box(v_pu_2718_);
lean_inc_ref(v_f_2719_);
v___x_2733_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed), 8, 2);
lean_closure_set(v___x_2733_, 0, v___x_2732_);
lean_closure_set(v___x_2733_, 1, v_f_2719_);
lean_inc_ref(v_value_2731_);
v___x_2734_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2731_, v___x_2733_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v_a_2737_; uint8_t v___x_2741_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref(v___x_2734_);
v___x_2741_ = lean_unbox(v_a_2735_);
lean_dec(v_a_2735_);
if (v___x_2741_ == 0)
{
v_a_2737_ = v_b_2723_;
goto v___jp_2736_;
}
else
{
lean_object* v___x_2742_; 
lean_inc(v___x_2730_);
v___x_2742_ = lean_array_push(v_b_2723_, v___x_2730_);
v_a_2737_ = v___x_2742_;
goto v___jp_2736_;
}
v___jp_2736_:
{
size_t v___x_2738_; size_t v___x_2739_; 
v___x_2738_ = ((size_t)1ULL);
v___x_2739_ = lean_usize_add(v_i_2721_, v___x_2738_);
v_i_2721_ = v___x_2739_;
v_b_2723_ = v_a_2737_;
goto _start;
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v_b_2723_);
lean_dec_ref(v_f_2719_);
v_a_2743_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2734_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2734_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v___x_2751_; 
lean_dec_ref(v_f_2719_);
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v_b_2723_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0___boxed(lean_object* v_pu_2752_, lean_object* v_f_2753_, lean_object* v_as_2754_, lean_object* v_i_2755_, lean_object* v_stop_2756_, lean_object* v_b_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
uint8_t v_pu_boxed_2763_; size_t v_i_boxed_2764_; size_t v_stop_boxed_2765_; lean_object* v_res_2766_; 
v_pu_boxed_2763_ = lean_unbox(v_pu_2752_);
v_i_boxed_2764_ = lean_unbox_usize(v_i_2755_);
lean_dec(v_i_2755_);
v_stop_boxed_2765_ = lean_unbox_usize(v_stop_2756_);
lean_dec(v_stop_2756_);
v_res_2766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_boxed_2763_, v_f_2753_, v_as_2754_, v_i_boxed_2764_, v_stop_boxed_2765_, v_b_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec_ref(v_as_2754_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn(uint8_t v_pu_2767_, lean_object* v_f_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2775_ = lean_unsigned_to_nat(0u);
v___x_2776_ = lean_array_get_size(v_a_2769_);
v___x_2777_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2778_ = lean_nat_dec_lt(v___x_2775_, v___x_2776_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; 
lean_dec_ref(v_f_2768_);
v___x_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
return v___x_2779_;
}
else
{
uint8_t v___x_2780_; 
v___x_2780_ = lean_nat_dec_le(v___x_2776_, v___x_2776_);
if (v___x_2780_ == 0)
{
if (v___x_2778_ == 0)
{
lean_object* v___x_2781_; 
lean_dec_ref(v_f_2768_);
v___x_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2777_);
return v___x_2781_;
}
else
{
size_t v___x_2782_; size_t v___x_2783_; lean_object* v___x_2784_; 
v___x_2782_ = ((size_t)0ULL);
v___x_2783_ = lean_usize_of_nat(v___x_2776_);
v___x_2784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2767_, v_f_2768_, v_a_2769_, v___x_2782_, v___x_2783_, v___x_2777_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
return v___x_2784_;
}
}
else
{
size_t v___x_2785_; size_t v___x_2786_; lean_object* v___x_2787_; 
v___x_2785_ = ((size_t)0ULL);
v___x_2786_ = lean_usize_of_nat(v___x_2776_);
v___x_2787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2767_, v_f_2768_, v_a_2769_, v___x_2785_, v___x_2786_, v___x_2777_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
return v___x_2787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn___boxed(lean_object* v_pu_2788_, lean_object* v_f_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_){
_start:
{
uint8_t v_pu_boxed_2796_; lean_object* v_res_2797_; 
v_pu_boxed_2796_ = lean_unbox(v_pu_2788_);
v_res_2797_ = l_Lean_Compiler_LCNF_Probe_filterByReturn(v_pu_boxed_2796_, v_f_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
lean_dec_ref(v_a_2790_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(uint8_t v_pu_2798_, lean_object* v_f_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
switch(lean_obj_tag(v_a_2800_))
{
case 0:
{
lean_object* v_k_2806_; 
v_k_2806_ = lean_ctor_get(v_a_2800_, 1);
lean_inc_ref(v_k_2806_);
lean_dec_ref(v_a_2800_);
v_a_2800_ = v_k_2806_;
goto _start;
}
case 1:
{
lean_object* v_decl_2808_; lean_object* v_k_2809_; lean_object* v_value_2810_; lean_object* v___x_2811_; 
v_decl_2808_ = lean_ctor_get(v_a_2800_, 0);
lean_inc_ref(v_decl_2808_);
v_k_2809_ = lean_ctor_get(v_a_2800_, 1);
lean_inc_ref(v_k_2809_);
lean_dec_ref(v_a_2800_);
v_value_2810_ = lean_ctor_get(v_decl_2808_, 4);
lean_inc_ref(v_value_2810_);
lean_dec_ref(v_decl_2808_);
lean_inc_ref(v_f_2799_);
v___x_2811_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2798_, v_f_2799_, v_value_2810_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; uint8_t v___x_2813_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
v___x_2813_ = lean_unbox(v_a_2812_);
lean_dec(v_a_2812_);
if (v___x_2813_ == 0)
{
lean_dec_ref(v___x_2811_);
v_a_2800_ = v_k_2809_;
goto _start;
}
else
{
lean_dec_ref(v_k_2809_);
lean_dec_ref(v_f_2799_);
return v___x_2811_;
}
}
else
{
lean_dec_ref(v_k_2809_);
lean_dec_ref(v_f_2799_);
return v___x_2811_;
}
}
case 2:
{
lean_object* v_decl_2815_; lean_object* v_k_2816_; lean_object* v_value_2817_; lean_object* v___x_2818_; 
v_decl_2815_ = lean_ctor_get(v_a_2800_, 0);
lean_inc_ref(v_decl_2815_);
v_k_2816_ = lean_ctor_get(v_a_2800_, 1);
lean_inc_ref(v_k_2816_);
lean_dec_ref(v_a_2800_);
v_value_2817_ = lean_ctor_get(v_decl_2815_, 4);
lean_inc_ref(v_value_2817_);
lean_dec_ref(v_decl_2815_);
lean_inc_ref(v_f_2799_);
v___x_2818_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2798_, v_f_2799_, v_value_2817_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; uint8_t v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
v___x_2820_ = lean_unbox(v_a_2819_);
lean_dec(v_a_2819_);
if (v___x_2820_ == 0)
{
lean_dec_ref(v___x_2818_);
v_a_2800_ = v_k_2816_;
goto _start;
}
else
{
lean_dec_ref(v_k_2816_);
lean_dec_ref(v_f_2799_);
return v___x_2818_;
}
}
else
{
lean_dec_ref(v_k_2816_);
lean_dec_ref(v_f_2799_);
return v___x_2818_;
}
}
case 4:
{
lean_object* v_cases_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2841_; 
v_cases_2822_ = lean_ctor_get(v_a_2800_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_a_2800_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2824_ = v_a_2800_;
v_isShared_2825_ = v_isSharedCheck_2841_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_cases_2822_);
lean_dec(v_a_2800_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2841_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v_alts_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; 
v_alts_2826_ = lean_ctor_get(v_cases_2822_, 3);
lean_inc_ref(v_alts_2826_);
lean_dec_ref(v_cases_2822_);
v___x_2827_ = lean_unsigned_to_nat(0u);
v___x_2828_ = lean_array_get_size(v_alts_2826_);
v___x_2829_ = lean_nat_dec_lt(v___x_2827_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2832_; 
lean_dec_ref(v_alts_2826_);
lean_dec_ref(v_f_2799_);
v___x_2830_ = lean_box(v___x_2829_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set_tag(v___x_2824_, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2830_);
v___x_2832_ = v___x_2824_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
else
{
if (v___x_2829_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2836_; 
lean_dec_ref(v_alts_2826_);
lean_dec_ref(v_f_2799_);
v___x_2834_ = lean_box(v___x_2829_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set_tag(v___x_2824_, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2834_);
v___x_2836_ = v___x_2824_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
else
{
size_t v___x_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
lean_del_object(v___x_2824_);
v___x_2838_ = ((size_t)0ULL);
v___x_2839_ = lean_usize_of_nat(v___x_2828_);
v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_2798_, v_f_2799_, v_alts_2826_, v___x_2838_, v___x_2839_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
lean_dec_ref(v_alts_2826_);
return v___x_2840_;
}
}
}
}
case 6:
{
lean_object* v_type_2842_; lean_object* v___x_2843_; 
v_type_2842_ = lean_ctor_get(v_a_2800_, 0);
lean_inc_ref(v_type_2842_);
lean_dec_ref(v_a_2800_);
lean_inc(v_a_2804_);
lean_inc_ref(v_a_2803_);
lean_inc(v_a_2802_);
lean_inc_ref(v_a_2801_);
v___x_2843_ = lean_apply_6(v_f_2799_, v_type_2842_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, lean_box(0));
return v___x_2843_;
}
case 7:
{
lean_object* v_k_2844_; 
v_k_2844_ = lean_ctor_get(v_a_2800_, 3);
lean_inc_ref(v_k_2844_);
lean_dec_ref(v_a_2800_);
v_a_2800_ = v_k_2844_;
goto _start;
}
case 8:
{
lean_object* v_k_2846_; 
v_k_2846_ = lean_ctor_get(v_a_2800_, 3);
lean_inc_ref(v_k_2846_);
lean_dec_ref(v_a_2800_);
v_a_2800_ = v_k_2846_;
goto _start;
}
case 9:
{
lean_object* v_k_2848_; 
v_k_2848_ = lean_ctor_get(v_a_2800_, 5);
lean_inc_ref(v_k_2848_);
lean_dec_ref(v_a_2800_);
v_a_2800_ = v_k_2848_;
goto _start;
}
case 10:
{
lean_object* v_k_2850_; 
v_k_2850_ = lean_ctor_get(v_a_2800_, 2);
lean_inc_ref(v_k_2850_);
lean_dec_ref(v_a_2800_);
v_a_2800_ = v_k_2850_;
goto _start;
}
case 11:
{
lean_object* v_k_2852_; 
v_k_2852_ = lean_ctor_get(v_a_2800_, 2);
lean_inc_ref(v_k_2852_);
lean_dec_ref(v_a_2800_);
v_a_2800_ = v_k_2852_;
goto _start;
}
case 12:
{
lean_object* v_k_2854_; 
v_k_2854_ = lean_ctor_get(v_a_2800_, 2);
lean_inc_ref(v_k_2854_);
lean_dec_ref(v_a_2800_);
v_a_2800_ = v_k_2854_;
goto _start;
}
case 13:
{
lean_object* v_k_2856_; 
v_k_2856_ = lean_ctor_get(v_a_2800_, 1);
lean_inc_ref(v_k_2856_);
lean_dec_ref(v_a_2800_);
v_a_2800_ = v_k_2856_;
goto _start;
}
default: 
{
uint8_t v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_dec_ref(v_a_2800_);
lean_dec_ref(v_f_2799_);
v___x_2858_ = 0;
v___x_2859_ = lean_box(v___x_2858_);
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(uint8_t v_pu_2861_, lean_object* v_f_2862_, lean_object* v_as_2863_, size_t v_i_2864_, size_t v_stop_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_usize_dec_eq(v_i_2864_, v_stop_2865_);
if (v___x_2871_ == 0)
{
uint8_t v___x_2872_; lean_object* v___y_2874_; lean_object* v___x_2889_; 
v___x_2872_ = 1;
v___x_2889_ = lean_array_uget_borrowed(v_as_2863_, v_i_2864_);
switch(lean_obj_tag(v___x_2889_))
{
case 0:
{
lean_object* v_code_2890_; 
v_code_2890_ = lean_ctor_get(v___x_2889_, 2);
lean_inc_ref(v_code_2890_);
v___y_2874_ = v_code_2890_;
goto v___jp_2873_;
}
case 1:
{
lean_object* v_code_2891_; 
v_code_2891_ = lean_ctor_get(v___x_2889_, 1);
lean_inc_ref(v_code_2891_);
v___y_2874_ = v_code_2891_;
goto v___jp_2873_;
}
default: 
{
lean_object* v_code_2892_; 
v_code_2892_ = lean_ctor_get(v___x_2889_, 0);
lean_inc_ref(v_code_2892_);
v___y_2874_ = v_code_2892_;
goto v___jp_2873_;
}
}
v___jp_2873_:
{
lean_object* v___x_2875_; 
lean_inc_ref(v_f_2862_);
v___x_2875_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2861_, v_f_2862_, v___y_2874_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2888_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2888_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2888_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
uint8_t v___x_2880_; 
v___x_2880_ = lean_unbox(v_a_2876_);
lean_dec(v_a_2876_);
if (v___x_2880_ == 0)
{
size_t v___x_2881_; size_t v___x_2882_; 
lean_del_object(v___x_2878_);
v___x_2881_ = ((size_t)1ULL);
v___x_2882_ = lean_usize_add(v_i_2864_, v___x_2881_);
v_i_2864_ = v___x_2882_;
goto _start;
}
else
{
lean_object* v___x_2884_; lean_object* v___x_2886_; 
lean_dec_ref(v_f_2862_);
v___x_2884_ = lean_box(v___x_2872_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2884_);
v___x_2886_ = v___x_2878_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
else
{
lean_dec_ref(v_f_2862_);
return v___x_2875_;
}
}
}
else
{
uint8_t v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
lean_dec_ref(v_f_2862_);
v___x_2893_ = 0;
v___x_2894_ = lean_box(v___x_2893_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0___boxed(lean_object* v_pu_2896_, lean_object* v_f_2897_, lean_object* v_as_2898_, lean_object* v_i_2899_, lean_object* v_stop_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
uint8_t v_pu_boxed_2906_; size_t v_i_boxed_2907_; size_t v_stop_boxed_2908_; lean_object* v_res_2909_; 
v_pu_boxed_2906_ = lean_unbox(v_pu_2896_);
v_i_boxed_2907_ = lean_unbox_usize(v_i_2899_);
lean_dec(v_i_2899_);
v_stop_boxed_2908_ = lean_unbox_usize(v_stop_2900_);
lean_dec(v_stop_2900_);
v_res_2909_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_boxed_2906_, v_f_2897_, v_as_2898_, v_i_boxed_2907_, v_stop_boxed_2908_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
lean_dec_ref(v_as_2898_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed(lean_object* v_pu_2910_, lean_object* v_f_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
uint8_t v_pu_boxed_2918_; lean_object* v_res_2919_; 
v_pu_boxed_2918_ = lean_unbox(v_pu_2910_);
v_res_2919_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_boxed_2918_, v_f_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
lean_dec(v_a_2916_);
lean_dec_ref(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec_ref(v_a_2913_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(uint8_t v_pu_2920_, lean_object* v_f_2921_, lean_object* v_as_2922_, size_t v_i_2923_, size_t v_stop_2924_, lean_object* v_b_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_usize_dec_eq(v_i_2923_, v_stop_2924_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v_value_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2932_ = lean_array_uget_borrowed(v_as_2922_, v_i_2923_);
v_value_2933_ = lean_ctor_get(v___x_2932_, 1);
v___x_2934_ = lean_box(v_pu_2920_);
lean_inc_ref(v_f_2921_);
v___x_2935_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed), 8, 2);
lean_closure_set(v___x_2935_, 0, v___x_2934_);
lean_closure_set(v___x_2935_, 1, v_f_2921_);
lean_inc_ref(v_value_2933_);
v___x_2936_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2933_, v___x_2935_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v_a_2939_; uint8_t v___x_2943_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref(v___x_2936_);
v___x_2943_ = lean_unbox(v_a_2937_);
lean_dec(v_a_2937_);
if (v___x_2943_ == 0)
{
v_a_2939_ = v_b_2925_;
goto v___jp_2938_;
}
else
{
lean_object* v___x_2944_; 
lean_inc(v___x_2932_);
v___x_2944_ = lean_array_push(v_b_2925_, v___x_2932_);
v_a_2939_ = v___x_2944_;
goto v___jp_2938_;
}
v___jp_2938_:
{
size_t v___x_2940_; size_t v___x_2941_; 
v___x_2940_ = ((size_t)1ULL);
v___x_2941_ = lean_usize_add(v_i_2923_, v___x_2940_);
v_i_2923_ = v___x_2941_;
v_b_2925_ = v_a_2939_;
goto _start;
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec_ref(v_b_2925_);
lean_dec_ref(v_f_2921_);
v_a_2945_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2936_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2936_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
else
{
lean_object* v___x_2953_; 
lean_dec_ref(v_f_2921_);
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_b_2925_);
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0___boxed(lean_object* v_pu_2954_, lean_object* v_f_2955_, lean_object* v_as_2956_, lean_object* v_i_2957_, lean_object* v_stop_2958_, lean_object* v_b_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
uint8_t v_pu_boxed_2965_; size_t v_i_boxed_2966_; size_t v_stop_boxed_2967_; lean_object* v_res_2968_; 
v_pu_boxed_2965_ = lean_unbox(v_pu_2954_);
v_i_boxed_2966_ = lean_unbox_usize(v_i_2957_);
lean_dec(v_i_2957_);
v_stop_boxed_2967_ = lean_unbox_usize(v_stop_2958_);
lean_dec(v_stop_2958_);
v_res_2968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_boxed_2965_, v_f_2955_, v_as_2956_, v_i_boxed_2966_, v_stop_boxed_2967_, v_b_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v_as_2956_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach(uint8_t v_pu_2969_, lean_object* v_f_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = lean_array_get_size(v_a_2971_);
v___x_2979_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2980_ = lean_nat_dec_lt(v___x_2977_, v___x_2978_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; 
lean_dec_ref(v_f_2970_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2979_);
return v___x_2981_;
}
else
{
uint8_t v___x_2982_; 
v___x_2982_ = lean_nat_dec_le(v___x_2978_, v___x_2978_);
if (v___x_2982_ == 0)
{
if (v___x_2980_ == 0)
{
lean_object* v___x_2983_; 
lean_dec_ref(v_f_2970_);
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2979_);
return v___x_2983_;
}
else
{
size_t v___x_2984_; size_t v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = ((size_t)0ULL);
v___x_2985_ = lean_usize_of_nat(v___x_2978_);
v___x_2986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_2969_, v_f_2970_, v_a_2971_, v___x_2984_, v___x_2985_, v___x_2979_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
return v___x_2986_;
}
}
else
{
size_t v___x_2987_; size_t v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = ((size_t)0ULL);
v___x_2988_ = lean_usize_of_nat(v___x_2978_);
v___x_2989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_2969_, v_f_2970_, v_a_2971_, v___x_2987_, v___x_2988_, v___x_2979_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
return v___x_2989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach___boxed(lean_object* v_pu_2990_, lean_object* v_f_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
uint8_t v_pu_boxed_2998_; lean_object* v_res_2999_; 
v_pu_boxed_2998_ = lean_unbox(v_pu_2990_);
v_res_2999_ = l_Lean_Compiler_LCNF_Probe_filterByUnreach(v_pu_boxed_2998_, v_f_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec_ref(v_a_2992_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(lean_object* v_decl_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_toSignature_3006_; lean_object* v_name_3007_; lean_object* v___x_3008_; 
v_toSignature_3006_ = lean_ctor_get(v_decl_3000_, 0);
v_name_3007_ = lean_ctor_get(v_toSignature_3006_, 0);
lean_inc(v_name_3007_);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_name_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed(lean_object* v_decl_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(v_decl_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v_decl_3009_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg(lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v___x_3023_; lean_object* v_toApplicative_3024_; lean_object* v_toFunctor_3025_; lean_object* v_toSeq_3026_; lean_object* v_toSeqLeft_3027_; lean_object* v_toSeqRight_3028_; lean_object* v___f_3029_; lean_object* v___f_3030_; lean_object* v___f_3031_; lean_object* v___f_3032_; lean_object* v___x_3033_; lean_object* v___f_3034_; lean_object* v___f_3035_; lean_object* v___f_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v_toApplicative_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3072_; 
v___x_3023_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3024_ = lean_ctor_get(v___x_3023_, 0);
v_toFunctor_3025_ = lean_ctor_get(v_toApplicative_3024_, 0);
v_toSeq_3026_ = lean_ctor_get(v_toApplicative_3024_, 2);
v_toSeqLeft_3027_ = lean_ctor_get(v_toApplicative_3024_, 3);
v_toSeqRight_3028_ = lean_ctor_get(v_toApplicative_3024_, 4);
v___f_3029_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3030_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3025_, 2);
v___f_3031_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3031_, 0, v_toFunctor_3025_);
v___f_3032_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3032_, 0, v_toFunctor_3025_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___f_3031_);
lean_ctor_set(v___x_3033_, 1, v___f_3032_);
lean_inc(v_toSeqRight_3028_);
v___f_3034_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3034_, 0, v_toSeqRight_3028_);
lean_inc(v_toSeqLeft_3027_);
v___f_3035_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3035_, 0, v_toSeqLeft_3027_);
lean_inc(v_toSeq_3026_);
v___f_3036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3036_, 0, v_toSeq_3026_);
v___x_3037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3033_);
lean_ctor_set(v___x_3037_, 1, v___f_3029_);
lean_ctor_set(v___x_3037_, 2, v___f_3036_);
lean_ctor_set(v___x_3037_, 3, v___f_3035_);
lean_ctor_set(v___x_3037_, 4, v___f_3034_);
v___x_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v___f_3030_);
v___x_3039_ = l_StateRefT_x27_instMonad___redArg(v___x_3038_);
v_toApplicative_3040_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3072_ == 0)
{
lean_object* v_unused_3073_; 
v_unused_3073_ = lean_ctor_get(v___x_3039_, 1);
lean_dec(v_unused_3073_);
v___x_3042_ = v___x_3039_;
v_isShared_3043_ = v_isSharedCheck_3072_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_toApplicative_3040_);
lean_dec(v___x_3039_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3072_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_toFunctor_3044_; lean_object* v_toSeq_3045_; lean_object* v_toSeqLeft_3046_; lean_object* v_toSeqRight_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3070_; 
v_toFunctor_3044_ = lean_ctor_get(v_toApplicative_3040_, 0);
v_toSeq_3045_ = lean_ctor_get(v_toApplicative_3040_, 2);
v_toSeqLeft_3046_ = lean_ctor_get(v_toApplicative_3040_, 3);
v_toSeqRight_3047_ = lean_ctor_get(v_toApplicative_3040_, 4);
v_isSharedCheck_3070_ = !lean_is_exclusive(v_toApplicative_3040_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; 
v_unused_3071_ = lean_ctor_get(v_toApplicative_3040_, 1);
lean_dec(v_unused_3071_);
v___x_3049_ = v_toApplicative_3040_;
v_isShared_3050_ = v_isSharedCheck_3070_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_toSeqRight_3047_);
lean_inc(v_toSeqLeft_3046_);
lean_inc(v_toSeq_3045_);
lean_inc(v_toFunctor_3044_);
lean_dec(v_toApplicative_3040_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3070_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___f_3051_; lean_object* v___f_3052_; lean_object* v___f_3053_; lean_object* v___f_3054_; lean_object* v___f_3055_; lean_object* v___x_3056_; lean_object* v___f_3057_; lean_object* v___f_3058_; lean_object* v___f_3059_; lean_object* v___x_3061_; 
v___f_3051_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3052_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3053_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3044_);
v___f_3054_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3054_, 0, v_toFunctor_3044_);
v___f_3055_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3055_, 0, v_toFunctor_3044_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___f_3054_);
lean_ctor_set(v___x_3056_, 1, v___f_3055_);
v___f_3057_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3057_, 0, v_toSeqRight_3047_);
v___f_3058_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3058_, 0, v_toSeqLeft_3046_);
v___f_3059_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3059_, 0, v_toSeq_3045_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 4, v___f_3057_);
lean_ctor_set(v___x_3049_, 3, v___f_3058_);
lean_ctor_set(v___x_3049_, 2, v___f_3059_);
lean_ctor_set(v___x_3049_, 1, v___f_3052_);
lean_ctor_set(v___x_3049_, 0, v___x_3056_);
v___x_3061_ = v___x_3049_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___f_3052_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v___f_3059_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v___f_3058_);
lean_ctor_set(v_reuseFailAlloc_3069_, 4, v___f_3057_);
v___x_3061_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3063_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 1, v___f_3053_);
lean_ctor_set(v___x_3042_, 0, v___x_3061_);
v___x_3063_ = v___x_3042_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___f_3053_);
v___x_3063_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
size_t v_sz_3064_; size_t v___x_3065_; lean_object* v___x_127__overap_3066_; lean_object* v___x_3067_; 
v_sz_3064_ = lean_array_size(v_a_3017_);
v___x_3065_ = ((size_t)0ULL);
v___x_127__overap_3066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3063_, v___f_3051_, v_sz_3064_, v___x_3065_, v_a_3017_);
lean_inc(v_a_3021_);
lean_inc_ref(v_a_3020_);
lean_inc(v_a_3019_);
lean_inc_ref(v_a_3018_);
v___x_3067_ = lean_apply_5(v___x_127__overap_3066_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, lean_box(0));
return v___x_3067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___boxed(lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg(v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames(uint8_t v_pu_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v___x_3088_; lean_object* v_toApplicative_3089_; lean_object* v_toFunctor_3090_; lean_object* v_toSeq_3091_; lean_object* v_toSeqLeft_3092_; lean_object* v_toSeqRight_3093_; lean_object* v___f_3094_; lean_object* v___f_3095_; lean_object* v___f_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___f_3099_; lean_object* v___f_3100_; lean_object* v___f_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v_toApplicative_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3137_; 
v___x_3088_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3089_ = lean_ctor_get(v___x_3088_, 0);
v_toFunctor_3090_ = lean_ctor_get(v_toApplicative_3089_, 0);
v_toSeq_3091_ = lean_ctor_get(v_toApplicative_3089_, 2);
v_toSeqLeft_3092_ = lean_ctor_get(v_toApplicative_3089_, 3);
v_toSeqRight_3093_ = lean_ctor_get(v_toApplicative_3089_, 4);
v___f_3094_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3095_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3090_, 2);
v___f_3096_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3096_, 0, v_toFunctor_3090_);
v___f_3097_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3097_, 0, v_toFunctor_3090_);
v___x_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___f_3096_);
lean_ctor_set(v___x_3098_, 1, v___f_3097_);
lean_inc(v_toSeqRight_3093_);
v___f_3099_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3099_, 0, v_toSeqRight_3093_);
lean_inc(v_toSeqLeft_3092_);
v___f_3100_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3100_, 0, v_toSeqLeft_3092_);
lean_inc(v_toSeq_3091_);
v___f_3101_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3101_, 0, v_toSeq_3091_);
v___x_3102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3098_);
lean_ctor_set(v___x_3102_, 1, v___f_3094_);
lean_ctor_set(v___x_3102_, 2, v___f_3101_);
lean_ctor_set(v___x_3102_, 3, v___f_3100_);
lean_ctor_set(v___x_3102_, 4, v___f_3099_);
v___x_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
lean_ctor_set(v___x_3103_, 1, v___f_3095_);
v___x_3104_ = l_StateRefT_x27_instMonad___redArg(v___x_3103_);
v_toApplicative_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v___x_3104_, 1);
lean_dec(v_unused_3138_);
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3137_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_toApplicative_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3137_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v_toFunctor_3109_; lean_object* v_toSeq_3110_; lean_object* v_toSeqLeft_3111_; lean_object* v_toSeqRight_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3135_; 
v_toFunctor_3109_ = lean_ctor_get(v_toApplicative_3105_, 0);
v_toSeq_3110_ = lean_ctor_get(v_toApplicative_3105_, 2);
v_toSeqLeft_3111_ = lean_ctor_get(v_toApplicative_3105_, 3);
v_toSeqRight_3112_ = lean_ctor_get(v_toApplicative_3105_, 4);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_toApplicative_3105_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v_toApplicative_3105_, 1);
lean_dec(v_unused_3136_);
v___x_3114_ = v_toApplicative_3105_;
v_isShared_3115_ = v_isSharedCheck_3135_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_toSeqRight_3112_);
lean_inc(v_toSeqLeft_3111_);
lean_inc(v_toSeq_3110_);
lean_inc(v_toFunctor_3109_);
lean_dec(v_toApplicative_3105_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3135_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___f_3116_; lean_object* v___f_3117_; lean_object* v___f_3118_; lean_object* v___f_3119_; lean_object* v___f_3120_; lean_object* v___x_3121_; lean_object* v___f_3122_; lean_object* v___f_3123_; lean_object* v___f_3124_; lean_object* v___x_3126_; 
v___f_3116_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3117_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3118_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3109_);
v___f_3119_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3119_, 0, v_toFunctor_3109_);
v___f_3120_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3120_, 0, v_toFunctor_3109_);
v___x_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___f_3119_);
lean_ctor_set(v___x_3121_, 1, v___f_3120_);
v___f_3122_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3122_, 0, v_toSeqRight_3112_);
v___f_3123_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3123_, 0, v_toSeqLeft_3111_);
v___f_3124_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3124_, 0, v_toSeq_3110_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 4, v___f_3122_);
lean_ctor_set(v___x_3114_, 3, v___f_3123_);
lean_ctor_set(v___x_3114_, 2, v___f_3124_);
lean_ctor_set(v___x_3114_, 1, v___f_3117_);
lean_ctor_set(v___x_3114_, 0, v___x_3121_);
v___x_3126_ = v___x_3114_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___f_3117_);
lean_ctor_set(v_reuseFailAlloc_3134_, 2, v___f_3124_);
lean_ctor_set(v_reuseFailAlloc_3134_, 3, v___f_3123_);
lean_ctor_set(v_reuseFailAlloc_3134_, 4, v___f_3122_);
v___x_3126_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3128_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v___f_3118_);
lean_ctor_set(v___x_3107_, 0, v___x_3126_);
v___x_3128_ = v___x_3107_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v___f_3118_);
v___x_3128_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
size_t v_sz_3129_; size_t v___x_3130_; lean_object* v___x_185__overap_3131_; lean_object* v___x_3132_; 
v_sz_3129_ = lean_array_size(v_a_3082_);
v___x_3130_ = ((size_t)0ULL);
v___x_185__overap_3131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3128_, v___f_3116_, v_sz_3129_, v___x_3130_, v_a_3082_);
lean_inc(v_a_3086_);
lean_inc_ref(v_a_3085_);
lean_inc(v_a_3084_);
lean_inc_ref(v_a_3083_);
v___x_3132_ = lean_apply_5(v___x_185__overap_3131_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, lean_box(0));
return v___x_3132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___boxed(lean_object* v_pu_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
uint8_t v_pu_boxed_3146_; lean_object* v_res_3147_; 
v_pu_boxed_3146_ = lean_unbox(v_pu_3139_);
v_res_3147_ = l_Lean_Compiler_LCNF_Probe_declNames(v_pu_boxed_3146_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(lean_object* v_inst_3148_, lean_object* v_x_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = lean_apply_1(v_inst_3148_, v_x_3149_);
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed(lean_object* v_inst_3157_, lean_object* v_x_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(v_inst_3157_, v_x_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg(lean_object* v_inst_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v___x_3172_; lean_object* v_toApplicative_3173_; lean_object* v_toFunctor_3174_; lean_object* v_toSeq_3175_; lean_object* v_toSeqLeft_3176_; lean_object* v_toSeqRight_3177_; lean_object* v___f_3178_; lean_object* v___f_3179_; lean_object* v___f_3180_; lean_object* v___f_3181_; lean_object* v___x_3182_; lean_object* v___f_3183_; lean_object* v___f_3184_; lean_object* v___f_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v_toApplicative_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3221_; 
v___x_3172_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3173_ = lean_ctor_get(v___x_3172_, 0);
v_toFunctor_3174_ = lean_ctor_get(v_toApplicative_3173_, 0);
v_toSeq_3175_ = lean_ctor_get(v_toApplicative_3173_, 2);
v_toSeqLeft_3176_ = lean_ctor_get(v_toApplicative_3173_, 3);
v_toSeqRight_3177_ = lean_ctor_get(v_toApplicative_3173_, 4);
v___f_3178_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3179_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3174_, 2);
v___f_3180_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3180_, 0, v_toFunctor_3174_);
v___f_3181_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3181_, 0, v_toFunctor_3174_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___f_3180_);
lean_ctor_set(v___x_3182_, 1, v___f_3181_);
lean_inc(v_toSeqRight_3177_);
v___f_3183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3183_, 0, v_toSeqRight_3177_);
lean_inc(v_toSeqLeft_3176_);
v___f_3184_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3184_, 0, v_toSeqLeft_3176_);
lean_inc(v_toSeq_3175_);
v___f_3185_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3185_, 0, v_toSeq_3175_);
v___x_3186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3182_);
lean_ctor_set(v___x_3186_, 1, v___f_3178_);
lean_ctor_set(v___x_3186_, 2, v___f_3185_);
lean_ctor_set(v___x_3186_, 3, v___f_3184_);
lean_ctor_set(v___x_3186_, 4, v___f_3183_);
v___x_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
lean_ctor_set(v___x_3187_, 1, v___f_3179_);
v___x_3188_ = l_StateRefT_x27_instMonad___redArg(v___x_3187_);
v_toApplicative_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v___x_3188_, 1);
lean_dec(v_unused_3222_);
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3221_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_toApplicative_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3221_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v_toFunctor_3193_; lean_object* v_toSeq_3194_; lean_object* v_toSeqLeft_3195_; lean_object* v_toSeqRight_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3219_; 
v_toFunctor_3193_ = lean_ctor_get(v_toApplicative_3189_, 0);
v_toSeq_3194_ = lean_ctor_get(v_toApplicative_3189_, 2);
v_toSeqLeft_3195_ = lean_ctor_get(v_toApplicative_3189_, 3);
v_toSeqRight_3196_ = lean_ctor_get(v_toApplicative_3189_, 4);
v_isSharedCheck_3219_ = !lean_is_exclusive(v_toApplicative_3189_);
if (v_isSharedCheck_3219_ == 0)
{
lean_object* v_unused_3220_; 
v_unused_3220_ = lean_ctor_get(v_toApplicative_3189_, 1);
lean_dec(v_unused_3220_);
v___x_3198_ = v_toApplicative_3189_;
v_isShared_3199_ = v_isSharedCheck_3219_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_toSeqRight_3196_);
lean_inc(v_toSeqLeft_3195_);
lean_inc(v_toSeq_3194_);
lean_inc(v_toFunctor_3193_);
lean_dec(v_toApplicative_3189_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3219_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___f_3200_; lean_object* v___f_3201_; lean_object* v___f_3202_; lean_object* v___f_3203_; lean_object* v___f_3204_; lean_object* v___x_3205_; lean_object* v___f_3206_; lean_object* v___f_3207_; lean_object* v___f_3208_; lean_object* v___x_3210_; 
v___f_3200_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3200_, 0, v_inst_3165_);
v___f_3201_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3202_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3193_);
v___f_3203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3203_, 0, v_toFunctor_3193_);
v___f_3204_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3204_, 0, v_toFunctor_3193_);
v___x_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___f_3203_);
lean_ctor_set(v___x_3205_, 1, v___f_3204_);
v___f_3206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3206_, 0, v_toSeqRight_3196_);
v___f_3207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3207_, 0, v_toSeqLeft_3195_);
v___f_3208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3208_, 0, v_toSeq_3194_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 4, v___f_3206_);
lean_ctor_set(v___x_3198_, 3, v___f_3207_);
lean_ctor_set(v___x_3198_, 2, v___f_3208_);
lean_ctor_set(v___x_3198_, 1, v___f_3201_);
lean_ctor_set(v___x_3198_, 0, v___x_3205_);
v___x_3210_ = v___x_3198_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v___f_3201_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v___f_3208_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v___f_3207_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v___f_3206_);
v___x_3210_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3212_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___f_3202_);
lean_ctor_set(v___x_3191_, 0, v___x_3210_);
v___x_3212_ = v___x_3191_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v___f_3202_);
v___x_3212_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
size_t v_sz_3213_; size_t v___x_3214_; lean_object* v___x_129__overap_3215_; lean_object* v___x_3216_; 
v_sz_3213_ = lean_array_size(v_a_3166_);
v___x_3214_ = ((size_t)0ULL);
v___x_129__overap_3215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3212_, v___f_3200_, v_sz_3213_, v___x_3214_, v_a_3166_);
lean_inc(v_a_3170_);
lean_inc_ref(v_a_3169_);
lean_inc(v_a_3168_);
lean_inc_ref(v_a_3167_);
v___x_3216_ = lean_apply_5(v___x_129__overap_3215_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, lean_box(0));
return v___x_3216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___boxed(lean_object* v_inst_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Lean_Compiler_LCNF_Probe_toString___redArg(v_inst_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
lean_dec(v_a_3228_);
lean_dec_ref(v_a_3227_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString(lean_object* v_00_u03b1_3231_, lean_object* v_inst_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v___x_3239_; lean_object* v_toApplicative_3240_; lean_object* v_toFunctor_3241_; lean_object* v_toSeq_3242_; lean_object* v_toSeqLeft_3243_; lean_object* v_toSeqRight_3244_; lean_object* v___f_3245_; lean_object* v___f_3246_; lean_object* v___f_3247_; lean_object* v___f_3248_; lean_object* v___x_3249_; lean_object* v___f_3250_; lean_object* v___f_3251_; lean_object* v___f_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v_toApplicative_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3288_; 
v___x_3239_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3240_ = lean_ctor_get(v___x_3239_, 0);
v_toFunctor_3241_ = lean_ctor_get(v_toApplicative_3240_, 0);
v_toSeq_3242_ = lean_ctor_get(v_toApplicative_3240_, 2);
v_toSeqLeft_3243_ = lean_ctor_get(v_toApplicative_3240_, 3);
v_toSeqRight_3244_ = lean_ctor_get(v_toApplicative_3240_, 4);
v___f_3245_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3246_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3241_, 2);
v___f_3247_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3247_, 0, v_toFunctor_3241_);
v___f_3248_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3248_, 0, v_toFunctor_3241_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___f_3247_);
lean_ctor_set(v___x_3249_, 1, v___f_3248_);
lean_inc(v_toSeqRight_3244_);
v___f_3250_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3250_, 0, v_toSeqRight_3244_);
lean_inc(v_toSeqLeft_3243_);
v___f_3251_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3251_, 0, v_toSeqLeft_3243_);
lean_inc(v_toSeq_3242_);
v___f_3252_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3252_, 0, v_toSeq_3242_);
v___x_3253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3249_);
lean_ctor_set(v___x_3253_, 1, v___f_3245_);
lean_ctor_set(v___x_3253_, 2, v___f_3252_);
lean_ctor_set(v___x_3253_, 3, v___f_3251_);
lean_ctor_set(v___x_3253_, 4, v___f_3250_);
v___x_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
lean_ctor_set(v___x_3254_, 1, v___f_3246_);
v___x_3255_ = l_StateRefT_x27_instMonad___redArg(v___x_3254_);
v_toApplicative_3256_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3288_ == 0)
{
lean_object* v_unused_3289_; 
v_unused_3289_ = lean_ctor_get(v___x_3255_, 1);
lean_dec(v_unused_3289_);
v___x_3258_ = v___x_3255_;
v_isShared_3259_ = v_isSharedCheck_3288_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_toApplicative_3256_);
lean_dec(v___x_3255_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3288_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v_toFunctor_3260_; lean_object* v_toSeq_3261_; lean_object* v_toSeqLeft_3262_; lean_object* v_toSeqRight_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3286_; 
v_toFunctor_3260_ = lean_ctor_get(v_toApplicative_3256_, 0);
v_toSeq_3261_ = lean_ctor_get(v_toApplicative_3256_, 2);
v_toSeqLeft_3262_ = lean_ctor_get(v_toApplicative_3256_, 3);
v_toSeqRight_3263_ = lean_ctor_get(v_toApplicative_3256_, 4);
v_isSharedCheck_3286_ = !lean_is_exclusive(v_toApplicative_3256_);
if (v_isSharedCheck_3286_ == 0)
{
lean_object* v_unused_3287_; 
v_unused_3287_ = lean_ctor_get(v_toApplicative_3256_, 1);
lean_dec(v_unused_3287_);
v___x_3265_ = v_toApplicative_3256_;
v_isShared_3266_ = v_isSharedCheck_3286_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_toSeqRight_3263_);
lean_inc(v_toSeqLeft_3262_);
lean_inc(v_toSeq_3261_);
lean_inc(v_toFunctor_3260_);
lean_dec(v_toApplicative_3256_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3286_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___f_3267_; lean_object* v___f_3268_; lean_object* v___f_3269_; lean_object* v___f_3270_; lean_object* v___f_3271_; lean_object* v___x_3272_; lean_object* v___f_3273_; lean_object* v___f_3274_; lean_object* v___f_3275_; lean_object* v___x_3277_; 
v___f_3267_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3267_, 0, v_inst_3232_);
v___f_3268_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3269_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3260_);
v___f_3270_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3270_, 0, v_toFunctor_3260_);
v___f_3271_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3271_, 0, v_toFunctor_3260_);
v___x_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___f_3270_);
lean_ctor_set(v___x_3272_, 1, v___f_3271_);
v___f_3273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3273_, 0, v_toSeqRight_3263_);
v___f_3274_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3274_, 0, v_toSeqLeft_3262_);
v___f_3275_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3275_, 0, v_toSeq_3261_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 4, v___f_3273_);
lean_ctor_set(v___x_3265_, 3, v___f_3274_);
lean_ctor_set(v___x_3265_, 2, v___f_3275_);
lean_ctor_set(v___x_3265_, 1, v___f_3268_);
lean_ctor_set(v___x_3265_, 0, v___x_3272_);
v___x_3277_ = v___x_3265_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v___f_3268_);
lean_ctor_set(v_reuseFailAlloc_3285_, 2, v___f_3275_);
lean_ctor_set(v_reuseFailAlloc_3285_, 3, v___f_3274_);
lean_ctor_set(v_reuseFailAlloc_3285_, 4, v___f_3273_);
v___x_3277_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
lean_object* v___x_3279_; 
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 1, v___f_3269_);
lean_ctor_set(v___x_3258_, 0, v___x_3277_);
v___x_3279_ = v___x_3258_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3277_);
lean_ctor_set(v_reuseFailAlloc_3284_, 1, v___f_3269_);
v___x_3279_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
size_t v_sz_3280_; size_t v___x_3281_; lean_object* v___x_190__overap_3282_; lean_object* v___x_3283_; 
v_sz_3280_ = lean_array_size(v_a_3233_);
v___x_3281_ = ((size_t)0ULL);
v___x_190__overap_3282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3279_, v___f_3267_, v_sz_3280_, v___x_3281_, v_a_3233_);
lean_inc(v_a_3237_);
lean_inc_ref(v_a_3236_);
lean_inc(v_a_3235_);
lean_inc_ref(v_a_3234_);
v___x_3283_ = lean_apply_5(v___x_190__overap_3282_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, lean_box(0));
return v___x_3283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___boxed(lean_object* v_00_u03b1_3290_, lean_object* v_inst_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l_Lean_Compiler_LCNF_Probe_toString(v_00_u03b1_3290_, v_inst_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg(lean_object* v_data_3299_){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3301_ = lean_array_get_size(v_data_3299_);
v___x_3302_ = lean_unsigned_to_nat(1u);
v___x_3303_ = lean_mk_empty_array_with_capacity(v___x_3302_);
v___x_3304_ = lean_array_push(v___x_3303_, v___x_3301_);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg___boxed(lean_object* v_data_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_Compiler_LCNF_Probe_count___redArg(v_data_3306_);
lean_dec_ref(v_data_3306_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count(lean_object* v_00_u03b1_3309_, lean_object* v_data_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3316_ = lean_array_get_size(v_data_3310_);
v___x_3317_ = lean_unsigned_to_nat(1u);
v___x_3318_ = lean_mk_empty_array_with_capacity(v___x_3317_);
v___x_3319_ = lean_array_push(v___x_3318_, v___x_3316_);
v___x_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___boxed(lean_object* v_00_u03b1_3321_, lean_object* v_data_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_Compiler_LCNF_Probe_count(v_00_u03b1_3321_, v_data_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_);
lean_dec(v_a_3326_);
lean_dec_ref(v_a_3325_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec_ref(v_data_3322_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg(lean_object* v_data_3330_){
_start:
{
lean_object* v___y_3333_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3338_ = lean_unsigned_to_nat(0u);
v___x_3339_ = lean_array_get_size(v_data_3330_);
v___x_3340_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3341_ = lean_nat_dec_lt(v___x_3338_, v___x_3339_);
if (v___x_3341_ == 0)
{
lean_dec_ref(v_data_3330_);
v___y_3333_ = v___x_3338_;
goto v___jp_3332_;
}
else
{
lean_object* v___f_3342_; uint8_t v___x_3343_; 
v___f_3342_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3343_ = lean_nat_dec_le(v___x_3339_, v___x_3339_);
if (v___x_3343_ == 0)
{
if (v___x_3341_ == 0)
{
lean_dec_ref(v_data_3330_);
v___y_3333_ = v___x_3338_;
goto v___jp_3332_;
}
else
{
size_t v___x_3344_; size_t v___x_3345_; lean_object* v___x_3346_; 
v___x_3344_ = ((size_t)0ULL);
v___x_3345_ = lean_usize_of_nat(v___x_3339_);
v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3340_, v___f_3342_, v_data_3330_, v___x_3344_, v___x_3345_, v___x_3338_);
v___y_3333_ = v___x_3346_;
goto v___jp_3332_;
}
}
else
{
size_t v___x_3347_; size_t v___x_3348_; lean_object* v___x_3349_; 
v___x_3347_ = ((size_t)0ULL);
v___x_3348_ = lean_usize_of_nat(v___x_3339_);
v___x_3349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3340_, v___f_3342_, v_data_3330_, v___x_3347_, v___x_3348_, v___x_3338_);
v___y_3333_ = v___x_3349_;
goto v___jp_3332_;
}
}
v___jp_3332_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3334_ = lean_unsigned_to_nat(1u);
v___x_3335_ = lean_mk_empty_array_with_capacity(v___x_3334_);
v___x_3336_ = lean_array_push(v___x_3335_, v___y_3333_);
v___x_3337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
return v___x_3337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg___boxed(lean_object* v_data_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Compiler_LCNF_Probe_sum___redArg(v_data_3350_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum(lean_object* v_data_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v___y_3360_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___x_3365_ = lean_unsigned_to_nat(0u);
v___x_3366_ = lean_array_get_size(v_data_3353_);
v___x_3367_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3368_ = lean_nat_dec_lt(v___x_3365_, v___x_3366_);
if (v___x_3368_ == 0)
{
lean_dec_ref(v_data_3353_);
v___y_3360_ = v___x_3365_;
goto v___jp_3359_;
}
else
{
lean_object* v___f_3369_; uint8_t v___x_3370_; 
v___f_3369_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3370_ = lean_nat_dec_le(v___x_3366_, v___x_3366_);
if (v___x_3370_ == 0)
{
if (v___x_3368_ == 0)
{
lean_dec_ref(v_data_3353_);
v___y_3360_ = v___x_3365_;
goto v___jp_3359_;
}
else
{
size_t v___x_3371_; size_t v___x_3372_; lean_object* v___x_3373_; 
v___x_3371_ = ((size_t)0ULL);
v___x_3372_ = lean_usize_of_nat(v___x_3366_);
v___x_3373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3367_, v___f_3369_, v_data_3353_, v___x_3371_, v___x_3372_, v___x_3365_);
v___y_3360_ = v___x_3373_;
goto v___jp_3359_;
}
}
else
{
size_t v___x_3374_; size_t v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = ((size_t)0ULL);
v___x_3375_ = lean_usize_of_nat(v___x_3366_);
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3367_, v___f_3369_, v_data_3353_, v___x_3374_, v___x_3375_, v___x_3365_);
v___y_3360_ = v___x_3376_;
goto v___jp_3359_;
}
}
v___jp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3361_ = lean_unsigned_to_nat(1u);
v___x_3362_ = lean_mk_empty_array_with_capacity(v___x_3361_);
v___x_3363_ = lean_array_push(v___x_3362_, v___y_3360_);
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___boxed(lean_object* v_data_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_Compiler_LCNF_Probe_sum(v_data_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg(lean_object* v_n_3384_, lean_object* v_data_3385_){
_start:
{
lean_object* v_lower_3388_; lean_object* v_upper_3389_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3393_ = lean_array_get_size(v_data_3385_);
v___x_3394_ = lean_nat_sub(v___x_3393_, v_n_3384_);
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = lean_nat_dec_le(v___x_3394_, v___x_3395_);
if (v___x_3396_ == 0)
{
v_lower_3388_ = v___x_3394_;
v_upper_3389_ = v___x_3393_;
goto v___jp_3387_;
}
else
{
lean_dec(v___x_3394_);
v_lower_3388_ = v___x_3395_;
v_upper_3389_ = v___x_3393_;
goto v___jp_3387_;
}
v___jp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = l_Array_toSubarray___redArg(v_data_3385_, v_lower_3388_, v_upper_3389_);
v___x_3391_ = l_Subarray_copy___redArg(v___x_3390_);
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg___boxed(lean_object* v_n_3397_, lean_object* v_data_3398_, lean_object* v_a_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_Compiler_LCNF_Probe_tail___redArg(v_n_3397_, v_data_3398_);
lean_dec(v_n_3397_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail(lean_object* v_00_u03b1_3401_, lean_object* v_n_3402_, lean_object* v_data_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v_lower_3410_; lean_object* v_upper_3411_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; 
v___x_3415_ = lean_array_get_size(v_data_3403_);
v___x_3416_ = lean_nat_sub(v___x_3415_, v_n_3402_);
v___x_3417_ = lean_unsigned_to_nat(0u);
v___x_3418_ = lean_nat_dec_le(v___x_3416_, v___x_3417_);
if (v___x_3418_ == 0)
{
v_lower_3410_ = v___x_3416_;
v_upper_3411_ = v___x_3415_;
goto v___jp_3409_;
}
else
{
lean_dec(v___x_3416_);
v_lower_3410_ = v___x_3417_;
v_upper_3411_ = v___x_3415_;
goto v___jp_3409_;
}
v___jp_3409_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3412_ = l_Array_toSubarray___redArg(v_data_3403_, v_lower_3410_, v_upper_3411_);
v___x_3413_ = l_Subarray_copy___redArg(v___x_3412_);
v___x_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___boxed(lean_object* v_00_u03b1_3419_, lean_object* v_n_3420_, lean_object* v_data_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_Compiler_LCNF_Probe_tail(v_00_u03b1_3419_, v_n_3420_, v_data_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_);
lean_dec(v_a_3425_);
lean_dec_ref(v_a_3424_);
lean_dec(v_a_3423_);
lean_dec_ref(v_a_3422_);
lean_dec(v_n_3420_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg(lean_object* v_n_3428_, lean_object* v_data_3429_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3431_ = lean_unsigned_to_nat(0u);
v___x_3432_ = l_Array_toSubarray___redArg(v_data_3429_, v___x_3431_, v_n_3428_);
v___x_3433_ = l_Subarray_copy___redArg(v___x_3432_);
v___x_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg___boxed(lean_object* v_n_3435_, lean_object* v_data_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_Compiler_LCNF_Probe_head___redArg(v_n_3435_, v_data_3436_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head(lean_object* v_00_u03b1_3439_, lean_object* v_n_3440_, lean_object* v_data_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3447_ = lean_unsigned_to_nat(0u);
v___x_3448_ = l_Array_toSubarray___redArg(v_data_3441_, v___x_3447_, v_n_3440_);
v___x_3449_ = l_Subarray_copy___redArg(v___x_3448_);
v___x_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___boxed(lean_object* v_00_u03b1_3451_, lean_object* v_n_3452_, lean_object* v_data_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Compiler_LCNF_Probe_head(v_00_u03b1_3451_, v_n_3452_, v_data_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(lean_object* v_probe_3468_, lean_object* v___x_3469_, lean_object* v___x_3470_, lean_object* v___f_3471_, lean_object* v_inst_3472_, lean_object* v___x_3473_, lean_object* v___x_3474_, lean_object* v_decls_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v___x_3481_; 
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
lean_inc_ref(v_decls_3475_);
v___x_3481_ = lean_apply_6(v_probe_3468_, v_decls_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, lean_box(0));
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_options_3482_; uint8_t v_hasTrace_3483_; 
v_options_3482_ = lean_ctor_get(v___y_3478_, 2);
v_hasTrace_3483_ = lean_ctor_get_uint8(v_options_3482_, sizeof(void*)*1);
if (v_hasTrace_3483_ == 0)
{
lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v___x_3474_);
lean_dec_ref(v___x_3473_);
lean_dec_ref(v_inst_3472_);
lean_dec(v___f_3471_);
lean_dec(v___x_3470_);
lean_dec_ref(v___x_3469_);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v___x_3481_, 0);
lean_dec(v_unused_3491_);
v___x_3485_ = v___x_3481_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_dec(v___x_3481_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v_decls_3475_);
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_decls_3475_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3536_; 
v_a_3492_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3494_ = v___x_3481_;
v_isShared_3495_ = v_isSharedCheck_3536_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3481_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3536_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v_inheritedTraceOptions_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; 
v_inheritedTraceOptions_3496_ = lean_ctor_get(v___y_3478_, 13);
v___x_3497_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0));
v___x_3498_ = l_Lean_Name_mkStr2(v___x_3497_, v___x_3469_);
v___x_3499_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2));
lean_inc(v___x_3498_);
v___x_3500_ = l_Lean_Name_append(v___x_3499_, v___x_3498_);
v___x_3501_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3496_, v_options_3482_, v___x_3500_);
lean_dec(v___x_3500_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3503_; 
lean_dec(v___x_3498_);
lean_dec(v_a_3492_);
lean_dec_ref(v___x_3474_);
lean_dec_ref(v___x_3473_);
lean_dec_ref(v_inst_3472_);
lean_dec(v___f_3471_);
lean_dec(v___x_3470_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v_decls_3475_);
v___x_3503_ = v___x_3494_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_decls_3475_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
else
{
lean_object* v___f_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v_toMonadRef_3510_; lean_object* v___f_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_1076__overap_3518_; lean_object* v___x_3519_; 
lean_del_object(v___x_3494_);
v___f_3505_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3));
v___x_3506_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4));
v___x_3507_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_3508_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3506_, v___x_3470_, v___x_3507_);
v___x_3509_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3505_, v___f_3471_, v___x_3508_);
v_toMonadRef_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc_ref(v_toMonadRef_3510_);
lean_dec_ref(v___x_3509_);
v___f_3511_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__5));
v___x_3512_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__6));
v___x_3513_ = lean_array_to_list(v_a_3492_);
v___x_3514_ = l_List_toString___redArg(v_inst_3472_, v___x_3513_);
v___x_3515_ = lean_string_append(v___x_3512_, v___x_3514_);
lean_dec_ref(v___x_3514_);
v___x_3516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
v___x_3517_ = l_Lean_MessageData_ofFormat(v___x_3516_);
v___x_1076__overap_3518_ = l_Lean_addTrace___redArg(v___x_3473_, v___x_3474_, v_toMonadRef_3510_, v___f_3511_, v___x_3498_, v___x_3517_);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
v___x_3519_ = lean_apply_5(v___x_1076__overap_3518_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, lean_box(0));
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3526_ == 0)
{
lean_object* v_unused_3527_; 
v_unused_3527_ = lean_ctor_get(v___x_3519_, 0);
lean_dec(v_unused_3527_);
v___x_3521_ = v___x_3519_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_dec(v___x_3519_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v_decls_3475_);
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_decls_3475_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec_ref(v_decls_3475_);
v_a_3528_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3519_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3519_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v_decls_3475_);
lean_dec_ref(v___x_3474_);
lean_dec_ref(v___x_3473_);
lean_dec_ref(v_inst_3472_);
lean_dec(v___f_3471_);
lean_dec(v___x_3470_);
lean_dec_ref(v___x_3469_);
v_a_3537_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3481_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3481_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed(lean_object* v_probe_3545_, lean_object* v___x_3546_, lean_object* v___x_3547_, lean_object* v___f_3548_, lean_object* v_inst_3549_, lean_object* v___x_3550_, lean_object* v___x_3551_, lean_object* v_decls_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(v_probe_3545_, v___x_3546_, v___x_3547_, v___f_3548_, v_inst_3549_, v___x_3550_, v___x_3551_, v_decls_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
return v_res_3558_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = l_Lean_Core_instMonadTraceCoreM;
v___x_3562_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3563_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3562_, v___x_3561_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___f_3565_; lean_object* v___x_3566_; 
v___x_3564_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2);
v___f_3565_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___x_3566_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3565_, v___x_3564_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg(lean_object* v_inst_3570_, uint8_t v_phase_3571_, lean_object* v_probe_3572_){
_start:
{
lean_object* v___x_3573_; lean_object* v_toApplicative_3574_; lean_object* v_toFunctor_3575_; lean_object* v_toSeq_3576_; lean_object* v_toSeqLeft_3577_; lean_object* v_toSeqRight_3578_; lean_object* v___f_3579_; lean_object* v___f_3580_; lean_object* v___f_3581_; lean_object* v___f_3582_; lean_object* v___x_3583_; lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___f_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v_toApplicative_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3626_; 
v___x_3573_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3574_ = lean_ctor_get(v___x_3573_, 0);
v_toFunctor_3575_ = lean_ctor_get(v_toApplicative_3574_, 0);
v_toSeq_3576_ = lean_ctor_get(v_toApplicative_3574_, 2);
v_toSeqLeft_3577_ = lean_ctor_get(v_toApplicative_3574_, 3);
v_toSeqRight_3578_ = lean_ctor_get(v_toApplicative_3574_, 4);
v___f_3579_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3580_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3575_, 2);
v___f_3581_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3581_, 0, v_toFunctor_3575_);
v___f_3582_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3582_, 0, v_toFunctor_3575_);
v___x_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___f_3581_);
lean_ctor_set(v___x_3583_, 1, v___f_3582_);
lean_inc(v_toSeqRight_3578_);
v___f_3584_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3584_, 0, v_toSeqRight_3578_);
lean_inc(v_toSeqLeft_3577_);
v___f_3585_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3585_, 0, v_toSeqLeft_3577_);
lean_inc(v_toSeq_3576_);
v___f_3586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3586_, 0, v_toSeq_3576_);
v___x_3587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3583_);
lean_ctor_set(v___x_3587_, 1, v___f_3579_);
lean_ctor_set(v___x_3587_, 2, v___f_3586_);
lean_ctor_set(v___x_3587_, 3, v___f_3585_);
lean_ctor_set(v___x_3587_, 4, v___f_3584_);
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
lean_ctor_set(v___x_3588_, 1, v___f_3580_);
v___x_3589_ = l_StateRefT_x27_instMonad___redArg(v___x_3588_);
v_toApplicative_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v___x_3589_, 1);
lean_dec(v_unused_3627_);
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3626_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_toApplicative_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3626_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v_toFunctor_3594_; lean_object* v_toSeq_3595_; lean_object* v_toSeqLeft_3596_; lean_object* v_toSeqRight_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3624_; 
v_toFunctor_3594_ = lean_ctor_get(v_toApplicative_3590_, 0);
v_toSeq_3595_ = lean_ctor_get(v_toApplicative_3590_, 2);
v_toSeqLeft_3596_ = lean_ctor_get(v_toApplicative_3590_, 3);
v_toSeqRight_3597_ = lean_ctor_get(v_toApplicative_3590_, 4);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_toApplicative_3590_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; 
v_unused_3625_ = lean_ctor_get(v_toApplicative_3590_, 1);
lean_dec(v_unused_3625_);
v___x_3599_ = v_toApplicative_3590_;
v_isShared_3600_ = v_isSharedCheck_3624_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_toSeqRight_3597_);
lean_inc(v_toSeqLeft_3596_);
lean_inc(v_toSeq_3595_);
lean_inc(v_toFunctor_3594_);
lean_dec(v_toApplicative_3590_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3624_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___f_3601_; lean_object* v___f_3602_; lean_object* v___f_3603_; lean_object* v___f_3604_; lean_object* v___x_3605_; lean_object* v___f_3606_; lean_object* v___f_3607_; lean_object* v___f_3608_; lean_object* v___x_3610_; 
v___f_3601_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3602_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3594_);
v___f_3603_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3603_, 0, v_toFunctor_3594_);
v___f_3604_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3604_, 0, v_toFunctor_3594_);
v___x_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___f_3603_);
lean_ctor_set(v___x_3605_, 1, v___f_3604_);
v___f_3606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3606_, 0, v_toSeqRight_3597_);
v___f_3607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3607_, 0, v_toSeqLeft_3596_);
v___f_3608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3608_, 0, v_toSeq_3595_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 4, v___f_3606_);
lean_ctor_set(v___x_3599_, 3, v___f_3607_);
lean_ctor_set(v___x_3599_, 2, v___f_3608_);
lean_ctor_set(v___x_3599_, 1, v___f_3601_);
lean_ctor_set(v___x_3599_, 0, v___x_3605_);
v___x_3610_ = v___x_3599_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v___f_3601_);
lean_ctor_set(v_reuseFailAlloc_3623_, 2, v___f_3608_);
lean_ctor_set(v_reuseFailAlloc_3623_, 3, v___f_3607_);
lean_ctor_set(v_reuseFailAlloc_3623_, 4, v___f_3606_);
v___x_3610_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3612_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 1, v___f_3602_);
lean_ctor_set(v___x_3592_, 0, v___x_3610_);
v___x_3612_ = v___x_3592_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v___f_3602_);
v___x_3612_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___f_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; lean_object* v___x_3618_; lean_object* v___f_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___f_3613_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___x_3614_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3615_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3);
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = 0;
v___x_3618_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4));
v___f_3619_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_3619_, 0, v_probe_3572_);
lean_closure_set(v___f_3619_, 1, v___x_3618_);
lean_closure_set(v___f_3619_, 2, v___x_3614_);
lean_closure_set(v___f_3619_, 3, v___f_3613_);
lean_closure_set(v___f_3619_, 4, v_inst_3570_);
lean_closure_set(v___f_3619_, 5, v___x_3612_);
lean_closure_set(v___f_3619_, 6, v___x_3615_);
v___x_3620_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5));
v___x_3621_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3621_, 0, v___x_3616_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
lean_ctor_set(v___x_3621_, 2, v___f_3619_);
lean_ctor_set_uint8(v___x_3621_, sizeof(void*)*3, v_phase_3571_);
lean_ctor_set_uint8(v___x_3621_, sizeof(void*)*3 + 1, v_phase_3571_);
lean_ctor_set_uint8(v___x_3621_, sizeof(void*)*3 + 2, v___x_3617_);
return v___x_3621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(lean_object* v_inst_3628_, lean_object* v_phase_3629_, lean_object* v_probe_3630_){
_start:
{
uint8_t v_phase_boxed_3631_; lean_object* v_res_3632_; 
v_phase_boxed_3631_ = lean_unbox(v_phase_3629_);
v_res_3632_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3628_, v_phase_boxed_3631_, v_probe_3630_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass(lean_object* v_00_u03b2_3633_, lean_object* v_inst_3634_, uint8_t v_phase_3635_, lean_object* v_probe_3636_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3634_, v_phase_3635_, v_probe_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___boxed(lean_object* v_00_u03b2_3638_, lean_object* v_inst_3639_, lean_object* v_phase_3640_, lean_object* v_probe_3641_){
_start:
{
uint8_t v_phase_boxed_3642_; lean_object* v_res_3643_; 
v_phase_boxed_3642_ = lean_unbox(v_phase_3640_);
v_res_3643_ = l_Lean_Compiler_LCNF_Probe_toPass(v_00_u03b2_3638_, v_inst_3639_, v_phase_boxed_3642_, v_probe_3641_);
return v_res_3643_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3702_ = lean_unsigned_to_nat(4008565020u);
v___x_3703_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3704_ = l_Lean_Name_num___override(v___x_3703_, v___x_3702_);
return v___x_3704_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3706_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3707_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3708_ = l_Lean_Name_str___override(v___x_3707_, v___x_3706_);
return v___x_3708_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3710_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3711_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3712_ = l_Lean_Name_str___override(v___x_3711_, v___x_3710_);
return v___x_3712_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3713_ = lean_unsigned_to_nat(2u);
v___x_3714_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3715_ = l_Lean_Name_num___override(v___x_3714_, v___x_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3717_; uint8_t v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3717_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3718_ = 1;
v___x_3719_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3720_ = l_Lean_registerTraceClass(v___x_3717_, v___x_3718_, v___x_3719_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2____boxed(lean_object* v_a_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
return v_res_3722_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Probing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
