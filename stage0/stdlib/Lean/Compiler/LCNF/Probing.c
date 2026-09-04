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
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3_value;
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
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8_value;
static const lean_string_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "probe"};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(210, 226, 36, 16, 11, 213, 189, 181)}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(60, 150, 55, 23, 179, 120, 143, 48)}};
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
size_t v___x_238_; size_t v___x_239_; lean_object* v___x_348__overap_240_; lean_object* v___x_241_; 
v___x_238_ = ((size_t)0ULL);
v___x_239_ = lean_usize_of_nat(v___x_231_);
v___x_348__overap_240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_229_, v___f_235_, v_data_184_, v___x_238_, v___x_239_, v___x_232_);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
v___x_241_ = lean_apply_5(v___x_348__overap_240_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, lean_box(0));
return v___x_241_;
}
}
else
{
size_t v___x_242_; size_t v___x_243_; lean_object* v___x_352__overap_244_; lean_object* v___x_245_; 
v___x_242_ = ((size_t)0ULL);
v___x_243_ = lean_usize_of_nat(v___x_231_);
v___x_352__overap_244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_229_, v___f_235_, v_data_184_, v___x_242_, v___x_243_, v___x_232_);
lean_inc(v_a_188_);
lean_inc_ref(v_a_187_);
lean_inc(v_a_186_);
lean_inc_ref(v_a_185_);
v___x_245_ = lean_apply_5(v___x_352__overap_244_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, lean_box(0));
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
size_t v___x_316_; size_t v___x_317_; lean_object* v___x_436__overap_318_; lean_object* v___x_319_; 
v___x_316_ = ((size_t)0ULL);
v___x_317_ = lean_usize_of_nat(v___x_309_);
v___x_436__overap_318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_307_, v___f_313_, v_data_262_, v___x_316_, v___x_317_, v___x_310_);
lean_inc(v_a_266_);
lean_inc_ref(v_a_265_);
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
v___x_319_ = lean_apply_5(v___x_436__overap_318_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, lean_box(0));
return v___x_319_;
}
}
else
{
size_t v___x_320_; size_t v___x_321_; lean_object* v___x_439__overap_322_; lean_object* v___x_323_; 
v___x_320_ = ((size_t)0ULL);
v___x_321_ = lean_usize_of_nat(v___x_309_);
v___x_439__overap_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_307_, v___f_313_, v_data_262_, v___x_320_, v___x_321_, v___x_310_);
lean_inc(v_a_266_);
lean_inc_ref(v_a_265_);
lean_inc(v_a_264_);
lean_inc_ref(v_a_263_);
v___x_323_ = lean_apply_5(v___x_439__overap_322_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, lean_box(0));
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
lean_object* v___x_582_; lean_object* v_toApplicative_583_; lean_object* v_toFunctor_584_; lean_object* v_toSeq_585_; lean_object* v_toSeqLeft_586_; lean_object* v_toSeqRight_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___f_591_; lean_object* v___x_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v_toApplicative_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_669_; 
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
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v___x_598_, 1);
lean_dec(v_unused_670_);
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_669_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_toApplicative_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_669_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_toFunctor_603_; lean_object* v_toSeq_604_; lean_object* v_toSeqLeft_605_; lean_object* v_toSeqRight_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_667_; 
v_toFunctor_603_ = lean_ctor_get(v_toApplicative_599_, 0);
v_toSeq_604_ = lean_ctor_get(v_toApplicative_599_, 2);
v_toSeqLeft_605_ = lean_ctor_get(v_toApplicative_599_, 3);
v_toSeqRight_606_ = lean_ctor_get(v_toApplicative_599_, 4);
v_isSharedCheck_667_ = !lean_is_exclusive(v_toApplicative_599_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v_toApplicative_599_, 1);
lean_dec(v_unused_668_);
v___x_608_ = v_toApplicative_599_;
v_isShared_609_ = v_isSharedCheck_667_;
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
v_isShared_609_ = v_isSharedCheck_667_;
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
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___f_611_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v___f_618_);
lean_ctor_set(v_reuseFailAlloc_666_, 3, v___f_617_);
lean_ctor_set(v_reuseFailAlloc_666_, 4, v___f_616_);
v___x_620_ = v_reuseFailAlloc_666_;
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
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___f_612_);
v___x_622_ = v_reuseFailAlloc_665_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_map_632_; size_t v_sz_633_; size_t v___x_634_; lean_object* v___x_720__overap_635_; lean_object* v___x_636_; 
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
v___x_720__overap_635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_622_, v_data_576_, v___f_610_, v_sz_633_, v___x_634_, v_map_632_);
lean_inc(v_a_580_);
lean_inc_ref(v_a_579_);
lean_inc(v_a_578_);
lean_inc_ref(v_a_577_);
v___x_636_ = lean_apply_5(v___x_720__overap_635_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, lean_box(0));
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_656_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_656_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_656_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_656_;
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
lean_object* v___f_650_; size_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___f_650_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1));
v___x_651_ = lean_usize_of_nat(v___x_645_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_644_, v___f_650_, v_buckets_642_, v___x_634_, v___x_651_, v___x_643_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_652_);
v___x_654_ = v___x_639_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
v_a_657_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_636_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_636_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___boxed(lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_data_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_671_, v_inst_672_, v_data_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique(lean_object* v_00_u03b1_680_, lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_data_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_682_, v_inst_683_, v_data_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___boxed(lean_object* v_00_u03b1_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_data_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Compiler_LCNF_Probe_countUnique(v_00_u03b1_691_, v_inst_692_, v_inst_693_, v_inst_694_, v_data_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec_ref(v_inst_692_);
return v_res_701_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(lean_object* v_l_702_, lean_object* v_r_703_){
_start:
{
lean_object* v_snd_704_; lean_object* v_snd_705_; uint8_t v___x_706_; 
v_snd_704_ = lean_ctor_get(v_l_702_, 1);
v_snd_705_ = lean_ctor_get(v_r_703_, 1);
v___x_706_ = lean_nat_dec_lt(v_snd_704_, v_snd_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0___boxed(lean_object* v_l_707_, lean_object* v_r_708_){
_start:
{
uint8_t v_res_709_; lean_object* v_r_710_; 
v_res_709_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(v_l_707_, v_r_708_);
lean_dec_ref(v_r_708_);
lean_dec_ref(v_l_707_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_712_, v_inst_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
v___x_722_ = lean_array_get_size(v_a_721_);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_nat_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_742_; 
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_720_, 0);
lean_dec(v_unused_743_);
v___x_726_ = v___x_720_;
v_isShared_727_ = v_isSharedCheck_742_;
goto v_resetjp_725_;
}
else
{
lean_dec(v___x_720_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_742_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___f_728_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___y_739_; uint8_t v___x_741_; 
v___f_728_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_sub(v___x_722_, v___x_736_);
v___x_741_ = lean_nat_dec_le(v___x_723_, v___x_737_);
if (v___x_741_ == 0)
{
lean_inc(v___x_737_);
v___y_739_ = v___x_737_;
goto v___jp_738_;
}
else
{
v___y_739_ = v___x_723_;
goto v___jp_738_;
}
v___jp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_728_, v___x_722_, v_a_721_, v___y_730_, v___y_731_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_731_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_732_);
v___x_734_ = v___x_726_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
v___jp_738_:
{
uint8_t v___x_740_; 
v___x_740_ = lean_nat_dec_le(v___y_739_, v___x_737_);
if (v___x_740_ == 0)
{
lean_dec(v___x_737_);
lean_inc(v___y_739_);
v___y_730_ = v___y_739_;
v___y_731_ = v___y_739_;
goto v___jp_729_;
}
else
{
v___y_730_ = v___y_739_;
v___y_731_ = v___x_737_;
goto v___jp_729_;
}
}
}
}
else
{
lean_dec(v_a_721_);
return v___x_720_;
}
}
else
{
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___boxed(lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(v_inst_744_, v_inst_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted(lean_object* v_00_u03b1_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_755_, v_inst_756_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
v___x_766_ = lean_array_get_size(v_a_765_);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = lean_nat_dec_eq(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_786_; 
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v___x_764_, 0);
lean_dec(v_unused_787_);
v___x_770_ = v___x_764_;
v_isShared_771_ = v_isSharedCheck_786_;
goto v_resetjp_769_;
}
else
{
lean_dec(v___x_764_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_786_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___f_772_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___y_783_; uint8_t v___x_785_; 
v___f_772_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_sub(v___x_766_, v___x_780_);
v___x_785_ = lean_nat_dec_le(v___x_767_, v___x_781_);
if (v___x_785_ == 0)
{
lean_inc(v___x_781_);
v___y_783_ = v___x_781_;
goto v___jp_782_;
}
else
{
v___y_783_ = v___x_767_;
goto v___jp_782_;
}
v___jp_773_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_772_, v___x_766_, v_a_765_, v___y_774_, v___y_775_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_775_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_776_);
v___x_778_ = v___x_770_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
v___jp_782_:
{
uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_le(v___y_783_, v___x_781_);
if (v___x_784_ == 0)
{
lean_dec(v___x_781_);
lean_inc(v___y_783_);
v___y_774_ = v___y_783_;
v___y_775_ = v___y_783_;
goto v___jp_773_;
}
else
{
v___y_774_ = v___y_783_;
v___y_775_ = v___x_781_;
goto v___jp_773_;
}
}
}
}
else
{
lean_dec(v_a_765_);
return v___x_764_;
}
}
else
{
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___boxed(lean_object* v_00_u03b1_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted(v_00_u03b1_788_, v_inst_789_, v_inst_790_, v_inst_791_, v_inst_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_inst_792_);
lean_dec_ref(v_inst_789_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(uint8_t v_pu_800_, lean_object* v_c_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
switch(lean_obj_tag(v_c_801_))
{
case 0:
{
lean_object* v_decl_808_; lean_object* v_k_809_; lean_object* v___x_810_; lean_object* v_value_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_decl_808_ = lean_ctor_get(v_c_801_, 0);
lean_inc_ref(v_decl_808_);
v_k_809_ = lean_ctor_get(v_c_801_, 1);
lean_inc_ref(v_k_809_);
lean_dec_ref_known(v_c_801_, 2);
v___x_810_ = lean_st_ref_take(v_a_802_);
v_value_811_ = lean_ctor_get(v_decl_808_, 3);
lean_inc(v_value_811_);
lean_dec_ref(v_decl_808_);
v___x_812_ = lean_array_push(v___x_810_, v_value_811_);
v___x_813_ = lean_st_ref_put(v_a_802_, v___x_812_);
v_c_801_ = v_k_809_;
goto _start;
}
case 1:
{
lean_object* v_decl_815_; lean_object* v_k_816_; lean_object* v_value_817_; lean_object* v___x_818_; 
v_decl_815_ = lean_ctor_get(v_c_801_, 0);
lean_inc_ref(v_decl_815_);
v_k_816_ = lean_ctor_get(v_c_801_, 1);
lean_inc_ref(v_k_816_);
lean_dec_ref_known(v_c_801_, 2);
v_value_817_ = lean_ctor_get(v_decl_815_, 4);
lean_inc_ref(v_value_817_);
lean_dec_ref(v_decl_815_);
v___x_818_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_800_, v_value_817_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_dec_ref_known(v___x_818_, 1);
v_c_801_ = v_k_816_;
goto _start;
}
else
{
lean_dec_ref(v_k_816_);
return v___x_818_;
}
}
case 2:
{
lean_object* v_decl_820_; lean_object* v_k_821_; lean_object* v_value_822_; lean_object* v___x_823_; 
v_decl_820_ = lean_ctor_get(v_c_801_, 0);
lean_inc_ref(v_decl_820_);
v_k_821_ = lean_ctor_get(v_c_801_, 1);
lean_inc_ref(v_k_821_);
lean_dec_ref_known(v_c_801_, 2);
v_value_822_ = lean_ctor_get(v_decl_820_, 4);
lean_inc_ref(v_value_822_);
lean_dec_ref(v_decl_820_);
v___x_823_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_800_, v_value_822_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_dec_ref_known(v___x_823_, 1);
v_c_801_ = v_k_821_;
goto _start;
}
else
{
lean_dec_ref(v_k_821_);
return v___x_823_;
}
}
case 4:
{
lean_object* v_cases_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_847_; 
v_cases_825_ = lean_ctor_get(v_c_801_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v_c_801_);
if (v_isSharedCheck_847_ == 0)
{
v___x_827_ = v_c_801_;
v_isShared_828_ = v_isSharedCheck_847_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_cases_825_);
lean_dec(v_c_801_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_847_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_alts_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_alts_829_ = lean_ctor_get(v_cases_825_, 3);
lean_inc_ref(v_alts_829_);
lean_dec_ref(v_cases_825_);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_array_get_size(v_alts_829_);
v___x_832_ = lean_box(0);
v___x_833_ = lean_nat_dec_lt(v___x_830_, v___x_831_);
if (v___x_833_ == 0)
{
lean_object* v___x_835_; 
lean_dec_ref(v_alts_829_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 0);
lean_ctor_set(v___x_827_, 0, v___x_832_);
v___x_835_ = v___x_827_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_832_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
uint8_t v___x_837_; 
v___x_837_ = lean_nat_dec_le(v___x_831_, v___x_831_);
if (v___x_837_ == 0)
{
if (v___x_833_ == 0)
{
lean_object* v___x_839_; 
lean_dec_ref(v_alts_829_);
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 0);
lean_ctor_set(v___x_827_, 0, v___x_832_);
v___x_839_ = v___x_827_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_832_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; 
lean_del_object(v___x_827_);
v___x_841_ = ((size_t)0ULL);
v___x_842_ = lean_usize_of_nat(v___x_831_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_800_, v_alts_829_, v___x_841_, v___x_842_, v___x_832_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec_ref(v_alts_829_);
return v___x_843_;
}
}
else
{
size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
lean_del_object(v___x_827_);
v___x_844_ = ((size_t)0ULL);
v___x_845_ = lean_usize_of_nat(v___x_831_);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_800_, v_alts_829_, v___x_844_, v___x_845_, v___x_832_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec_ref(v_alts_829_);
return v___x_846_;
}
}
}
}
case 7:
{
lean_object* v_k_848_; 
v_k_848_ = lean_ctor_get(v_c_801_, 3);
lean_inc_ref(v_k_848_);
lean_dec_ref_known(v_c_801_, 4);
v_c_801_ = v_k_848_;
goto _start;
}
case 8:
{
lean_object* v_k_850_; 
v_k_850_ = lean_ctor_get(v_c_801_, 3);
lean_inc_ref(v_k_850_);
lean_dec_ref_known(v_c_801_, 4);
v_c_801_ = v_k_850_;
goto _start;
}
case 9:
{
lean_object* v_k_852_; 
v_k_852_ = lean_ctor_get(v_c_801_, 5);
lean_inc_ref(v_k_852_);
lean_dec_ref_known(v_c_801_, 6);
v_c_801_ = v_k_852_;
goto _start;
}
case 10:
{
lean_object* v_k_854_; 
v_k_854_ = lean_ctor_get(v_c_801_, 2);
lean_inc_ref(v_k_854_);
lean_dec_ref_known(v_c_801_, 3);
v_c_801_ = v_k_854_;
goto _start;
}
case 11:
{
lean_object* v_k_856_; 
v_k_856_ = lean_ctor_get(v_c_801_, 2);
lean_inc_ref(v_k_856_);
lean_dec_ref_known(v_c_801_, 3);
v_c_801_ = v_k_856_;
goto _start;
}
case 12:
{
lean_object* v_k_858_; 
v_k_858_ = lean_ctor_get(v_c_801_, 3);
lean_inc_ref(v_k_858_);
lean_dec_ref_known(v_c_801_, 4);
v_c_801_ = v_k_858_;
goto _start;
}
case 13:
{
lean_object* v_k_860_; 
v_k_860_ = lean_ctor_get(v_c_801_, 1);
lean_inc_ref(v_k_860_);
lean_dec_ref_known(v_c_801_, 2);
v_c_801_ = v_k_860_;
goto _start;
}
default: 
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec_ref(v_c_801_);
v___x_862_ = lean_box(0);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(uint8_t v_pu_864_, lean_object* v_as_865_, size_t v_i_866_, size_t v_stop_867_, lean_object* v_b_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___y_876_; uint8_t v___x_882_; 
v___x_882_ = lean_usize_dec_eq(v_i_866_, v_stop_867_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = lean_array_uget_borrowed(v_as_865_, v_i_866_);
switch(lean_obj_tag(v___x_883_))
{
case 0:
{
lean_object* v_code_884_; 
v_code_884_ = lean_ctor_get(v___x_883_, 2);
lean_inc_ref(v_code_884_);
v___y_876_ = v_code_884_;
goto v___jp_875_;
}
case 1:
{
lean_object* v_code_885_; 
v_code_885_ = lean_ctor_get(v___x_883_, 1);
lean_inc_ref(v_code_885_);
v___y_876_ = v_code_885_;
goto v___jp_875_;
}
default: 
{
lean_object* v_code_886_; 
v_code_886_ = lean_ctor_get(v___x_883_, 0);
lean_inc_ref(v_code_886_);
v___y_876_ = v_code_886_;
goto v___jp_875_;
}
}
}
else
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v_b_868_);
return v___x_887_;
}
v___jp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_864_, v___y_876_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; size_t v___x_879_; size_t v___x_880_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_add(v_i_866_, v___x_879_);
v_i_866_ = v___x_880_;
v_b_868_ = v_a_878_;
goto _start;
}
else
{
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0___boxed(lean_object* v_pu_888_, lean_object* v_as_889_, lean_object* v_i_890_, lean_object* v_stop_891_, lean_object* v_b_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
uint8_t v_pu_boxed_899_; size_t v_i_boxed_900_; size_t v_stop_boxed_901_; lean_object* v_res_902_; 
v_pu_boxed_899_ = lean_unbox(v_pu_888_);
v_i_boxed_900_ = lean_unbox_usize(v_i_890_);
lean_dec(v_i_890_);
v_stop_boxed_901_ = lean_unbox_usize(v_stop_891_);
lean_dec(v_stop_891_);
v_res_902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_boxed_899_, v_as_889_, v_i_boxed_900_, v_stop_boxed_901_, v_b_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v_as_889_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed(lean_object* v_pu_903_, lean_object* v_c_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
uint8_t v_pu_boxed_911_; lean_object* v_res_912_; 
v_pu_boxed_911_ = lean_unbox(v_pu_903_);
v_res_912_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_boxed_911_, v_c_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(lean_object* v_f_913_, lean_object* v_v_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
if (lean_obj_tag(v_v_914_) == 0)
{
lean_object* v_code_921_; lean_object* v___x_922_; 
v_code_921_ = lean_ctor_get(v_v_914_, 0);
lean_inc_ref(v_code_921_);
lean_dec_ref_known(v_v_914_, 1);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
v___x_922_ = lean_apply_7(v_f_913_, v_code_921_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, lean_box(0));
return v___x_922_;
}
else
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v_f_913_);
v_isSharedCheck_930_ = !lean_is_exclusive(v_v_914_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_v_914_, 0);
lean_dec(v_unused_931_);
v___x_924_ = v_v_914_;
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
else
{
lean_dec(v_v_914_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_930_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_box(0);
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 0);
lean_ctor_set(v___x_924_, 0, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg___boxed(lean_object* v_f_932_, lean_object* v_v_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_932_, v_v_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(uint8_t v_pu_941_, lean_object* v_f_942_, lean_object* v_v_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_942_, v_v_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___boxed(lean_object* v_pu_951_, lean_object* v_f_952_, lean_object* v_v_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
uint8_t v_pu_boxed_960_; lean_object* v_res_961_; 
v_pu_boxed_960_ = lean_unbox(v_pu_951_);
v_res_961_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(v_pu_boxed_960_, v_f_952_, v_v_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(uint8_t v_pu_962_, lean_object* v_as_963_, size_t v_i_964_, size_t v_stop_965_, lean_object* v_b_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = lean_usize_dec_eq(v_i_964_, v_stop_965_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v_value_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_974_ = lean_array_uget_borrowed(v_as_963_, v_i_964_);
v_value_975_ = lean_ctor_get(v___x_974_, 1);
v___x_976_ = lean_box(v_pu_962_);
v___x_977_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed), 8, 1);
lean_closure_set(v___x_977_, 0, v___x_976_);
lean_inc_ref(v_value_975_);
v___x_978_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v___x_977_, v_value_975_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; size_t v___x_980_; size_t v___x_981_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_add(v_i_964_, v___x_980_);
v_i_964_ = v___x_981_;
v_b_966_ = v_a_979_;
goto _start;
}
else
{
return v___x_978_;
}
}
else
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_b_966_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1___boxed(lean_object* v_pu_984_, lean_object* v_as_985_, lean_object* v_i_986_, lean_object* v_stop_987_, lean_object* v_b_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
uint8_t v_pu_boxed_995_; size_t v_i_boxed_996_; size_t v_stop_boxed_997_; lean_object* v_res_998_; 
v_pu_boxed_995_ = lean_unbox(v_pu_984_);
v_i_boxed_996_ = lean_unbox_usize(v_i_986_);
lean_dec(v_i_986_);
v_stop_boxed_997_ = lean_unbox_usize(v_stop_987_);
lean_dec(v_stop_987_);
v_res_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_boxed_995_, v_as_985_, v_i_boxed_996_, v_stop_boxed_997_, v_b_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v_as_985_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(uint8_t v_pu_999_, lean_object* v_decls_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_array_get_size(v_decls_1000_);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_nat_dec_lt(v___x_1007_, v___x_1008_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
return v___x_1011_;
}
else
{
uint8_t v___x_1012_; 
v___x_1012_ = lean_nat_dec_le(v___x_1008_, v___x_1008_);
if (v___x_1012_ == 0)
{
if (v___x_1010_ == 0)
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1009_);
return v___x_1013_;
}
else
{
size_t v___x_1014_; size_t v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = ((size_t)0ULL);
v___x_1015_ = lean_usize_of_nat(v___x_1008_);
v___x_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_999_, v_decls_1000_, v___x_1014_, v___x_1015_, v___x_1009_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
return v___x_1016_;
}
}
else
{
size_t v___x_1017_; size_t v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = ((size_t)0ULL);
v___x_1018_ = lean_usize_of_nat(v___x_1008_);
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_999_, v_decls_1000_, v___x_1017_, v___x_1018_, v___x_1009_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start___boxed(lean_object* v_pu_1020_, lean_object* v_decls_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
uint8_t v_pu_boxed_1028_; lean_object* v_res_1029_; 
v_pu_boxed_1028_ = lean_unbox(v_pu_1020_);
v_res_1029_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_boxed_1028_, v_decls_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_decls_1021_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues(uint8_t v_pu_1032_, lean_object* v_decls_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0));
v___x_1040_ = lean_st_mk_ref(v___x_1039_);
v___x_1041_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_1032_, v_decls_1033_, v___x_1040_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v___x_1041_, 0);
lean_dec(v_unused_1050_);
v___x_1043_ = v___x_1041_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_dec(v___x_1041_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_st_ref_get(v___x_1040_);
lean_dec(v___x_1040_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1045_);
v___x_1047_ = v___x_1043_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v___x_1040_);
v_a_1051_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1041_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1041_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues___boxed(lean_object* v_pu_1059_, lean_object* v_decls_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
uint8_t v_pu_boxed_1066_; lean_object* v_res_1067_; 
v_pu_boxed_1066_ = lean_unbox(v_pu_1059_);
v_res_1067_ = l_Lean_Compiler_LCNF_Probe_getLetValues(v_pu_boxed_1066_, v_decls_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec_ref(v_decls_1060_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(uint8_t v_pu_1068_, lean_object* v_code_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
switch(lean_obj_tag(v_code_1069_))
{
case 0:
{
lean_object* v_k_1076_; 
v_k_1076_ = lean_ctor_get(v_code_1069_, 1);
lean_inc_ref(v_k_1076_);
lean_dec_ref_known(v_code_1069_, 2);
v_code_1069_ = v_k_1076_;
goto _start;
}
case 1:
{
lean_object* v_decl_1078_; lean_object* v_k_1079_; lean_object* v_value_1080_; lean_object* v___x_1081_; 
v_decl_1078_ = lean_ctor_get(v_code_1069_, 0);
lean_inc_ref(v_decl_1078_);
v_k_1079_ = lean_ctor_get(v_code_1069_, 1);
lean_inc_ref(v_k_1079_);
lean_dec_ref_known(v_code_1069_, 2);
v_value_1080_ = lean_ctor_get(v_decl_1078_, 4);
lean_inc_ref(v_value_1080_);
lean_dec_ref(v_decl_1078_);
v___x_1081_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1068_, v_value_1080_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_dec_ref_known(v___x_1081_, 1);
v_code_1069_ = v_k_1079_;
goto _start;
}
else
{
lean_dec_ref(v_k_1079_);
return v___x_1081_;
}
}
case 2:
{
lean_object* v_decl_1083_; lean_object* v_k_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v_value_1088_; lean_object* v___x_1089_; 
v_decl_1083_ = lean_ctor_get(v_code_1069_, 0);
lean_inc_ref_n(v_decl_1083_, 2);
v_k_1084_ = lean_ctor_get(v_code_1069_, 1);
lean_inc_ref(v_k_1084_);
lean_dec_ref_known(v_code_1069_, 2);
v___x_1085_ = lean_st_ref_take(v_a_1070_);
v___x_1086_ = lean_array_push(v___x_1085_, v_decl_1083_);
v___x_1087_ = lean_st_ref_put(v_a_1070_, v___x_1086_);
v_value_1088_ = lean_ctor_get(v_decl_1083_, 4);
lean_inc_ref(v_value_1088_);
lean_dec_ref(v_decl_1083_);
v___x_1089_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1068_, v_value_1088_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_dec_ref_known(v___x_1089_, 1);
v_code_1069_ = v_k_1084_;
goto _start;
}
else
{
lean_dec_ref(v_k_1084_);
return v___x_1089_;
}
}
case 4:
{
lean_object* v_cases_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1113_; 
v_cases_1091_ = lean_ctor_get(v_code_1069_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_code_1069_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1093_ = v_code_1069_;
v_isShared_1094_ = v_isSharedCheck_1113_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_cases_1091_);
lean_dec(v_code_1069_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1113_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_alts_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_alts_1095_ = lean_ctor_get(v_cases_1091_, 3);
lean_inc_ref(v_alts_1095_);
lean_dec_ref(v_cases_1091_);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = lean_array_get_size(v_alts_1095_);
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_nat_dec_lt(v___x_1096_, v___x_1097_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1101_; 
lean_dec_ref(v_alts_1095_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1098_);
v___x_1101_ = v___x_1093_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1098_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
else
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_nat_dec_le(v___x_1097_, v___x_1097_);
if (v___x_1103_ == 0)
{
if (v___x_1099_ == 0)
{
lean_object* v___x_1105_; 
lean_dec_ref(v_alts_1095_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1098_);
v___x_1105_ = v___x_1093_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1098_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
else
{
size_t v___x_1107_; size_t v___x_1108_; lean_object* v___x_1109_; 
lean_del_object(v___x_1093_);
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = lean_usize_of_nat(v___x_1097_);
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1068_, v_alts_1095_, v___x_1107_, v___x_1108_, v___x_1098_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec_ref(v_alts_1095_);
return v___x_1109_;
}
}
else
{
size_t v___x_1110_; size_t v___x_1111_; lean_object* v___x_1112_; 
lean_del_object(v___x_1093_);
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = lean_usize_of_nat(v___x_1097_);
v___x_1112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1068_, v_alts_1095_, v___x_1110_, v___x_1111_, v___x_1098_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec_ref(v_alts_1095_);
return v___x_1112_;
}
}
}
}
case 7:
{
lean_object* v_k_1114_; 
v_k_1114_ = lean_ctor_get(v_code_1069_, 3);
lean_inc_ref(v_k_1114_);
lean_dec_ref_known(v_code_1069_, 4);
v_code_1069_ = v_k_1114_;
goto _start;
}
case 8:
{
lean_object* v_k_1116_; 
v_k_1116_ = lean_ctor_get(v_code_1069_, 3);
lean_inc_ref(v_k_1116_);
lean_dec_ref_known(v_code_1069_, 4);
v_code_1069_ = v_k_1116_;
goto _start;
}
case 9:
{
lean_object* v_k_1118_; 
v_k_1118_ = lean_ctor_get(v_code_1069_, 5);
lean_inc_ref(v_k_1118_);
lean_dec_ref_known(v_code_1069_, 6);
v_code_1069_ = v_k_1118_;
goto _start;
}
case 10:
{
lean_object* v_k_1120_; 
v_k_1120_ = lean_ctor_get(v_code_1069_, 2);
lean_inc_ref(v_k_1120_);
lean_dec_ref_known(v_code_1069_, 3);
v_code_1069_ = v_k_1120_;
goto _start;
}
case 11:
{
lean_object* v_k_1122_; 
v_k_1122_ = lean_ctor_get(v_code_1069_, 2);
lean_inc_ref(v_k_1122_);
lean_dec_ref_known(v_code_1069_, 3);
v_code_1069_ = v_k_1122_;
goto _start;
}
case 12:
{
lean_object* v_k_1124_; 
v_k_1124_ = lean_ctor_get(v_code_1069_, 3);
lean_inc_ref(v_k_1124_);
lean_dec_ref_known(v_code_1069_, 4);
v_code_1069_ = v_k_1124_;
goto _start;
}
case 13:
{
lean_object* v_k_1126_; 
v_k_1126_ = lean_ctor_get(v_code_1069_, 1);
lean_inc_ref(v_k_1126_);
lean_dec_ref_known(v_code_1069_, 2);
v_code_1069_ = v_k_1126_;
goto _start;
}
default: 
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_dec_ref(v_code_1069_);
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(uint8_t v_pu_1130_, lean_object* v_as_1131_, size_t v_i_1132_, size_t v_stop_1133_, lean_object* v_b_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___y_1142_; uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_eq(v_i_1132_, v_stop_1133_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_array_uget_borrowed(v_as_1131_, v_i_1132_);
switch(lean_obj_tag(v___x_1149_))
{
case 0:
{
lean_object* v_code_1150_; 
v_code_1150_ = lean_ctor_get(v___x_1149_, 2);
lean_inc_ref(v_code_1150_);
v___y_1142_ = v_code_1150_;
goto v___jp_1141_;
}
case 1:
{
lean_object* v_code_1151_; 
v_code_1151_ = lean_ctor_get(v___x_1149_, 1);
lean_inc_ref(v_code_1151_);
v___y_1142_ = v_code_1151_;
goto v___jp_1141_;
}
default: 
{
lean_object* v_code_1152_; 
v_code_1152_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref(v_code_1152_);
v___y_1142_ = v_code_1152_;
goto v___jp_1141_;
}
}
}
else
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_b_1134_);
return v___x_1153_;
}
v___jp_1141_:
{
lean_object* v___x_1143_; 
v___x_1143_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1130_, v___y_1142_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; size_t v___x_1145_; size_t v___x_1146_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_add(v_i_1132_, v___x_1145_);
v_i_1132_ = v___x_1146_;
v_b_1134_ = v_a_1144_;
goto _start;
}
else
{
return v___x_1143_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0___boxed(lean_object* v_pu_1154_, lean_object* v_as_1155_, lean_object* v_i_1156_, lean_object* v_stop_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v_pu_boxed_1165_; size_t v_i_boxed_1166_; size_t v_stop_boxed_1167_; lean_object* v_res_1168_; 
v_pu_boxed_1165_ = lean_unbox(v_pu_1154_);
v_i_boxed_1166_ = lean_unbox_usize(v_i_1156_);
lean_dec(v_i_1156_);
v_stop_boxed_1167_ = lean_unbox_usize(v_stop_1157_);
lean_dec(v_stop_1157_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_boxed_1165_, v_as_1155_, v_i_boxed_1166_, v_stop_boxed_1167_, v_b_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v_as_1155_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed(lean_object* v_pu_1169_, lean_object* v_code_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
uint8_t v_pu_boxed_1177_; lean_object* v_res_1178_; 
v_pu_boxed_1177_ = lean_unbox(v_pu_1169_);
v_res_1178_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_boxed_1177_, v_code_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(lean_object* v_f_1179_, lean_object* v_v_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
if (lean_obj_tag(v_v_1180_) == 0)
{
lean_object* v_code_1187_; lean_object* v___x_1188_; 
v_code_1187_ = lean_ctor_get(v_v_1180_, 0);
lean_inc_ref(v_code_1187_);
lean_dec_ref_known(v_v_1180_, 1);
lean_inc(v___y_1185_);
lean_inc_ref(v___y_1184_);
lean_inc(v___y_1183_);
lean_inc_ref(v___y_1182_);
lean_inc(v___y_1181_);
v___x_1188_ = lean_apply_7(v_f_1179_, v_code_1187_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, lean_box(0));
return v___x_1188_;
}
else
{
lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_f_1179_);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_v_1180_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; 
v_unused_1197_ = lean_ctor_get(v_v_1180_, 0);
lean_dec(v_unused_1197_);
v___x_1190_ = v_v_1180_;
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v_v_1180_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_box(0);
if (v_isShared_1191_ == 0)
{
lean_ctor_set_tag(v___x_1190_, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg___boxed(lean_object* v_f_1198_, lean_object* v_v_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1198_, v_v_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(uint8_t v_pu_1207_, lean_object* v_f_1208_, lean_object* v_v_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1208_, v_v_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___boxed(lean_object* v_pu_1217_, lean_object* v_f_1218_, lean_object* v_v_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
uint8_t v_pu_boxed_1226_; lean_object* v_res_1227_; 
v_pu_boxed_1226_ = lean_unbox(v_pu_1217_);
v_res_1227_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(v_pu_boxed_1226_, v_f_1218_, v_v_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(uint8_t v_pu_1228_, lean_object* v_as_1229_, size_t v_i_1230_, size_t v_stop_1231_, lean_object* v_b_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_usize_dec_eq(v_i_1230_, v_stop_1231_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v_value_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1240_ = lean_array_uget_borrowed(v_as_1229_, v_i_1230_);
v_value_1241_ = lean_ctor_get(v___x_1240_, 1);
v___x_1242_ = lean_box(v_pu_1228_);
v___x_1243_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed), 8, 1);
lean_closure_set(v___x_1243_, 0, v___x_1242_);
lean_inc_ref(v_value_1241_);
v___x_1244_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v___x_1243_, v_value_1241_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; size_t v___x_1246_; size_t v___x_1247_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = ((size_t)1ULL);
v___x_1247_ = lean_usize_add(v_i_1230_, v___x_1246_);
v_i_1230_ = v___x_1247_;
v_b_1232_ = v_a_1245_;
goto _start;
}
else
{
return v___x_1244_;
}
}
else
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_b_1232_);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1___boxed(lean_object* v_pu_1250_, lean_object* v_as_1251_, lean_object* v_i_1252_, lean_object* v_stop_1253_, lean_object* v_b_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
uint8_t v_pu_boxed_1261_; size_t v_i_boxed_1262_; size_t v_stop_boxed_1263_; lean_object* v_res_1264_; 
v_pu_boxed_1261_ = lean_unbox(v_pu_1250_);
v_i_boxed_1262_ = lean_unbox_usize(v_i_1252_);
lean_dec(v_i_1252_);
v_stop_boxed_1263_ = lean_unbox_usize(v_stop_1253_);
lean_dec(v_stop_1253_);
v_res_1264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_boxed_1261_, v_as_1251_, v_i_boxed_1262_, v_stop_boxed_1263_, v_b_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v_as_1251_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(uint8_t v_pu_1265_, lean_object* v_decls_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_array_get_size(v_decls_1266_);
v___x_1275_ = lean_box(0);
v___x_1276_ = lean_nat_dec_lt(v___x_1273_, v___x_1274_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1275_);
return v___x_1277_;
}
else
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_nat_dec_le(v___x_1274_, v___x_1274_);
if (v___x_1278_ == 0)
{
if (v___x_1276_ == 0)
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1275_);
return v___x_1279_;
}
else
{
size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = ((size_t)0ULL);
v___x_1281_ = lean_usize_of_nat(v___x_1274_);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1265_, v_decls_1266_, v___x_1280_, v___x_1281_, v___x_1275_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
return v___x_1282_;
}
}
else
{
size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = ((size_t)0ULL);
v___x_1284_ = lean_usize_of_nat(v___x_1274_);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1265_, v_decls_1266_, v___x_1283_, v___x_1284_, v___x_1275_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start___boxed(lean_object* v_pu_1286_, lean_object* v_decls_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
uint8_t v_pu_boxed_1294_; lean_object* v_res_1295_; 
v_pu_boxed_1294_ = lean_unbox(v_pu_1286_);
v_res_1295_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_boxed_1294_, v_decls_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_decls_1287_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps(uint8_t v_pu_1298_, lean_object* v_decls_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getJps___closed__0));
v___x_1306_ = lean_st_mk_ref(v___x_1305_);
v___x_1307_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_1298_, v_decls_1299_, v___x_1306_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1315_; 
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v___x_1307_, 0);
lean_dec(v_unused_1316_);
v___x_1309_ = v___x_1307_;
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
else
{
lean_dec(v___x_1307_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_st_ref_get(v___x_1306_);
lean_dec(v___x_1306_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
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
lean_dec(v___x_1306_);
v_a_1317_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1307_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1307_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps___boxed(lean_object* v_pu_1325_, lean_object* v_decls_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
uint8_t v_pu_boxed_1332_; lean_object* v_res_1333_; 
v_pu_boxed_1332_ = lean_unbox(v_pu_1325_);
v_res_1333_ = l_Lean_Compiler_LCNF_Probe_getJps(v_pu_boxed_1332_, v_decls_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec_ref(v_decls_1326_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(uint8_t v_pu_1334_, lean_object* v_f_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
switch(lean_obj_tag(v_a_1336_))
{
case 0:
{
lean_object* v_decl_1342_; lean_object* v_k_1343_; lean_object* v___x_1344_; 
v_decl_1342_ = lean_ctor_get(v_a_1336_, 0);
lean_inc_ref(v_decl_1342_);
v_k_1343_ = lean_ctor_get(v_a_1336_, 1);
lean_inc_ref(v_k_1343_);
lean_dec_ref_known(v_a_1336_, 2);
lean_inc_ref(v_f_1335_);
lean_inc(v_a_1340_);
lean_inc_ref(v_a_1339_);
lean_inc(v_a_1338_);
lean_inc_ref(v_a_1337_);
v___x_1344_ = lean_apply_6(v_f_1335_, v_decl_1342_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, lean_box(0));
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; uint8_t v___x_1346_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
v___x_1346_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
if (v___x_1346_ == 0)
{
lean_dec_ref_known(v___x_1344_, 1);
v_a_1336_ = v_k_1343_;
goto _start;
}
else
{
lean_dec_ref(v_k_1343_);
lean_dec_ref(v_f_1335_);
return v___x_1344_;
}
}
else
{
lean_dec_ref(v_k_1343_);
lean_dec_ref(v_f_1335_);
return v___x_1344_;
}
}
case 1:
{
lean_object* v_decl_1348_; lean_object* v_k_1349_; lean_object* v_value_1350_; lean_object* v___x_1351_; 
v_decl_1348_ = lean_ctor_get(v_a_1336_, 0);
lean_inc_ref(v_decl_1348_);
v_k_1349_ = lean_ctor_get(v_a_1336_, 1);
lean_inc_ref(v_k_1349_);
lean_dec_ref_known(v_a_1336_, 2);
v_value_1350_ = lean_ctor_get(v_decl_1348_, 4);
lean_inc_ref(v_value_1350_);
lean_dec_ref(v_decl_1348_);
lean_inc_ref(v_f_1335_);
v___x_1351_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1334_, v_f_1335_, v_value_1350_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; uint8_t v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
v___x_1353_ = lean_unbox(v_a_1352_);
lean_dec(v_a_1352_);
if (v___x_1353_ == 0)
{
lean_dec_ref_known(v___x_1351_, 1);
v_a_1336_ = v_k_1349_;
goto _start;
}
else
{
lean_dec_ref(v_k_1349_);
lean_dec_ref(v_f_1335_);
return v___x_1351_;
}
}
else
{
lean_dec_ref(v_k_1349_);
lean_dec_ref(v_f_1335_);
return v___x_1351_;
}
}
case 2:
{
lean_object* v_decl_1355_; lean_object* v_k_1356_; lean_object* v_value_1357_; lean_object* v___x_1358_; 
v_decl_1355_ = lean_ctor_get(v_a_1336_, 0);
lean_inc_ref(v_decl_1355_);
v_k_1356_ = lean_ctor_get(v_a_1336_, 1);
lean_inc_ref(v_k_1356_);
lean_dec_ref_known(v_a_1336_, 2);
v_value_1357_ = lean_ctor_get(v_decl_1355_, 4);
lean_inc_ref(v_value_1357_);
lean_dec_ref(v_decl_1355_);
lean_inc_ref(v_f_1335_);
v___x_1358_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1334_, v_f_1335_, v_value_1357_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; uint8_t v___x_1360_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
v___x_1360_ = lean_unbox(v_a_1359_);
lean_dec(v_a_1359_);
if (v___x_1360_ == 0)
{
lean_dec_ref_known(v___x_1358_, 1);
v_a_1336_ = v_k_1356_;
goto _start;
}
else
{
lean_dec_ref(v_k_1356_);
lean_dec_ref(v_f_1335_);
return v___x_1358_;
}
}
else
{
lean_dec_ref(v_k_1356_);
lean_dec_ref(v_f_1335_);
return v___x_1358_;
}
}
case 4:
{
lean_object* v_cases_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1381_; 
v_cases_1362_ = lean_ctor_get(v_a_1336_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_a_1336_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1364_ = v_a_1336_;
v_isShared_1365_ = v_isSharedCheck_1381_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_cases_1362_);
lean_dec(v_a_1336_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1381_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_alts_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_alts_1366_ = lean_ctor_get(v_cases_1362_, 3);
lean_inc_ref(v_alts_1366_);
lean_dec_ref(v_cases_1362_);
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_array_get_size(v_alts_1366_);
v___x_1369_ = lean_nat_dec_lt(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_dec_ref(v_alts_1366_);
lean_dec_ref(v_f_1335_);
v___x_1370_ = lean_box(v___x_1369_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set_tag(v___x_1364_, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1370_);
v___x_1372_ = v___x_1364_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
else
{
if (v___x_1369_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_dec_ref(v_alts_1366_);
lean_dec_ref(v_f_1335_);
v___x_1374_ = lean_box(v___x_1369_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set_tag(v___x_1364_, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1374_);
v___x_1376_ = v___x_1364_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
else
{
size_t v___x_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
lean_del_object(v___x_1364_);
v___x_1378_ = ((size_t)0ULL);
v___x_1379_ = lean_usize_of_nat(v___x_1368_);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_1334_, v_f_1335_, v_alts_1366_, v___x_1378_, v___x_1379_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec_ref(v_alts_1366_);
return v___x_1380_;
}
}
}
}
case 7:
{
lean_object* v_k_1382_; 
v_k_1382_ = lean_ctor_get(v_a_1336_, 3);
lean_inc_ref(v_k_1382_);
lean_dec_ref_known(v_a_1336_, 4);
v_a_1336_ = v_k_1382_;
goto _start;
}
case 8:
{
lean_object* v_k_1384_; 
v_k_1384_ = lean_ctor_get(v_a_1336_, 3);
lean_inc_ref(v_k_1384_);
lean_dec_ref_known(v_a_1336_, 4);
v_a_1336_ = v_k_1384_;
goto _start;
}
case 9:
{
lean_object* v_k_1386_; 
v_k_1386_ = lean_ctor_get(v_a_1336_, 5);
lean_inc_ref(v_k_1386_);
lean_dec_ref_known(v_a_1336_, 6);
v_a_1336_ = v_k_1386_;
goto _start;
}
case 10:
{
lean_object* v_k_1388_; 
v_k_1388_ = lean_ctor_get(v_a_1336_, 2);
lean_inc_ref(v_k_1388_);
lean_dec_ref_known(v_a_1336_, 3);
v_a_1336_ = v_k_1388_;
goto _start;
}
case 11:
{
lean_object* v_k_1390_; 
v_k_1390_ = lean_ctor_get(v_a_1336_, 2);
lean_inc_ref(v_k_1390_);
lean_dec_ref_known(v_a_1336_, 3);
v_a_1336_ = v_k_1390_;
goto _start;
}
case 12:
{
lean_object* v_k_1392_; 
v_k_1392_ = lean_ctor_get(v_a_1336_, 3);
lean_inc_ref(v_k_1392_);
lean_dec_ref_known(v_a_1336_, 4);
v_a_1336_ = v_k_1392_;
goto _start;
}
case 13:
{
lean_object* v_k_1394_; 
v_k_1394_ = lean_ctor_get(v_a_1336_, 1);
lean_inc_ref(v_k_1394_);
lean_dec_ref_known(v_a_1336_, 2);
v_a_1336_ = v_k_1394_;
goto _start;
}
default: 
{
uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec_ref(v_a_1336_);
lean_dec_ref(v_f_1335_);
v___x_1396_ = 0;
v___x_1397_ = lean_box(v___x_1396_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(uint8_t v_pu_1399_, lean_object* v_f_1400_, lean_object* v_as_1401_, size_t v_i_1402_, size_t v_stop_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_usize_dec_eq(v_i_1402_, v_stop_1403_);
if (v___x_1409_ == 0)
{
uint8_t v___x_1410_; lean_object* v___y_1412_; lean_object* v___x_1427_; 
v___x_1410_ = 1;
v___x_1427_ = lean_array_uget_borrowed(v_as_1401_, v_i_1402_);
switch(lean_obj_tag(v___x_1427_))
{
case 0:
{
lean_object* v_code_1428_; 
v_code_1428_ = lean_ctor_get(v___x_1427_, 2);
lean_inc_ref(v_code_1428_);
v___y_1412_ = v_code_1428_;
goto v___jp_1411_;
}
case 1:
{
lean_object* v_code_1429_; 
v_code_1429_ = lean_ctor_get(v___x_1427_, 1);
lean_inc_ref(v_code_1429_);
v___y_1412_ = v_code_1429_;
goto v___jp_1411_;
}
default: 
{
lean_object* v_code_1430_; 
v_code_1430_ = lean_ctor_get(v___x_1427_, 0);
lean_inc_ref(v_code_1430_);
v___y_1412_ = v_code_1430_;
goto v___jp_1411_;
}
}
v___jp_1411_:
{
lean_object* v___x_1413_; 
lean_inc_ref(v_f_1400_);
v___x_1413_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1399_, v_f_1400_, v___y_1412_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1426_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1426_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1426_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_unbox(v_a_1414_);
lean_dec(v_a_1414_);
if (v___x_1418_ == 0)
{
size_t v___x_1419_; size_t v___x_1420_; 
lean_del_object(v___x_1416_);
v___x_1419_ = ((size_t)1ULL);
v___x_1420_ = lean_usize_add(v_i_1402_, v___x_1419_);
v_i_1402_ = v___x_1420_;
goto _start;
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_dec_ref(v_f_1400_);
v___x_1422_ = lean_box(v___x_1410_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1422_);
v___x_1424_ = v___x_1416_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_dec_ref(v_f_1400_);
return v___x_1413_;
}
}
}
else
{
uint8_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec_ref(v_f_1400_);
v___x_1431_ = 0;
v___x_1432_ = lean_box(v___x_1431_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0___boxed(lean_object* v_pu_1434_, lean_object* v_f_1435_, lean_object* v_as_1436_, lean_object* v_i_1437_, lean_object* v_stop_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
uint8_t v_pu_boxed_1444_; size_t v_i_boxed_1445_; size_t v_stop_boxed_1446_; lean_object* v_res_1447_; 
v_pu_boxed_1444_ = lean_unbox(v_pu_1434_);
v_i_boxed_1445_ = lean_unbox_usize(v_i_1437_);
lean_dec(v_i_1437_);
v_stop_boxed_1446_ = lean_unbox_usize(v_stop_1438_);
lean_dec(v_stop_1438_);
v_res_1447_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_boxed_1444_, v_f_1435_, v_as_1436_, v_i_boxed_1445_, v_stop_boxed_1446_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec_ref(v_as_1436_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed(lean_object* v_pu_1448_, lean_object* v_f_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
uint8_t v_pu_boxed_1456_; lean_object* v_res_1457_; 
v_pu_boxed_1456_ = lean_unbox(v_pu_1448_);
v_res_1457_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_boxed_1456_, v_f_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(lean_object* v_v_1458_, lean_object* v_f_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
if (lean_obj_tag(v_v_1458_) == 0)
{
lean_object* v_code_1465_; lean_object* v___x_1466_; 
v_code_1465_ = lean_ctor_get(v_v_1458_, 0);
lean_inc_ref(v_code_1465_);
lean_dec_ref_known(v_v_1458_, 1);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
v___x_1466_ = lean_apply_6(v_f_1459_, v_code_1465_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, lean_box(0));
return v___x_1466_;
}
else
{
lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v_f_1459_);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_v_1458_);
if (v_isSharedCheck_1475_ == 0)
{
lean_object* v_unused_1476_; 
v_unused_1476_ = lean_ctor_get(v_v_1458_, 0);
lean_dec(v_unused_1476_);
v___x_1468_ = v_v_1458_;
v_isShared_1469_ = v_isSharedCheck_1475_;
goto v_resetjp_1467_;
}
else
{
lean_dec(v_v_1458_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1475_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
uint8_t v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1470_ = 0;
v___x_1471_ = lean_box(v___x_1470_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set_tag(v___x_1468_, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1471_);
v___x_1473_ = v___x_1468_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg___boxed(lean_object* v_v_1477_, lean_object* v_f_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1477_, v_f_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(uint8_t v_pu_1485_, lean_object* v_v_1486_, lean_object* v_f_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1486_, v_f_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___boxed(lean_object* v_pu_1494_, lean_object* v_v_1495_, lean_object* v_f_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_pu_boxed_1502_; lean_object* v_res_1503_; 
v_pu_boxed_1502_ = lean_unbox(v_pu_1494_);
v_res_1503_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(v_pu_boxed_1502_, v_v_1495_, v_f_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(uint8_t v_pu_1504_, lean_object* v_f_1505_, lean_object* v_as_1506_, size_t v_i_1507_, size_t v_stop_1508_, lean_object* v_b_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_eq(v_i_1507_, v_stop_1508_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v_value_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1516_ = lean_array_uget_borrowed(v_as_1506_, v_i_1507_);
v_value_1517_ = lean_ctor_get(v___x_1516_, 1);
v___x_1518_ = lean_box(v_pu_1504_);
lean_inc_ref(v_f_1505_);
v___x_1519_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed), 8, 2);
lean_closure_set(v___x_1519_, 0, v___x_1518_);
lean_closure_set(v___x_1519_, 1, v_f_1505_);
lean_inc_ref(v_value_1517_);
v___x_1520_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1517_, v___x_1519_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_a_1523_; uint8_t v___x_1527_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v___x_1527_ = lean_unbox(v_a_1521_);
lean_dec(v_a_1521_);
if (v___x_1527_ == 0)
{
v_a_1523_ = v_b_1509_;
goto v___jp_1522_;
}
else
{
lean_object* v___x_1528_; 
lean_inc(v___x_1516_);
v___x_1528_ = lean_array_push(v_b_1509_, v___x_1516_);
v_a_1523_ = v___x_1528_;
goto v___jp_1522_;
}
v___jp_1522_:
{
size_t v___x_1524_; size_t v___x_1525_; 
v___x_1524_ = ((size_t)1ULL);
v___x_1525_ = lean_usize_add(v_i_1507_, v___x_1524_);
v_i_1507_ = v___x_1525_;
v_b_1509_ = v_a_1523_;
goto _start;
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec_ref(v_b_1509_);
lean_dec_ref(v_f_1505_);
v_a_1529_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1520_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1520_);
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
lean_object* v___x_1537_; 
lean_dec_ref(v_f_1505_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_b_1509_);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1___boxed(lean_object* v_pu_1538_, lean_object* v_f_1539_, lean_object* v_as_1540_, lean_object* v_i_1541_, lean_object* v_stop_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v_pu_boxed_1549_; size_t v_i_boxed_1550_; size_t v_stop_boxed_1551_; lean_object* v_res_1552_; 
v_pu_boxed_1549_ = lean_unbox(v_pu_1538_);
v_i_boxed_1550_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_stop_boxed_1551_ = lean_unbox_usize(v_stop_1542_);
lean_dec(v_stop_1542_);
v_res_1552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_boxed_1549_, v_f_1539_, v_as_1540_, v_i_boxed_1550_, v_stop_boxed_1551_, v_b_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_as_1540_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet(uint8_t v_pu_1555_, lean_object* v_f_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_array_get_size(v_a_1557_);
v___x_1565_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1566_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; 
lean_dec_ref(v_f_1556_);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
return v___x_1567_;
}
else
{
size_t v___x_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = lean_usize_of_nat(v___x_1564_);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1555_, v_f_1556_, v_a_1557_, v___x_1568_, v___x_1569_, v___x_1565_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet___boxed(lean_object* v_pu_1571_, lean_object* v_f_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
uint8_t v_pu_boxed_1579_; lean_object* v_res_1580_; 
v_pu_boxed_1579_ = lean_unbox(v_pu_1571_);
v_res_1580_ = l_Lean_Compiler_LCNF_Probe_filterByLet(v_pu_boxed_1579_, v_f_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec_ref(v_a_1573_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(uint8_t v_pu_1581_, lean_object* v_f_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
switch(lean_obj_tag(v_a_1583_))
{
case 0:
{
lean_object* v_k_1589_; 
v_k_1589_ = lean_ctor_get(v_a_1583_, 1);
lean_inc_ref(v_k_1589_);
lean_dec_ref_known(v_a_1583_, 2);
v_a_1583_ = v_k_1589_;
goto _start;
}
case 1:
{
lean_object* v_decl_1591_; lean_object* v_k_1592_; lean_object* v___x_1593_; 
v_decl_1591_ = lean_ctor_get(v_a_1583_, 0);
lean_inc_ref_n(v_decl_1591_, 2);
v_k_1592_ = lean_ctor_get(v_a_1583_, 1);
lean_inc_ref(v_k_1592_);
lean_dec_ref_known(v_a_1583_, 2);
lean_inc_ref(v_f_1582_);
lean_inc(v_a_1587_);
lean_inc_ref(v_a_1586_);
lean_inc(v_a_1585_);
lean_inc_ref(v_a_1584_);
v___x_1593_ = lean_apply_6(v_f_1582_, v_decl_1591_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, lean_box(0));
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; uint8_t v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
v___x_1595_ = lean_unbox(v_a_1594_);
lean_dec(v_a_1594_);
if (v___x_1595_ == 0)
{
lean_object* v_value_1596_; lean_object* v___x_1597_; 
lean_dec_ref_known(v___x_1593_, 1);
v_value_1596_ = lean_ctor_get(v_decl_1591_, 4);
lean_inc_ref(v_value_1596_);
lean_dec_ref(v_decl_1591_);
lean_inc_ref(v_f_1582_);
v___x_1597_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1581_, v_f_1582_, v_value_1596_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; uint8_t v___x_1599_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
v___x_1599_ = lean_unbox(v_a_1598_);
lean_dec(v_a_1598_);
if (v___x_1599_ == 0)
{
lean_dec_ref_known(v___x_1597_, 1);
v_a_1583_ = v_k_1592_;
goto _start;
}
else
{
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_f_1582_);
return v___x_1597_;
}
}
else
{
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_f_1582_);
return v___x_1597_;
}
}
else
{
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_decl_1591_);
lean_dec_ref(v_f_1582_);
return v___x_1593_;
}
}
else
{
lean_dec_ref(v_k_1592_);
lean_dec_ref(v_decl_1591_);
lean_dec_ref(v_f_1582_);
return v___x_1593_;
}
}
case 2:
{
lean_object* v_k_1601_; 
v_k_1601_ = lean_ctor_get(v_a_1583_, 1);
lean_inc_ref(v_k_1601_);
lean_dec_ref_known(v_a_1583_, 2);
v_a_1583_ = v_k_1601_;
goto _start;
}
case 4:
{
lean_object* v_cases_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1622_; 
v_cases_1603_ = lean_ctor_get(v_a_1583_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_a_1583_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1605_ = v_a_1583_;
v_isShared_1606_ = v_isSharedCheck_1622_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_cases_1603_);
lean_dec(v_a_1583_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1622_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v_alts_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v_alts_1607_ = lean_ctor_get(v_cases_1603_, 3);
lean_inc_ref(v_alts_1607_);
lean_dec_ref(v_cases_1603_);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = lean_array_get_size(v_alts_1607_);
v___x_1610_ = lean_nat_dec_lt(v___x_1608_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
lean_dec_ref(v_alts_1607_);
lean_dec_ref(v_f_1582_);
v___x_1611_ = lean_box(v___x_1610_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set_tag(v___x_1605_, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1611_);
v___x_1613_ = v___x_1605_;
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
else
{
if (v___x_1610_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
lean_dec_ref(v_alts_1607_);
lean_dec_ref(v_f_1582_);
v___x_1615_ = lean_box(v___x_1610_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set_tag(v___x_1605_, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1615_);
v___x_1617_ = v___x_1605_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
else
{
size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; 
lean_del_object(v___x_1605_);
v___x_1619_ = ((size_t)0ULL);
v___x_1620_ = lean_usize_of_nat(v___x_1609_);
v___x_1621_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_1581_, v_f_1582_, v_alts_1607_, v___x_1619_, v___x_1620_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec_ref(v_alts_1607_);
return v___x_1621_;
}
}
}
}
case 7:
{
lean_object* v_k_1623_; 
v_k_1623_ = lean_ctor_get(v_a_1583_, 3);
lean_inc_ref(v_k_1623_);
lean_dec_ref_known(v_a_1583_, 4);
v_a_1583_ = v_k_1623_;
goto _start;
}
case 8:
{
lean_object* v_k_1625_; 
v_k_1625_ = lean_ctor_get(v_a_1583_, 3);
lean_inc_ref(v_k_1625_);
lean_dec_ref_known(v_a_1583_, 4);
v_a_1583_ = v_k_1625_;
goto _start;
}
case 9:
{
lean_object* v_k_1627_; 
v_k_1627_ = lean_ctor_get(v_a_1583_, 5);
lean_inc_ref(v_k_1627_);
lean_dec_ref_known(v_a_1583_, 6);
v_a_1583_ = v_k_1627_;
goto _start;
}
case 10:
{
lean_object* v_k_1629_; 
v_k_1629_ = lean_ctor_get(v_a_1583_, 2);
lean_inc_ref(v_k_1629_);
lean_dec_ref_known(v_a_1583_, 3);
v_a_1583_ = v_k_1629_;
goto _start;
}
case 11:
{
lean_object* v_k_1631_; 
v_k_1631_ = lean_ctor_get(v_a_1583_, 2);
lean_inc_ref(v_k_1631_);
lean_dec_ref_known(v_a_1583_, 3);
v_a_1583_ = v_k_1631_;
goto _start;
}
case 12:
{
lean_object* v_k_1633_; 
v_k_1633_ = lean_ctor_get(v_a_1583_, 3);
lean_inc_ref(v_k_1633_);
lean_dec_ref_known(v_a_1583_, 4);
v_a_1583_ = v_k_1633_;
goto _start;
}
case 13:
{
lean_object* v_k_1635_; 
v_k_1635_ = lean_ctor_get(v_a_1583_, 1);
lean_inc_ref(v_k_1635_);
lean_dec_ref_known(v_a_1583_, 2);
v_a_1583_ = v_k_1635_;
goto _start;
}
default: 
{
uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec_ref(v_a_1583_);
lean_dec_ref(v_f_1582_);
v___x_1637_ = 0;
v___x_1638_ = lean_box(v___x_1637_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(uint8_t v_pu_1640_, lean_object* v_f_1641_, lean_object* v_as_1642_, size_t v_i_1643_, size_t v_stop_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_usize_dec_eq(v_i_1643_, v_stop_1644_);
if (v___x_1650_ == 0)
{
uint8_t v___x_1651_; lean_object* v___y_1653_; lean_object* v___x_1668_; 
v___x_1651_ = 1;
v___x_1668_ = lean_array_uget_borrowed(v_as_1642_, v_i_1643_);
switch(lean_obj_tag(v___x_1668_))
{
case 0:
{
lean_object* v_code_1669_; 
v_code_1669_ = lean_ctor_get(v___x_1668_, 2);
lean_inc_ref(v_code_1669_);
v___y_1653_ = v_code_1669_;
goto v___jp_1652_;
}
case 1:
{
lean_object* v_code_1670_; 
v_code_1670_ = lean_ctor_get(v___x_1668_, 1);
lean_inc_ref(v_code_1670_);
v___y_1653_ = v_code_1670_;
goto v___jp_1652_;
}
default: 
{
lean_object* v_code_1671_; 
v_code_1671_ = lean_ctor_get(v___x_1668_, 0);
lean_inc_ref(v_code_1671_);
v___y_1653_ = v_code_1671_;
goto v___jp_1652_;
}
}
v___jp_1652_:
{
lean_object* v___x_1654_; 
lean_inc_ref(v_f_1641_);
v___x_1654_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1640_, v_f_1641_, v___y_1653_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1667_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1667_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1667_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
uint8_t v___x_1659_; 
v___x_1659_ = lean_unbox(v_a_1655_);
lean_dec(v_a_1655_);
if (v___x_1659_ == 0)
{
size_t v___x_1660_; size_t v___x_1661_; 
lean_del_object(v___x_1657_);
v___x_1660_ = ((size_t)1ULL);
v___x_1661_ = lean_usize_add(v_i_1643_, v___x_1660_);
v_i_1643_ = v___x_1661_;
goto _start;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
lean_dec_ref(v_f_1641_);
v___x_1663_ = lean_box(v___x_1651_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1663_);
v___x_1665_ = v___x_1657_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
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
else
{
lean_dec_ref(v_f_1641_);
return v___x_1654_;
}
}
}
else
{
uint8_t v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec_ref(v_f_1641_);
v___x_1672_ = 0;
v___x_1673_ = lean_box(v___x_1672_);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0___boxed(lean_object* v_pu_1675_, lean_object* v_f_1676_, lean_object* v_as_1677_, lean_object* v_i_1678_, lean_object* v_stop_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_pu_boxed_1685_; size_t v_i_boxed_1686_; size_t v_stop_boxed_1687_; lean_object* v_res_1688_; 
v_pu_boxed_1685_ = lean_unbox(v_pu_1675_);
v_i_boxed_1686_ = lean_unbox_usize(v_i_1678_);
lean_dec(v_i_1678_);
v_stop_boxed_1687_ = lean_unbox_usize(v_stop_1679_);
lean_dec(v_stop_1679_);
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_boxed_1685_, v_f_1676_, v_as_1677_, v_i_boxed_1686_, v_stop_boxed_1687_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v_as_1677_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed(lean_object* v_pu_1689_, lean_object* v_f_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
uint8_t v_pu_boxed_1697_; lean_object* v_res_1698_; 
v_pu_boxed_1697_ = lean_unbox(v_pu_1689_);
v_res_1698_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_boxed_1697_, v_f_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
lean_dec(v_a_1695_);
lean_dec_ref(v_a_1694_);
lean_dec(v_a_1693_);
lean_dec_ref(v_a_1692_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(uint8_t v_pu_1699_, lean_object* v_f_1700_, lean_object* v_as_1701_, size_t v_i_1702_, size_t v_stop_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_eq(v_i_1702_, v_stop_1703_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v_value_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1711_ = lean_array_uget_borrowed(v_as_1701_, v_i_1702_);
v_value_1712_ = lean_ctor_get(v___x_1711_, 1);
v___x_1713_ = lean_box(v_pu_1699_);
lean_inc_ref(v_f_1700_);
v___x_1714_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed), 8, 2);
lean_closure_set(v___x_1714_, 0, v___x_1713_);
lean_closure_set(v___x_1714_, 1, v_f_1700_);
lean_inc_ref(v_value_1712_);
v___x_1715_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1712_, v___x_1714_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v_a_1718_; uint8_t v___x_1722_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v___x_1722_ = lean_unbox(v_a_1716_);
lean_dec(v_a_1716_);
if (v___x_1722_ == 0)
{
v_a_1718_ = v_b_1704_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1723_; 
lean_inc(v___x_1711_);
v___x_1723_ = lean_array_push(v_b_1704_, v___x_1711_);
v_a_1718_ = v___x_1723_;
goto v___jp_1717_;
}
v___jp_1717_:
{
size_t v___x_1719_; size_t v___x_1720_; 
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1702_, v___x_1719_);
v_i_1702_ = v___x_1720_;
v_b_1704_ = v_a_1718_;
goto _start;
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v_b_1704_);
lean_dec_ref(v_f_1700_);
v_a_1724_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1715_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1715_);
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
else
{
lean_object* v___x_1732_; 
lean_dec_ref(v_f_1700_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_b_1704_);
return v___x_1732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0___boxed(lean_object* v_pu_1733_, lean_object* v_f_1734_, lean_object* v_as_1735_, lean_object* v_i_1736_, lean_object* v_stop_1737_, lean_object* v_b_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
uint8_t v_pu_boxed_1744_; size_t v_i_boxed_1745_; size_t v_stop_boxed_1746_; lean_object* v_res_1747_; 
v_pu_boxed_1744_ = lean_unbox(v_pu_1733_);
v_i_boxed_1745_ = lean_unbox_usize(v_i_1736_);
lean_dec(v_i_1736_);
v_stop_boxed_1746_ = lean_unbox_usize(v_stop_1737_);
lean_dec(v_stop_1737_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_boxed_1744_, v_f_1734_, v_as_1735_, v_i_boxed_1745_, v_stop_boxed_1746_, v_b_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec_ref(v_as_1735_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun(uint8_t v_pu_1748_, lean_object* v_f_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_array_get_size(v_a_1750_);
v___x_1758_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1759_ = lean_nat_dec_lt(v___x_1756_, v___x_1757_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_dec_ref(v_f_1749_);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
return v___x_1760_;
}
else
{
size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = lean_usize_of_nat(v___x_1757_);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1748_, v_f_1749_, v_a_1750_, v___x_1761_, v___x_1762_, v___x_1758_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun___boxed(lean_object* v_pu_1764_, lean_object* v_f_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
uint8_t v_pu_boxed_1772_; lean_object* v_res_1773_; 
v_pu_boxed_1772_ = lean_unbox(v_pu_1764_);
v_res_1773_ = l_Lean_Compiler_LCNF_Probe_filterByFun(v_pu_boxed_1772_, v_f_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec_ref(v_a_1766_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(uint8_t v_pu_1774_, lean_object* v_f_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
switch(lean_obj_tag(v_a_1776_))
{
case 0:
{
lean_object* v_k_1782_; 
v_k_1782_ = lean_ctor_get(v_a_1776_, 1);
lean_inc_ref(v_k_1782_);
lean_dec_ref_known(v_a_1776_, 2);
v_a_1776_ = v_k_1782_;
goto _start;
}
case 1:
{
lean_object* v_decl_1784_; lean_object* v_k_1785_; lean_object* v_value_1786_; lean_object* v___x_1787_; 
v_decl_1784_ = lean_ctor_get(v_a_1776_, 0);
lean_inc_ref(v_decl_1784_);
v_k_1785_ = lean_ctor_get(v_a_1776_, 1);
lean_inc_ref(v_k_1785_);
lean_dec_ref_known(v_a_1776_, 2);
v_value_1786_ = lean_ctor_get(v_decl_1784_, 4);
lean_inc_ref(v_value_1786_);
lean_dec_ref(v_decl_1784_);
lean_inc_ref(v_f_1775_);
v___x_1787_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1774_, v_f_1775_, v_value_1786_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; uint8_t v___x_1789_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
v___x_1789_ = lean_unbox(v_a_1788_);
lean_dec(v_a_1788_);
if (v___x_1789_ == 0)
{
lean_dec_ref_known(v___x_1787_, 1);
v_a_1776_ = v_k_1785_;
goto _start;
}
else
{
lean_dec_ref(v_k_1785_);
lean_dec_ref(v_f_1775_);
return v___x_1787_;
}
}
else
{
lean_dec_ref(v_k_1785_);
lean_dec_ref(v_f_1775_);
return v___x_1787_;
}
}
case 2:
{
lean_object* v_decl_1791_; lean_object* v_k_1792_; lean_object* v___x_1793_; 
v_decl_1791_ = lean_ctor_get(v_a_1776_, 0);
lean_inc_ref_n(v_decl_1791_, 2);
v_k_1792_ = lean_ctor_get(v_a_1776_, 1);
lean_inc_ref(v_k_1792_);
lean_dec_ref_known(v_a_1776_, 2);
lean_inc_ref(v_f_1775_);
lean_inc(v_a_1780_);
lean_inc_ref(v_a_1779_);
lean_inc(v_a_1778_);
lean_inc_ref(v_a_1777_);
v___x_1793_ = lean_apply_6(v_f_1775_, v_decl_1791_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, lean_box(0));
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; uint8_t v___x_1795_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
v___x_1795_ = lean_unbox(v_a_1794_);
lean_dec(v_a_1794_);
if (v___x_1795_ == 0)
{
lean_object* v_value_1796_; lean_object* v___x_1797_; 
lean_dec_ref_known(v___x_1793_, 1);
v_value_1796_ = lean_ctor_get(v_decl_1791_, 4);
lean_inc_ref(v_value_1796_);
lean_dec_ref(v_decl_1791_);
lean_inc_ref(v_f_1775_);
v___x_1797_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1774_, v_f_1775_, v_value_1796_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; uint8_t v___x_1799_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
v___x_1799_ = lean_unbox(v_a_1798_);
lean_dec(v_a_1798_);
if (v___x_1799_ == 0)
{
lean_dec_ref_known(v___x_1797_, 1);
v_a_1776_ = v_k_1792_;
goto _start;
}
else
{
lean_dec_ref(v_k_1792_);
lean_dec_ref(v_f_1775_);
return v___x_1797_;
}
}
else
{
lean_dec_ref(v_k_1792_);
lean_dec_ref(v_f_1775_);
return v___x_1797_;
}
}
else
{
lean_dec_ref(v_k_1792_);
lean_dec_ref(v_decl_1791_);
lean_dec_ref(v_f_1775_);
return v___x_1793_;
}
}
else
{
lean_dec_ref(v_k_1792_);
lean_dec_ref(v_decl_1791_);
lean_dec_ref(v_f_1775_);
return v___x_1793_;
}
}
case 4:
{
lean_object* v_cases_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1820_; 
v_cases_1801_ = lean_ctor_get(v_a_1776_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_a_1776_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1803_ = v_a_1776_;
v_isShared_1804_ = v_isSharedCheck_1820_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_cases_1801_);
lean_dec(v_a_1776_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1820_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_alts_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_alts_1805_ = lean_ctor_get(v_cases_1801_, 3);
lean_inc_ref(v_alts_1805_);
lean_dec_ref(v_cases_1801_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_array_get_size(v_alts_1805_);
v___x_1808_ = lean_nat_dec_lt(v___x_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
lean_dec_ref(v_alts_1805_);
lean_dec_ref(v_f_1775_);
v___x_1809_ = lean_box(v___x_1808_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1809_);
v___x_1811_ = v___x_1803_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
else
{
if (v___x_1808_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
lean_dec_ref(v_alts_1805_);
lean_dec_ref(v_f_1775_);
v___x_1813_ = lean_box(v___x_1808_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1813_);
v___x_1815_ = v___x_1803_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
else
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
lean_del_object(v___x_1803_);
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1807_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_1774_, v_f_1775_, v_alts_1805_, v___x_1817_, v___x_1818_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
lean_dec_ref(v_alts_1805_);
return v___x_1819_;
}
}
}
}
case 7:
{
lean_object* v_k_1821_; 
v_k_1821_ = lean_ctor_get(v_a_1776_, 3);
lean_inc_ref(v_k_1821_);
lean_dec_ref_known(v_a_1776_, 4);
v_a_1776_ = v_k_1821_;
goto _start;
}
case 8:
{
lean_object* v_k_1823_; 
v_k_1823_ = lean_ctor_get(v_a_1776_, 3);
lean_inc_ref(v_k_1823_);
lean_dec_ref_known(v_a_1776_, 4);
v_a_1776_ = v_k_1823_;
goto _start;
}
case 9:
{
lean_object* v_k_1825_; 
v_k_1825_ = lean_ctor_get(v_a_1776_, 5);
lean_inc_ref(v_k_1825_);
lean_dec_ref_known(v_a_1776_, 6);
v_a_1776_ = v_k_1825_;
goto _start;
}
case 10:
{
lean_object* v_k_1827_; 
v_k_1827_ = lean_ctor_get(v_a_1776_, 2);
lean_inc_ref(v_k_1827_);
lean_dec_ref_known(v_a_1776_, 3);
v_a_1776_ = v_k_1827_;
goto _start;
}
case 11:
{
lean_object* v_k_1829_; 
v_k_1829_ = lean_ctor_get(v_a_1776_, 2);
lean_inc_ref(v_k_1829_);
lean_dec_ref_known(v_a_1776_, 3);
v_a_1776_ = v_k_1829_;
goto _start;
}
case 12:
{
lean_object* v_k_1831_; 
v_k_1831_ = lean_ctor_get(v_a_1776_, 3);
lean_inc_ref(v_k_1831_);
lean_dec_ref_known(v_a_1776_, 4);
v_a_1776_ = v_k_1831_;
goto _start;
}
case 13:
{
lean_object* v_k_1833_; 
v_k_1833_ = lean_ctor_get(v_a_1776_, 1);
lean_inc_ref(v_k_1833_);
lean_dec_ref_known(v_a_1776_, 2);
v_a_1776_ = v_k_1833_;
goto _start;
}
default: 
{
uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec_ref(v_a_1776_);
lean_dec_ref(v_f_1775_);
v___x_1835_ = 0;
v___x_1836_ = lean_box(v___x_1835_);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(uint8_t v_pu_1838_, lean_object* v_f_1839_, lean_object* v_as_1840_, size_t v_i_1841_, size_t v_stop_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_usize_dec_eq(v_i_1841_, v_stop_1842_);
if (v___x_1848_ == 0)
{
uint8_t v___x_1849_; lean_object* v___y_1851_; lean_object* v___x_1866_; 
v___x_1849_ = 1;
v___x_1866_ = lean_array_uget_borrowed(v_as_1840_, v_i_1841_);
switch(lean_obj_tag(v___x_1866_))
{
case 0:
{
lean_object* v_code_1867_; 
v_code_1867_ = lean_ctor_get(v___x_1866_, 2);
lean_inc_ref(v_code_1867_);
v___y_1851_ = v_code_1867_;
goto v___jp_1850_;
}
case 1:
{
lean_object* v_code_1868_; 
v_code_1868_ = lean_ctor_get(v___x_1866_, 1);
lean_inc_ref(v_code_1868_);
v___y_1851_ = v_code_1868_;
goto v___jp_1850_;
}
default: 
{
lean_object* v_code_1869_; 
v_code_1869_ = lean_ctor_get(v___x_1866_, 0);
lean_inc_ref(v_code_1869_);
v___y_1851_ = v_code_1869_;
goto v___jp_1850_;
}
}
v___jp_1850_:
{
lean_object* v___x_1852_; 
lean_inc_ref(v_f_1839_);
v___x_1852_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1838_, v_f_1839_, v___y_1851_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1865_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1855_ = v___x_1852_;
v_isShared_1856_ = v_isSharedCheck_1865_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1852_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1865_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_unbox(v_a_1853_);
lean_dec(v_a_1853_);
if (v___x_1857_ == 0)
{
size_t v___x_1858_; size_t v___x_1859_; 
lean_del_object(v___x_1855_);
v___x_1858_ = ((size_t)1ULL);
v___x_1859_ = lean_usize_add(v_i_1841_, v___x_1858_);
v_i_1841_ = v___x_1859_;
goto _start;
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_dec_ref(v_f_1839_);
v___x_1861_ = lean_box(v___x_1849_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1861_);
v___x_1863_ = v___x_1855_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_dec_ref(v_f_1839_);
return v___x_1852_;
}
}
}
else
{
uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec_ref(v_f_1839_);
v___x_1870_ = 0;
v___x_1871_ = lean_box(v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0___boxed(lean_object* v_pu_1873_, lean_object* v_f_1874_, lean_object* v_as_1875_, lean_object* v_i_1876_, lean_object* v_stop_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
uint8_t v_pu_boxed_1883_; size_t v_i_boxed_1884_; size_t v_stop_boxed_1885_; lean_object* v_res_1886_; 
v_pu_boxed_1883_ = lean_unbox(v_pu_1873_);
v_i_boxed_1884_ = lean_unbox_usize(v_i_1876_);
lean_dec(v_i_1876_);
v_stop_boxed_1885_ = lean_unbox_usize(v_stop_1877_);
lean_dec(v_stop_1877_);
v_res_1886_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_boxed_1883_, v_f_1874_, v_as_1875_, v_i_boxed_1884_, v_stop_boxed_1885_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec_ref(v_as_1875_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed(lean_object* v_pu_1887_, lean_object* v_f_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
uint8_t v_pu_boxed_1895_; lean_object* v_res_1896_; 
v_pu_boxed_1895_ = lean_unbox(v_pu_1887_);
v_res_1896_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_boxed_1895_, v_f_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(uint8_t v_pu_1897_, lean_object* v_f_1898_, lean_object* v_as_1899_, size_t v_i_1900_, size_t v_stop_1901_, lean_object* v_b_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_usize_dec_eq(v_i_1900_, v_stop_1901_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v_value_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1909_ = lean_array_uget_borrowed(v_as_1899_, v_i_1900_);
v_value_1910_ = lean_ctor_get(v___x_1909_, 1);
v___x_1911_ = lean_box(v_pu_1897_);
lean_inc_ref(v_f_1898_);
v___x_1912_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed), 8, 2);
lean_closure_set(v___x_1912_, 0, v___x_1911_);
lean_closure_set(v___x_1912_, 1, v_f_1898_);
lean_inc_ref(v_value_1910_);
v___x_1913_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1910_, v___x_1912_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v_a_1916_; uint8_t v___x_1920_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1920_ = lean_unbox(v_a_1914_);
lean_dec(v_a_1914_);
if (v___x_1920_ == 0)
{
v_a_1916_ = v_b_1902_;
goto v___jp_1915_;
}
else
{
lean_object* v___x_1921_; 
lean_inc(v___x_1909_);
v___x_1921_ = lean_array_push(v_b_1902_, v___x_1909_);
v_a_1916_ = v___x_1921_;
goto v___jp_1915_;
}
v___jp_1915_:
{
size_t v___x_1917_; size_t v___x_1918_; 
v___x_1917_ = ((size_t)1ULL);
v___x_1918_ = lean_usize_add(v_i_1900_, v___x_1917_);
v_i_1900_ = v___x_1918_;
v_b_1902_ = v_a_1916_;
goto _start;
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v_b_1902_);
lean_dec_ref(v_f_1898_);
v_a_1922_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1913_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1913_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v___x_1930_; 
lean_dec_ref(v_f_1898_);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_b_1902_);
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0___boxed(lean_object* v_pu_1931_, lean_object* v_f_1932_, lean_object* v_as_1933_, lean_object* v_i_1934_, lean_object* v_stop_1935_, lean_object* v_b_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
uint8_t v_pu_boxed_1942_; size_t v_i_boxed_1943_; size_t v_stop_boxed_1944_; lean_object* v_res_1945_; 
v_pu_boxed_1942_ = lean_unbox(v_pu_1931_);
v_i_boxed_1943_ = lean_unbox_usize(v_i_1934_);
lean_dec(v_i_1934_);
v_stop_boxed_1944_ = lean_unbox_usize(v_stop_1935_);
lean_dec(v_stop_1935_);
v_res_1945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_boxed_1942_, v_f_1932_, v_as_1933_, v_i_boxed_1943_, v_stop_boxed_1944_, v_b_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec_ref(v_as_1933_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp(uint8_t v_pu_1946_, lean_object* v_f_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = lean_array_get_size(v_a_1948_);
v___x_1956_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1957_ = lean_nat_dec_lt(v___x_1954_, v___x_1955_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; 
lean_dec_ref(v_f_1947_);
v___x_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
return v___x_1958_;
}
else
{
size_t v___x_1959_; size_t v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = lean_usize_of_nat(v___x_1955_);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_1946_, v_f_1947_, v_a_1948_, v___x_1959_, v___x_1960_, v___x_1956_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp___boxed(lean_object* v_pu_1962_, lean_object* v_f_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
uint8_t v_pu_boxed_1970_; lean_object* v_res_1971_; 
v_pu_boxed_1970_ = lean_unbox(v_pu_1962_);
v_res_1971_ = l_Lean_Compiler_LCNF_Probe_filterByJp(v_pu_boxed_1970_, v_f_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
lean_dec_ref(v_a_1964_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(uint8_t v_pu_1972_, lean_object* v_f_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
switch(lean_obj_tag(v_a_1974_))
{
case 0:
{
lean_object* v_k_1980_; 
v_k_1980_ = lean_ctor_get(v_a_1974_, 1);
lean_inc_ref(v_k_1980_);
lean_dec_ref_known(v_a_1974_, 2);
v_a_1974_ = v_k_1980_;
goto _start;
}
case 1:
{
lean_object* v_decl_1982_; lean_object* v_k_1983_; lean_object* v___x_1984_; 
v_decl_1982_ = lean_ctor_get(v_a_1974_, 0);
lean_inc_ref_n(v_decl_1982_, 2);
v_k_1983_ = lean_ctor_get(v_a_1974_, 1);
lean_inc_ref(v_k_1983_);
lean_dec_ref_known(v_a_1974_, 2);
lean_inc_ref(v_f_1973_);
lean_inc(v_a_1978_);
lean_inc_ref(v_a_1977_);
lean_inc(v_a_1976_);
lean_inc_ref(v_a_1975_);
v___x_1984_ = lean_apply_6(v_f_1973_, v_decl_1982_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, lean_box(0));
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; uint8_t v___x_1986_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
v___x_1986_ = lean_unbox(v_a_1985_);
lean_dec(v_a_1985_);
if (v___x_1986_ == 0)
{
lean_object* v_value_1987_; lean_object* v___x_1988_; 
lean_dec_ref_known(v___x_1984_, 1);
v_value_1987_ = lean_ctor_get(v_decl_1982_, 4);
lean_inc_ref(v_value_1987_);
lean_dec_ref(v_decl_1982_);
lean_inc_ref(v_f_1973_);
v___x_1988_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_1972_, v_f_1973_, v_value_1987_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; uint8_t v___x_1990_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
v___x_1990_ = lean_unbox(v_a_1989_);
lean_dec(v_a_1989_);
if (v___x_1990_ == 0)
{
lean_dec_ref_known(v___x_1988_, 1);
v_a_1974_ = v_k_1983_;
goto _start;
}
else
{
lean_dec_ref(v_k_1983_);
lean_dec_ref(v_f_1973_);
return v___x_1988_;
}
}
else
{
lean_dec_ref(v_k_1983_);
lean_dec_ref(v_f_1973_);
return v___x_1988_;
}
}
else
{
lean_dec_ref(v_k_1983_);
lean_dec_ref(v_decl_1982_);
lean_dec_ref(v_f_1973_);
return v___x_1984_;
}
}
else
{
lean_dec_ref(v_k_1983_);
lean_dec_ref(v_decl_1982_);
lean_dec_ref(v_f_1973_);
return v___x_1984_;
}
}
case 2:
{
lean_object* v_decl_1992_; lean_object* v_k_1993_; lean_object* v___x_1994_; 
v_decl_1992_ = lean_ctor_get(v_a_1974_, 0);
lean_inc_ref_n(v_decl_1992_, 2);
v_k_1993_ = lean_ctor_get(v_a_1974_, 1);
lean_inc_ref(v_k_1993_);
lean_dec_ref_known(v_a_1974_, 2);
lean_inc_ref(v_f_1973_);
lean_inc(v_a_1978_);
lean_inc_ref(v_a_1977_);
lean_inc(v_a_1976_);
lean_inc_ref(v_a_1975_);
v___x_1994_ = lean_apply_6(v_f_1973_, v_decl_1992_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, lean_box(0));
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; uint8_t v___x_1996_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
v___x_1996_ = lean_unbox(v_a_1995_);
lean_dec(v_a_1995_);
if (v___x_1996_ == 0)
{
lean_object* v_value_1997_; lean_object* v___x_1998_; 
lean_dec_ref_known(v___x_1994_, 1);
v_value_1997_ = lean_ctor_get(v_decl_1992_, 4);
lean_inc_ref(v_value_1997_);
lean_dec_ref(v_decl_1992_);
lean_inc_ref(v_f_1973_);
v___x_1998_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_1972_, v_f_1973_, v_value_1997_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; uint8_t v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
v___x_2000_ = lean_unbox(v_a_1999_);
lean_dec(v_a_1999_);
if (v___x_2000_ == 0)
{
lean_dec_ref_known(v___x_1998_, 1);
v_a_1974_ = v_k_1993_;
goto _start;
}
else
{
lean_dec_ref(v_k_1993_);
lean_dec_ref(v_f_1973_);
return v___x_1998_;
}
}
else
{
lean_dec_ref(v_k_1993_);
lean_dec_ref(v_f_1973_);
return v___x_1998_;
}
}
else
{
lean_dec_ref(v_k_1993_);
lean_dec_ref(v_decl_1992_);
lean_dec_ref(v_f_1973_);
return v___x_1994_;
}
}
else
{
lean_dec_ref(v_k_1993_);
lean_dec_ref(v_decl_1992_);
lean_dec_ref(v_f_1973_);
return v___x_1994_;
}
}
case 4:
{
lean_object* v_cases_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2021_; 
v_cases_2002_ = lean_ctor_get(v_a_1974_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_a_1974_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2004_ = v_a_1974_;
v_isShared_2005_ = v_isSharedCheck_2021_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_cases_2002_);
lean_dec(v_a_1974_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2021_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v_alts_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_alts_2006_ = lean_ctor_get(v_cases_2002_, 3);
lean_inc_ref(v_alts_2006_);
lean_dec_ref(v_cases_2002_);
v___x_2007_ = lean_unsigned_to_nat(0u);
v___x_2008_ = lean_array_get_size(v_alts_2006_);
v___x_2009_ = lean_nat_dec_lt(v___x_2007_, v___x_2008_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_dec_ref(v_alts_2006_);
lean_dec_ref(v_f_1973_);
v___x_2010_ = lean_box(v___x_2009_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2010_);
v___x_2012_ = v___x_2004_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
else
{
if (v___x_2009_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
lean_dec_ref(v_alts_2006_);
lean_dec_ref(v_f_1973_);
v___x_2014_ = lean_box(v___x_2009_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2014_);
v___x_2016_ = v___x_2004_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
else
{
size_t v___x_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
lean_del_object(v___x_2004_);
v___x_2018_ = ((size_t)0ULL);
v___x_2019_ = lean_usize_of_nat(v___x_2008_);
v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_1972_, v_f_1973_, v_alts_2006_, v___x_2018_, v___x_2019_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
lean_dec_ref(v_alts_2006_);
return v___x_2020_;
}
}
}
}
case 7:
{
lean_object* v_k_2022_; 
v_k_2022_ = lean_ctor_get(v_a_1974_, 3);
lean_inc_ref(v_k_2022_);
lean_dec_ref_known(v_a_1974_, 4);
v_a_1974_ = v_k_2022_;
goto _start;
}
case 8:
{
lean_object* v_k_2024_; 
v_k_2024_ = lean_ctor_get(v_a_1974_, 3);
lean_inc_ref(v_k_2024_);
lean_dec_ref_known(v_a_1974_, 4);
v_a_1974_ = v_k_2024_;
goto _start;
}
case 9:
{
lean_object* v_k_2026_; 
v_k_2026_ = lean_ctor_get(v_a_1974_, 5);
lean_inc_ref(v_k_2026_);
lean_dec_ref_known(v_a_1974_, 6);
v_a_1974_ = v_k_2026_;
goto _start;
}
case 10:
{
lean_object* v_k_2028_; 
v_k_2028_ = lean_ctor_get(v_a_1974_, 2);
lean_inc_ref(v_k_2028_);
lean_dec_ref_known(v_a_1974_, 3);
v_a_1974_ = v_k_2028_;
goto _start;
}
case 11:
{
lean_object* v_k_2030_; 
v_k_2030_ = lean_ctor_get(v_a_1974_, 2);
lean_inc_ref(v_k_2030_);
lean_dec_ref_known(v_a_1974_, 3);
v_a_1974_ = v_k_2030_;
goto _start;
}
case 12:
{
lean_object* v_k_2032_; 
v_k_2032_ = lean_ctor_get(v_a_1974_, 3);
lean_inc_ref(v_k_2032_);
lean_dec_ref_known(v_a_1974_, 4);
v_a_1974_ = v_k_2032_;
goto _start;
}
case 13:
{
lean_object* v_k_2034_; 
v_k_2034_ = lean_ctor_get(v_a_1974_, 1);
lean_inc_ref(v_k_2034_);
lean_dec_ref_known(v_a_1974_, 2);
v_a_1974_ = v_k_2034_;
goto _start;
}
default: 
{
uint8_t v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_dec_ref(v_a_1974_);
lean_dec_ref(v_f_1973_);
v___x_2036_ = 0;
v___x_2037_ = lean_box(v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
return v___x_2038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(uint8_t v_pu_2039_, lean_object* v_f_2040_, lean_object* v_as_2041_, size_t v_i_2042_, size_t v_stop_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_eq(v_i_2042_, v_stop_2043_);
if (v___x_2049_ == 0)
{
uint8_t v___x_2050_; lean_object* v___y_2052_; lean_object* v___x_2067_; 
v___x_2050_ = 1;
v___x_2067_ = lean_array_uget_borrowed(v_as_2041_, v_i_2042_);
switch(lean_obj_tag(v___x_2067_))
{
case 0:
{
lean_object* v_code_2068_; 
v_code_2068_ = lean_ctor_get(v___x_2067_, 2);
lean_inc_ref(v_code_2068_);
v___y_2052_ = v_code_2068_;
goto v___jp_2051_;
}
case 1:
{
lean_object* v_code_2069_; 
v_code_2069_ = lean_ctor_get(v___x_2067_, 1);
lean_inc_ref(v_code_2069_);
v___y_2052_ = v_code_2069_;
goto v___jp_2051_;
}
default: 
{
lean_object* v_code_2070_; 
v_code_2070_ = lean_ctor_get(v___x_2067_, 0);
lean_inc_ref(v_code_2070_);
v___y_2052_ = v_code_2070_;
goto v___jp_2051_;
}
}
v___jp_2051_:
{
lean_object* v___x_2053_; 
lean_inc_ref(v_f_2040_);
v___x_2053_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2039_, v_f_2040_, v___y_2052_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2066_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2066_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2066_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_unbox(v_a_2054_);
lean_dec(v_a_2054_);
if (v___x_2058_ == 0)
{
size_t v___x_2059_; size_t v___x_2060_; 
lean_del_object(v___x_2056_);
v___x_2059_ = ((size_t)1ULL);
v___x_2060_ = lean_usize_add(v_i_2042_, v___x_2059_);
v_i_2042_ = v___x_2060_;
goto _start;
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
lean_dec_ref(v_f_2040_);
v___x_2062_ = lean_box(v___x_2050_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2062_);
v___x_2064_ = v___x_2056_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_dec_ref(v_f_2040_);
return v___x_2053_;
}
}
}
else
{
uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec_ref(v_f_2040_);
v___x_2071_ = 0;
v___x_2072_ = lean_box(v___x_2071_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0___boxed(lean_object* v_pu_2074_, lean_object* v_f_2075_, lean_object* v_as_2076_, lean_object* v_i_2077_, lean_object* v_stop_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
uint8_t v_pu_boxed_2084_; size_t v_i_boxed_2085_; size_t v_stop_boxed_2086_; lean_object* v_res_2087_; 
v_pu_boxed_2084_ = lean_unbox(v_pu_2074_);
v_i_boxed_2085_ = lean_unbox_usize(v_i_2077_);
lean_dec(v_i_2077_);
v_stop_boxed_2086_ = lean_unbox_usize(v_stop_2078_);
lean_dec(v_stop_2078_);
v_res_2087_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_boxed_2084_, v_f_2075_, v_as_2076_, v_i_boxed_2085_, v_stop_boxed_2086_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec_ref(v_as_2076_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed(lean_object* v_pu_2088_, lean_object* v_f_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
uint8_t v_pu_boxed_2096_; lean_object* v_res_2097_; 
v_pu_boxed_2096_ = lean_unbox(v_pu_2088_);
v_res_2097_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_boxed_2096_, v_f_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(uint8_t v_pu_2098_, lean_object* v_f_2099_, lean_object* v_as_2100_, size_t v_i_2101_, size_t v_stop_2102_, lean_object* v_b_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_usize_dec_eq(v_i_2101_, v_stop_2102_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; lean_object* v_value_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2110_ = lean_array_uget_borrowed(v_as_2100_, v_i_2101_);
v_value_2111_ = lean_ctor_get(v___x_2110_, 1);
v___x_2112_ = lean_box(v_pu_2098_);
lean_inc_ref(v_f_2099_);
v___x_2113_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed), 8, 2);
lean_closure_set(v___x_2113_, 0, v___x_2112_);
lean_closure_set(v___x_2113_, 1, v_f_2099_);
lean_inc_ref(v_value_2111_);
v___x_2114_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2111_, v___x_2113_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v_a_2117_; uint8_t v___x_2121_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2121_ = lean_unbox(v_a_2115_);
lean_dec(v_a_2115_);
if (v___x_2121_ == 0)
{
v_a_2117_ = v_b_2103_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2122_; 
lean_inc(v___x_2110_);
v___x_2122_ = lean_array_push(v_b_2103_, v___x_2110_);
v_a_2117_ = v___x_2122_;
goto v___jp_2116_;
}
v___jp_2116_:
{
size_t v___x_2118_; size_t v___x_2119_; 
v___x_2118_ = ((size_t)1ULL);
v___x_2119_ = lean_usize_add(v_i_2101_, v___x_2118_);
v_i_2101_ = v___x_2119_;
v_b_2103_ = v_a_2117_;
goto _start;
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref(v_b_2103_);
lean_dec_ref(v_f_2099_);
v_a_2123_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2114_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2114_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
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
else
{
lean_object* v___x_2131_; 
lean_dec_ref(v_f_2099_);
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_b_2103_);
return v___x_2131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0___boxed(lean_object* v_pu_2132_, lean_object* v_f_2133_, lean_object* v_as_2134_, lean_object* v_i_2135_, lean_object* v_stop_2136_, lean_object* v_b_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v_pu_boxed_2143_; size_t v_i_boxed_2144_; size_t v_stop_boxed_2145_; lean_object* v_res_2146_; 
v_pu_boxed_2143_ = lean_unbox(v_pu_2132_);
v_i_boxed_2144_ = lean_unbox_usize(v_i_2135_);
lean_dec(v_i_2135_);
v_stop_boxed_2145_ = lean_unbox_usize(v_stop_2136_);
lean_dec(v_stop_2136_);
v_res_2146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_boxed_2143_, v_f_2133_, v_as_2134_, v_i_boxed_2144_, v_stop_boxed_2145_, v_b_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec_ref(v_as_2134_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl(uint8_t v_pu_2147_, lean_object* v_f_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_array_get_size(v_a_2149_);
v___x_2157_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2158_ = lean_nat_dec_lt(v___x_2155_, v___x_2156_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
lean_dec_ref(v_f_2148_);
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
return v___x_2159_;
}
else
{
size_t v___x_2160_; size_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = ((size_t)0ULL);
v___x_2161_ = lean_usize_of_nat(v___x_2156_);
v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2147_, v_f_2148_, v_a_2149_, v___x_2160_, v___x_2161_, v___x_2157_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl___boxed(lean_object* v_pu_2163_, lean_object* v_f_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
uint8_t v_pu_boxed_2171_; lean_object* v_res_2172_; 
v_pu_boxed_2171_ = lean_unbox(v_pu_2163_);
v_res_2172_ = l_Lean_Compiler_LCNF_Probe_filterByFunDecl(v_pu_boxed_2171_, v_f_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
lean_dec(v_a_2169_);
lean_dec_ref(v_a_2168_);
lean_dec(v_a_2167_);
lean_dec_ref(v_a_2166_);
lean_dec_ref(v_a_2165_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(uint8_t v_pu_2173_, lean_object* v_f_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
switch(lean_obj_tag(v_a_2175_))
{
case 0:
{
lean_object* v_k_2181_; 
v_k_2181_ = lean_ctor_get(v_a_2175_, 1);
lean_inc_ref(v_k_2181_);
lean_dec_ref_known(v_a_2175_, 2);
v_a_2175_ = v_k_2181_;
goto _start;
}
case 1:
{
lean_object* v_decl_2183_; lean_object* v_k_2184_; lean_object* v_value_2185_; lean_object* v___x_2186_; 
v_decl_2183_ = lean_ctor_get(v_a_2175_, 0);
lean_inc_ref(v_decl_2183_);
v_k_2184_ = lean_ctor_get(v_a_2175_, 1);
lean_inc_ref(v_k_2184_);
lean_dec_ref_known(v_a_2175_, 2);
v_value_2185_ = lean_ctor_get(v_decl_2183_, 4);
lean_inc_ref(v_value_2185_);
lean_dec_ref(v_decl_2183_);
lean_inc_ref(v_f_2174_);
v___x_2186_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2173_, v_f_2174_, v_value_2185_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; uint8_t v___x_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
v___x_2188_ = lean_unbox(v_a_2187_);
lean_dec(v_a_2187_);
if (v___x_2188_ == 0)
{
lean_dec_ref_known(v___x_2186_, 1);
v_a_2175_ = v_k_2184_;
goto _start;
}
else
{
lean_dec_ref(v_k_2184_);
lean_dec_ref(v_f_2174_);
return v___x_2186_;
}
}
else
{
lean_dec_ref(v_k_2184_);
lean_dec_ref(v_f_2174_);
return v___x_2186_;
}
}
case 2:
{
lean_object* v_decl_2190_; lean_object* v_k_2191_; lean_object* v_value_2192_; lean_object* v___x_2193_; 
v_decl_2190_ = lean_ctor_get(v_a_2175_, 0);
lean_inc_ref(v_decl_2190_);
v_k_2191_ = lean_ctor_get(v_a_2175_, 1);
lean_inc_ref(v_k_2191_);
lean_dec_ref_known(v_a_2175_, 2);
v_value_2192_ = lean_ctor_get(v_decl_2190_, 4);
lean_inc_ref(v_value_2192_);
lean_dec_ref(v_decl_2190_);
lean_inc_ref(v_f_2174_);
v___x_2193_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2173_, v_f_2174_, v_value_2192_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; uint8_t v___x_2195_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
v___x_2195_ = lean_unbox(v_a_2194_);
lean_dec(v_a_2194_);
if (v___x_2195_ == 0)
{
lean_dec_ref_known(v___x_2193_, 1);
v_a_2175_ = v_k_2191_;
goto _start;
}
else
{
lean_dec_ref(v_k_2191_);
lean_dec_ref(v_f_2174_);
return v___x_2193_;
}
}
else
{
lean_dec_ref(v_k_2191_);
lean_dec_ref(v_f_2174_);
return v___x_2193_;
}
}
case 4:
{
lean_object* v_cases_2197_; lean_object* v___x_2198_; 
v_cases_2197_ = lean_ctor_get(v_a_2175_, 0);
lean_inc_ref_n(v_cases_2197_, 2);
lean_dec_ref_known(v_a_2175_, 1);
lean_inc_ref(v_f_2174_);
lean_inc(v_a_2179_);
lean_inc_ref(v_a_2178_);
lean_inc(v_a_2177_);
lean_inc_ref(v_a_2176_);
v___x_2198_ = lean_apply_6(v_f_2174_, v_cases_2197_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, lean_box(0));
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; uint8_t v___x_2200_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
v___x_2200_ = lean_unbox(v_a_2199_);
lean_dec(v_a_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2219_; 
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2219_ == 0)
{
lean_object* v_unused_2220_; 
v_unused_2220_ = lean_ctor_get(v___x_2198_, 0);
lean_dec(v_unused_2220_);
v___x_2202_ = v___x_2198_;
v_isShared_2203_ = v_isSharedCheck_2219_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v___x_2198_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2219_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_alts_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v_alts_2204_ = lean_ctor_get(v_cases_2197_, 3);
lean_inc_ref(v_alts_2204_);
lean_dec_ref(v_cases_2197_);
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = lean_array_get_size(v_alts_2204_);
v___x_2207_ = lean_nat_dec_lt(v___x_2205_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2210_; 
lean_dec_ref(v_alts_2204_);
lean_dec_ref(v_f_2174_);
v___x_2208_ = lean_box(v___x_2207_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2208_);
v___x_2210_ = v___x_2202_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2208_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
else
{
if (v___x_2207_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
lean_dec_ref(v_alts_2204_);
lean_dec_ref(v_f_2174_);
v___x_2212_ = lean_box(v___x_2207_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2212_);
v___x_2214_ = v___x_2202_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
else
{
size_t v___x_2216_; size_t v___x_2217_; lean_object* v___x_2218_; 
lean_del_object(v___x_2202_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = lean_usize_of_nat(v___x_2206_);
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_2173_, v_f_2174_, v_alts_2204_, v___x_2216_, v___x_2217_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
lean_dec_ref(v_alts_2204_);
return v___x_2218_;
}
}
}
}
else
{
lean_dec_ref(v_cases_2197_);
lean_dec_ref(v_f_2174_);
return v___x_2198_;
}
}
else
{
lean_dec_ref(v_cases_2197_);
lean_dec_ref(v_f_2174_);
return v___x_2198_;
}
}
case 7:
{
lean_object* v_k_2221_; 
v_k_2221_ = lean_ctor_get(v_a_2175_, 3);
lean_inc_ref(v_k_2221_);
lean_dec_ref_known(v_a_2175_, 4);
v_a_2175_ = v_k_2221_;
goto _start;
}
case 8:
{
lean_object* v_k_2223_; 
v_k_2223_ = lean_ctor_get(v_a_2175_, 3);
lean_inc_ref(v_k_2223_);
lean_dec_ref_known(v_a_2175_, 4);
v_a_2175_ = v_k_2223_;
goto _start;
}
case 9:
{
lean_object* v_k_2225_; 
v_k_2225_ = lean_ctor_get(v_a_2175_, 5);
lean_inc_ref(v_k_2225_);
lean_dec_ref_known(v_a_2175_, 6);
v_a_2175_ = v_k_2225_;
goto _start;
}
case 10:
{
lean_object* v_k_2227_; 
v_k_2227_ = lean_ctor_get(v_a_2175_, 2);
lean_inc_ref(v_k_2227_);
lean_dec_ref_known(v_a_2175_, 3);
v_a_2175_ = v_k_2227_;
goto _start;
}
case 11:
{
lean_object* v_k_2229_; 
v_k_2229_ = lean_ctor_get(v_a_2175_, 2);
lean_inc_ref(v_k_2229_);
lean_dec_ref_known(v_a_2175_, 3);
v_a_2175_ = v_k_2229_;
goto _start;
}
case 12:
{
lean_object* v_k_2231_; 
v_k_2231_ = lean_ctor_get(v_a_2175_, 3);
lean_inc_ref(v_k_2231_);
lean_dec_ref_known(v_a_2175_, 4);
v_a_2175_ = v_k_2231_;
goto _start;
}
case 13:
{
lean_object* v_k_2233_; 
v_k_2233_ = lean_ctor_get(v_a_2175_, 1);
lean_inc_ref(v_k_2233_);
lean_dec_ref_known(v_a_2175_, 2);
v_a_2175_ = v_k_2233_;
goto _start;
}
default: 
{
uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec_ref(v_a_2175_);
lean_dec_ref(v_f_2174_);
v___x_2235_ = 0;
v___x_2236_ = lean_box(v___x_2235_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(uint8_t v_pu_2238_, lean_object* v_f_2239_, lean_object* v_as_2240_, size_t v_i_2241_, size_t v_stop_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
uint8_t v___x_2248_; 
v___x_2248_ = lean_usize_dec_eq(v_i_2241_, v_stop_2242_);
if (v___x_2248_ == 0)
{
uint8_t v___x_2249_; lean_object* v___y_2251_; lean_object* v___x_2266_; 
v___x_2249_ = 1;
v___x_2266_ = lean_array_uget_borrowed(v_as_2240_, v_i_2241_);
switch(lean_obj_tag(v___x_2266_))
{
case 0:
{
lean_object* v_code_2267_; 
v_code_2267_ = lean_ctor_get(v___x_2266_, 2);
lean_inc_ref(v_code_2267_);
v___y_2251_ = v_code_2267_;
goto v___jp_2250_;
}
case 1:
{
lean_object* v_code_2268_; 
v_code_2268_ = lean_ctor_get(v___x_2266_, 1);
lean_inc_ref(v_code_2268_);
v___y_2251_ = v_code_2268_;
goto v___jp_2250_;
}
default: 
{
lean_object* v_code_2269_; 
v_code_2269_ = lean_ctor_get(v___x_2266_, 0);
lean_inc_ref(v_code_2269_);
v___y_2251_ = v_code_2269_;
goto v___jp_2250_;
}
}
v___jp_2250_:
{
lean_object* v___x_2252_; 
lean_inc_ref(v_f_2239_);
v___x_2252_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2238_, v_f_2239_, v___y_2251_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2265_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2265_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2265_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
uint8_t v___x_2257_; 
v___x_2257_ = lean_unbox(v_a_2253_);
lean_dec(v_a_2253_);
if (v___x_2257_ == 0)
{
size_t v___x_2258_; size_t v___x_2259_; 
lean_del_object(v___x_2255_);
v___x_2258_ = ((size_t)1ULL);
v___x_2259_ = lean_usize_add(v_i_2241_, v___x_2258_);
v_i_2241_ = v___x_2259_;
goto _start;
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2263_; 
lean_dec_ref(v_f_2239_);
v___x_2261_ = lean_box(v___x_2249_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2261_);
v___x_2263_ = v___x_2255_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_dec_ref(v_f_2239_);
return v___x_2252_;
}
}
}
else
{
uint8_t v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec_ref(v_f_2239_);
v___x_2270_ = 0;
v___x_2271_ = lean_box(v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
return v___x_2272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0___boxed(lean_object* v_pu_2273_, lean_object* v_f_2274_, lean_object* v_as_2275_, lean_object* v_i_2276_, lean_object* v_stop_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
uint8_t v_pu_boxed_2283_; size_t v_i_boxed_2284_; size_t v_stop_boxed_2285_; lean_object* v_res_2286_; 
v_pu_boxed_2283_ = lean_unbox(v_pu_2273_);
v_i_boxed_2284_ = lean_unbox_usize(v_i_2276_);
lean_dec(v_i_2276_);
v_stop_boxed_2285_ = lean_unbox_usize(v_stop_2277_);
lean_dec(v_stop_2277_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_boxed_2283_, v_f_2274_, v_as_2275_, v_i_boxed_2284_, v_stop_boxed_2285_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_as_2275_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed(lean_object* v_pu_2287_, lean_object* v_f_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
uint8_t v_pu_boxed_2295_; lean_object* v_res_2296_; 
v_pu_boxed_2295_ = lean_unbox(v_pu_2287_);
v_res_2296_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_boxed_2295_, v_f_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(uint8_t v_pu_2297_, lean_object* v_f_2298_, lean_object* v_as_2299_, size_t v_i_2300_, size_t v_stop_2301_, lean_object* v_b_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
uint8_t v___x_2308_; 
v___x_2308_ = lean_usize_dec_eq(v_i_2300_, v_stop_2301_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v_value_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2309_ = lean_array_uget_borrowed(v_as_2299_, v_i_2300_);
v_value_2310_ = lean_ctor_get(v___x_2309_, 1);
v___x_2311_ = lean_box(v_pu_2297_);
lean_inc_ref(v_f_2298_);
v___x_2312_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed), 8, 2);
lean_closure_set(v___x_2312_, 0, v___x_2311_);
lean_closure_set(v___x_2312_, 1, v_f_2298_);
lean_inc_ref(v_value_2310_);
v___x_2313_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2310_, v___x_2312_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v_a_2316_; uint8_t v___x_2320_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2320_ = lean_unbox(v_a_2314_);
lean_dec(v_a_2314_);
if (v___x_2320_ == 0)
{
v_a_2316_ = v_b_2302_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2321_; 
lean_inc(v___x_2309_);
v___x_2321_ = lean_array_push(v_b_2302_, v___x_2309_);
v_a_2316_ = v___x_2321_;
goto v___jp_2315_;
}
v___jp_2315_:
{
size_t v___x_2317_; size_t v___x_2318_; 
v___x_2317_ = ((size_t)1ULL);
v___x_2318_ = lean_usize_add(v_i_2300_, v___x_2317_);
v_i_2300_ = v___x_2318_;
v_b_2302_ = v_a_2316_;
goto _start;
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec_ref(v_b_2302_);
lean_dec_ref(v_f_2298_);
v_a_2322_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2313_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2313_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v___x_2330_; 
lean_dec_ref(v_f_2298_);
v___x_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2330_, 0, v_b_2302_);
return v___x_2330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0___boxed(lean_object* v_pu_2331_, lean_object* v_f_2332_, lean_object* v_as_2333_, lean_object* v_i_2334_, lean_object* v_stop_2335_, lean_object* v_b_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
uint8_t v_pu_boxed_2342_; size_t v_i_boxed_2343_; size_t v_stop_boxed_2344_; lean_object* v_res_2345_; 
v_pu_boxed_2342_ = lean_unbox(v_pu_2331_);
v_i_boxed_2343_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_stop_boxed_2344_ = lean_unbox_usize(v_stop_2335_);
lean_dec(v_stop_2335_);
v_res_2345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_boxed_2342_, v_f_2332_, v_as_2333_, v_i_boxed_2343_, v_stop_boxed_2344_, v_b_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec_ref(v_as_2333_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases(uint8_t v_pu_2346_, lean_object* v_f_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = lean_array_get_size(v_a_2348_);
v___x_2356_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2357_ = lean_nat_dec_lt(v___x_2354_, v___x_2355_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
lean_dec_ref(v_f_2347_);
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
return v___x_2358_;
}
else
{
size_t v___x_2359_; size_t v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = ((size_t)0ULL);
v___x_2360_ = lean_usize_of_nat(v___x_2355_);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2346_, v_f_2347_, v_a_2348_, v___x_2359_, v___x_2360_, v___x_2356_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases___boxed(lean_object* v_pu_2362_, lean_object* v_f_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
uint8_t v_pu_boxed_2370_; lean_object* v_res_2371_; 
v_pu_boxed_2370_ = lean_unbox(v_pu_2362_);
v_res_2371_ = l_Lean_Compiler_LCNF_Probe_filterByCases(v_pu_boxed_2370_, v_f_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec_ref(v_a_2364_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(uint8_t v_pu_2372_, lean_object* v_f_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
switch(lean_obj_tag(v_a_2374_))
{
case 0:
{
lean_object* v_k_2380_; 
v_k_2380_ = lean_ctor_get(v_a_2374_, 1);
lean_inc_ref(v_k_2380_);
lean_dec_ref_known(v_a_2374_, 2);
v_a_2374_ = v_k_2380_;
goto _start;
}
case 1:
{
lean_object* v_decl_2382_; lean_object* v_k_2383_; lean_object* v_value_2384_; lean_object* v___x_2385_; 
v_decl_2382_ = lean_ctor_get(v_a_2374_, 0);
lean_inc_ref(v_decl_2382_);
v_k_2383_ = lean_ctor_get(v_a_2374_, 1);
lean_inc_ref(v_k_2383_);
lean_dec_ref_known(v_a_2374_, 2);
v_value_2384_ = lean_ctor_get(v_decl_2382_, 4);
lean_inc_ref(v_value_2384_);
lean_dec_ref(v_decl_2382_);
lean_inc_ref(v_f_2373_);
v___x_2385_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2372_, v_f_2373_, v_value_2384_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; uint8_t v___x_2387_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
v___x_2387_ = lean_unbox(v_a_2386_);
lean_dec(v_a_2386_);
if (v___x_2387_ == 0)
{
lean_dec_ref_known(v___x_2385_, 1);
v_a_2374_ = v_k_2383_;
goto _start;
}
else
{
lean_dec_ref(v_k_2383_);
lean_dec_ref(v_f_2373_);
return v___x_2385_;
}
}
else
{
lean_dec_ref(v_k_2383_);
lean_dec_ref(v_f_2373_);
return v___x_2385_;
}
}
case 2:
{
lean_object* v_decl_2389_; lean_object* v_k_2390_; lean_object* v_value_2391_; lean_object* v___x_2392_; 
v_decl_2389_ = lean_ctor_get(v_a_2374_, 0);
lean_inc_ref(v_decl_2389_);
v_k_2390_ = lean_ctor_get(v_a_2374_, 1);
lean_inc_ref(v_k_2390_);
lean_dec_ref_known(v_a_2374_, 2);
v_value_2391_ = lean_ctor_get(v_decl_2389_, 4);
lean_inc_ref(v_value_2391_);
lean_dec_ref(v_decl_2389_);
lean_inc_ref(v_f_2373_);
v___x_2392_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2372_, v_f_2373_, v_value_2391_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; uint8_t v___x_2394_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
v___x_2394_ = lean_unbox(v_a_2393_);
lean_dec(v_a_2393_);
if (v___x_2394_ == 0)
{
lean_dec_ref_known(v___x_2392_, 1);
v_a_2374_ = v_k_2390_;
goto _start;
}
else
{
lean_dec_ref(v_k_2390_);
lean_dec_ref(v_f_2373_);
return v___x_2392_;
}
}
else
{
lean_dec_ref(v_k_2390_);
lean_dec_ref(v_f_2373_);
return v___x_2392_;
}
}
case 3:
{
lean_object* v_fvarId_2396_; lean_object* v_args_2397_; lean_object* v___x_2398_; 
v_fvarId_2396_ = lean_ctor_get(v_a_2374_, 0);
lean_inc(v_fvarId_2396_);
v_args_2397_ = lean_ctor_get(v_a_2374_, 1);
lean_inc_ref(v_args_2397_);
lean_dec_ref_known(v_a_2374_, 2);
lean_inc(v_a_2378_);
lean_inc_ref(v_a_2377_);
lean_inc(v_a_2376_);
lean_inc_ref(v_a_2375_);
v___x_2398_ = lean_apply_7(v_f_2373_, v_fvarId_2396_, v_args_2397_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, lean_box(0));
return v___x_2398_;
}
case 4:
{
lean_object* v_cases_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2418_; 
v_cases_2399_ = lean_ctor_get(v_a_2374_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_a_2374_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2401_ = v_a_2374_;
v_isShared_2402_ = v_isSharedCheck_2418_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_cases_2399_);
lean_dec(v_a_2374_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2418_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v_alts_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v_alts_2403_ = lean_ctor_get(v_cases_2399_, 3);
lean_inc_ref(v_alts_2403_);
lean_dec_ref(v_cases_2399_);
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = lean_array_get_size(v_alts_2403_);
v___x_2406_ = lean_nat_dec_lt(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
lean_dec_ref(v_alts_2403_);
lean_dec_ref(v_f_2373_);
v___x_2407_ = lean_box(v___x_2406_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set_tag(v___x_2401_, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2407_);
v___x_2409_ = v___x_2401_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
else
{
if (v___x_2406_ == 0)
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
lean_dec_ref(v_alts_2403_);
lean_dec_ref(v_f_2373_);
v___x_2411_ = lean_box(v___x_2406_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set_tag(v___x_2401_, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2411_);
v___x_2413_ = v___x_2401_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
else
{
size_t v___x_2415_; size_t v___x_2416_; lean_object* v___x_2417_; 
lean_del_object(v___x_2401_);
v___x_2415_ = ((size_t)0ULL);
v___x_2416_ = lean_usize_of_nat(v___x_2405_);
v___x_2417_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_2372_, v_f_2373_, v_alts_2403_, v___x_2415_, v___x_2416_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec_ref(v_alts_2403_);
return v___x_2417_;
}
}
}
}
case 7:
{
lean_object* v_k_2419_; 
v_k_2419_ = lean_ctor_get(v_a_2374_, 3);
lean_inc_ref(v_k_2419_);
lean_dec_ref_known(v_a_2374_, 4);
v_a_2374_ = v_k_2419_;
goto _start;
}
case 8:
{
lean_object* v_k_2421_; 
v_k_2421_ = lean_ctor_get(v_a_2374_, 3);
lean_inc_ref(v_k_2421_);
lean_dec_ref_known(v_a_2374_, 4);
v_a_2374_ = v_k_2421_;
goto _start;
}
case 9:
{
lean_object* v_k_2423_; 
v_k_2423_ = lean_ctor_get(v_a_2374_, 5);
lean_inc_ref(v_k_2423_);
lean_dec_ref_known(v_a_2374_, 6);
v_a_2374_ = v_k_2423_;
goto _start;
}
case 10:
{
lean_object* v_k_2425_; 
v_k_2425_ = lean_ctor_get(v_a_2374_, 2);
lean_inc_ref(v_k_2425_);
lean_dec_ref_known(v_a_2374_, 3);
v_a_2374_ = v_k_2425_;
goto _start;
}
case 11:
{
lean_object* v_k_2427_; 
v_k_2427_ = lean_ctor_get(v_a_2374_, 2);
lean_inc_ref(v_k_2427_);
lean_dec_ref_known(v_a_2374_, 3);
v_a_2374_ = v_k_2427_;
goto _start;
}
case 12:
{
lean_object* v_k_2429_; 
v_k_2429_ = lean_ctor_get(v_a_2374_, 3);
lean_inc_ref(v_k_2429_);
lean_dec_ref_known(v_a_2374_, 4);
v_a_2374_ = v_k_2429_;
goto _start;
}
case 13:
{
lean_object* v_k_2431_; 
v_k_2431_ = lean_ctor_get(v_a_2374_, 1);
lean_inc_ref(v_k_2431_);
lean_dec_ref_known(v_a_2374_, 2);
v_a_2374_ = v_k_2431_;
goto _start;
}
default: 
{
uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_dec_ref(v_a_2374_);
lean_dec_ref(v_f_2373_);
v___x_2433_ = 0;
v___x_2434_ = lean_box(v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
return v___x_2435_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(uint8_t v_pu_2436_, lean_object* v_f_2437_, lean_object* v_as_2438_, size_t v_i_2439_, size_t v_stop_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
uint8_t v___x_2446_; 
v___x_2446_ = lean_usize_dec_eq(v_i_2439_, v_stop_2440_);
if (v___x_2446_ == 0)
{
uint8_t v___x_2447_; lean_object* v___y_2449_; lean_object* v___x_2464_; 
v___x_2447_ = 1;
v___x_2464_ = lean_array_uget_borrowed(v_as_2438_, v_i_2439_);
switch(lean_obj_tag(v___x_2464_))
{
case 0:
{
lean_object* v_code_2465_; 
v_code_2465_ = lean_ctor_get(v___x_2464_, 2);
lean_inc_ref(v_code_2465_);
v___y_2449_ = v_code_2465_;
goto v___jp_2448_;
}
case 1:
{
lean_object* v_code_2466_; 
v_code_2466_ = lean_ctor_get(v___x_2464_, 1);
lean_inc_ref(v_code_2466_);
v___y_2449_ = v_code_2466_;
goto v___jp_2448_;
}
default: 
{
lean_object* v_code_2467_; 
v_code_2467_ = lean_ctor_get(v___x_2464_, 0);
lean_inc_ref(v_code_2467_);
v___y_2449_ = v_code_2467_;
goto v___jp_2448_;
}
}
v___jp_2448_:
{
lean_object* v___x_2450_; 
lean_inc_ref(v_f_2437_);
v___x_2450_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2436_, v_f_2437_, v___y_2449_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2463_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2463_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2463_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
uint8_t v___x_2455_; 
v___x_2455_ = lean_unbox(v_a_2451_);
lean_dec(v_a_2451_);
if (v___x_2455_ == 0)
{
size_t v___x_2456_; size_t v___x_2457_; 
lean_del_object(v___x_2453_);
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_add(v_i_2439_, v___x_2456_);
v_i_2439_ = v___x_2457_;
goto _start;
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2461_; 
lean_dec_ref(v_f_2437_);
v___x_2459_ = lean_box(v___x_2447_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2459_);
v___x_2461_ = v___x_2453_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_dec_ref(v_f_2437_);
return v___x_2450_;
}
}
}
else
{
uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec_ref(v_f_2437_);
v___x_2468_ = 0;
v___x_2469_ = lean_box(v___x_2468_);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
return v___x_2470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0___boxed(lean_object* v_pu_2471_, lean_object* v_f_2472_, lean_object* v_as_2473_, lean_object* v_i_2474_, lean_object* v_stop_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v_pu_boxed_2481_; size_t v_i_boxed_2482_; size_t v_stop_boxed_2483_; lean_object* v_res_2484_; 
v_pu_boxed_2481_ = lean_unbox(v_pu_2471_);
v_i_boxed_2482_ = lean_unbox_usize(v_i_2474_);
lean_dec(v_i_2474_);
v_stop_boxed_2483_ = lean_unbox_usize(v_stop_2475_);
lean_dec(v_stop_2475_);
v_res_2484_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_boxed_2481_, v_f_2472_, v_as_2473_, v_i_boxed_2482_, v_stop_boxed_2483_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v_as_2473_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed(lean_object* v_pu_2485_, lean_object* v_f_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
uint8_t v_pu_boxed_2493_; lean_object* v_res_2494_; 
v_pu_boxed_2493_ = lean_unbox(v_pu_2485_);
v_res_2494_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_boxed_2493_, v_f_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(uint8_t v_pu_2495_, lean_object* v_f_2496_, lean_object* v_as_2497_, size_t v_i_2498_, size_t v_stop_2499_, lean_object* v_b_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
uint8_t v___x_2506_; 
v___x_2506_ = lean_usize_dec_eq(v_i_2498_, v_stop_2499_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; lean_object* v_value_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2507_ = lean_array_uget_borrowed(v_as_2497_, v_i_2498_);
v_value_2508_ = lean_ctor_get(v___x_2507_, 1);
v___x_2509_ = lean_box(v_pu_2495_);
lean_inc_ref(v_f_2496_);
v___x_2510_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed), 8, 2);
lean_closure_set(v___x_2510_, 0, v___x_2509_);
lean_closure_set(v___x_2510_, 1, v_f_2496_);
lean_inc_ref(v_value_2508_);
v___x_2511_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2508_, v___x_2510_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v_a_2514_; uint8_t v___x_2518_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v___x_2518_ = lean_unbox(v_a_2512_);
lean_dec(v_a_2512_);
if (v___x_2518_ == 0)
{
v_a_2514_ = v_b_2500_;
goto v___jp_2513_;
}
else
{
lean_object* v___x_2519_; 
lean_inc(v___x_2507_);
v___x_2519_ = lean_array_push(v_b_2500_, v___x_2507_);
v_a_2514_ = v___x_2519_;
goto v___jp_2513_;
}
v___jp_2513_:
{
size_t v___x_2515_; size_t v___x_2516_; 
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_add(v_i_2498_, v___x_2515_);
v_i_2498_ = v___x_2516_;
v_b_2500_ = v_a_2514_;
goto _start;
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec_ref(v_b_2500_);
lean_dec_ref(v_f_2496_);
v_a_2520_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2511_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2511_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v___x_2528_; 
lean_dec_ref(v_f_2496_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v_b_2500_);
return v___x_2528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0___boxed(lean_object* v_pu_2529_, lean_object* v_f_2530_, lean_object* v_as_2531_, lean_object* v_i_2532_, lean_object* v_stop_2533_, lean_object* v_b_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
uint8_t v_pu_boxed_2540_; size_t v_i_boxed_2541_; size_t v_stop_boxed_2542_; lean_object* v_res_2543_; 
v_pu_boxed_2540_ = lean_unbox(v_pu_2529_);
v_i_boxed_2541_ = lean_unbox_usize(v_i_2532_);
lean_dec(v_i_2532_);
v_stop_boxed_2542_ = lean_unbox_usize(v_stop_2533_);
lean_dec(v_stop_2533_);
v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_boxed_2540_, v_f_2530_, v_as_2531_, v_i_boxed_2541_, v_stop_boxed_2542_, v_b_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v_as_2531_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp(uint8_t v_pu_2544_, lean_object* v_f_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = lean_array_get_size(v_a_2546_);
v___x_2554_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2555_ = lean_nat_dec_lt(v___x_2552_, v___x_2553_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; 
lean_dec_ref(v_f_2545_);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
return v___x_2556_;
}
else
{
size_t v___x_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = lean_usize_of_nat(v___x_2553_);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2544_, v_f_2545_, v_a_2546_, v___x_2557_, v___x_2558_, v___x_2554_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp___boxed(lean_object* v_pu_2560_, lean_object* v_f_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
uint8_t v_pu_boxed_2568_; lean_object* v_res_2569_; 
v_pu_boxed_2568_ = lean_unbox(v_pu_2560_);
v_res_2569_ = l_Lean_Compiler_LCNF_Probe_filterByJmp(v_pu_boxed_2568_, v_f_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
lean_dec(v_a_2566_);
lean_dec_ref(v_a_2565_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec_ref(v_a_2562_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(uint8_t v_pu_2570_, lean_object* v_f_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
switch(lean_obj_tag(v_a_2572_))
{
case 0:
{
lean_object* v_k_2578_; 
v_k_2578_ = lean_ctor_get(v_a_2572_, 1);
lean_inc_ref(v_k_2578_);
lean_dec_ref_known(v_a_2572_, 2);
v_a_2572_ = v_k_2578_;
goto _start;
}
case 1:
{
lean_object* v_decl_2580_; lean_object* v_k_2581_; lean_object* v_value_2582_; lean_object* v___x_2583_; 
v_decl_2580_ = lean_ctor_get(v_a_2572_, 0);
lean_inc_ref(v_decl_2580_);
v_k_2581_ = lean_ctor_get(v_a_2572_, 1);
lean_inc_ref(v_k_2581_);
lean_dec_ref_known(v_a_2572_, 2);
v_value_2582_ = lean_ctor_get(v_decl_2580_, 4);
lean_inc_ref(v_value_2582_);
lean_dec_ref(v_decl_2580_);
lean_inc_ref(v_f_2571_);
v___x_2583_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2570_, v_f_2571_, v_value_2582_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; uint8_t v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
v___x_2585_ = lean_unbox(v_a_2584_);
lean_dec(v_a_2584_);
if (v___x_2585_ == 0)
{
lean_dec_ref_known(v___x_2583_, 1);
v_a_2572_ = v_k_2581_;
goto _start;
}
else
{
lean_dec_ref(v_k_2581_);
lean_dec_ref(v_f_2571_);
return v___x_2583_;
}
}
else
{
lean_dec_ref(v_k_2581_);
lean_dec_ref(v_f_2571_);
return v___x_2583_;
}
}
case 2:
{
lean_object* v_decl_2587_; lean_object* v_k_2588_; lean_object* v_value_2589_; lean_object* v___x_2590_; 
v_decl_2587_ = lean_ctor_get(v_a_2572_, 0);
lean_inc_ref(v_decl_2587_);
v_k_2588_ = lean_ctor_get(v_a_2572_, 1);
lean_inc_ref(v_k_2588_);
lean_dec_ref_known(v_a_2572_, 2);
v_value_2589_ = lean_ctor_get(v_decl_2587_, 4);
lean_inc_ref(v_value_2589_);
lean_dec_ref(v_decl_2587_);
lean_inc_ref(v_f_2571_);
v___x_2590_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2570_, v_f_2571_, v_value_2589_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; uint8_t v___x_2592_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
v___x_2592_ = lean_unbox(v_a_2591_);
lean_dec(v_a_2591_);
if (v___x_2592_ == 0)
{
lean_dec_ref_known(v___x_2590_, 1);
v_a_2572_ = v_k_2588_;
goto _start;
}
else
{
lean_dec_ref(v_k_2588_);
lean_dec_ref(v_f_2571_);
return v___x_2590_;
}
}
else
{
lean_dec_ref(v_k_2588_);
lean_dec_ref(v_f_2571_);
return v___x_2590_;
}
}
case 4:
{
lean_object* v_cases_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2613_; 
v_cases_2594_ = lean_ctor_get(v_a_2572_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_a_2572_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2596_ = v_a_2572_;
v_isShared_2597_ = v_isSharedCheck_2613_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_cases_2594_);
lean_dec(v_a_2572_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2613_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v_alts_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_alts_2598_ = lean_ctor_get(v_cases_2594_, 3);
lean_inc_ref(v_alts_2598_);
lean_dec_ref(v_cases_2594_);
v___x_2599_ = lean_unsigned_to_nat(0u);
v___x_2600_ = lean_array_get_size(v_alts_2598_);
v___x_2601_ = lean_nat_dec_lt(v___x_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v___x_2604_; 
lean_dec_ref(v_alts_2598_);
lean_dec_ref(v_f_2571_);
v___x_2602_ = lean_box(v___x_2601_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set_tag(v___x_2596_, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2602_);
v___x_2604_ = v___x_2596_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
else
{
if (v___x_2601_ == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_dec_ref(v_alts_2598_);
lean_dec_ref(v_f_2571_);
v___x_2606_ = lean_box(v___x_2601_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set_tag(v___x_2596_, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2606_);
v___x_2608_ = v___x_2596_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
else
{
size_t v___x_2610_; size_t v___x_2611_; lean_object* v___x_2612_; 
lean_del_object(v___x_2596_);
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = lean_usize_of_nat(v___x_2600_);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_2570_, v_f_2571_, v_alts_2598_, v___x_2610_, v___x_2611_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
lean_dec_ref(v_alts_2598_);
return v___x_2612_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2614_; lean_object* v___x_2615_; 
v_fvarId_2614_ = lean_ctor_get(v_a_2572_, 0);
lean_inc(v_fvarId_2614_);
lean_dec_ref_known(v_a_2572_, 1);
lean_inc(v_a_2576_);
lean_inc_ref(v_a_2575_);
lean_inc(v_a_2574_);
lean_inc_ref(v_a_2573_);
v___x_2615_ = lean_apply_6(v_f_2571_, v_fvarId_2614_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, lean_box(0));
return v___x_2615_;
}
case 7:
{
lean_object* v_k_2616_; 
v_k_2616_ = lean_ctor_get(v_a_2572_, 3);
lean_inc_ref(v_k_2616_);
lean_dec_ref_known(v_a_2572_, 4);
v_a_2572_ = v_k_2616_;
goto _start;
}
case 8:
{
lean_object* v_k_2618_; 
v_k_2618_ = lean_ctor_get(v_a_2572_, 3);
lean_inc_ref(v_k_2618_);
lean_dec_ref_known(v_a_2572_, 4);
v_a_2572_ = v_k_2618_;
goto _start;
}
case 9:
{
lean_object* v_k_2620_; 
v_k_2620_ = lean_ctor_get(v_a_2572_, 5);
lean_inc_ref(v_k_2620_);
lean_dec_ref_known(v_a_2572_, 6);
v_a_2572_ = v_k_2620_;
goto _start;
}
case 10:
{
lean_object* v_k_2622_; 
v_k_2622_ = lean_ctor_get(v_a_2572_, 2);
lean_inc_ref(v_k_2622_);
lean_dec_ref_known(v_a_2572_, 3);
v_a_2572_ = v_k_2622_;
goto _start;
}
case 11:
{
lean_object* v_k_2624_; 
v_k_2624_ = lean_ctor_get(v_a_2572_, 2);
lean_inc_ref(v_k_2624_);
lean_dec_ref_known(v_a_2572_, 3);
v_a_2572_ = v_k_2624_;
goto _start;
}
case 12:
{
lean_object* v_k_2626_; 
v_k_2626_ = lean_ctor_get(v_a_2572_, 3);
lean_inc_ref(v_k_2626_);
lean_dec_ref_known(v_a_2572_, 4);
v_a_2572_ = v_k_2626_;
goto _start;
}
case 13:
{
lean_object* v_k_2628_; 
v_k_2628_ = lean_ctor_get(v_a_2572_, 1);
lean_inc_ref(v_k_2628_);
lean_dec_ref_known(v_a_2572_, 2);
v_a_2572_ = v_k_2628_;
goto _start;
}
default: 
{
uint8_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec_ref(v_a_2572_);
lean_dec_ref(v_f_2571_);
v___x_2630_ = 0;
v___x_2631_ = lean_box(v___x_2630_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(uint8_t v_pu_2633_, lean_object* v_f_2634_, lean_object* v_as_2635_, size_t v_i_2636_, size_t v_stop_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
uint8_t v___x_2643_; 
v___x_2643_ = lean_usize_dec_eq(v_i_2636_, v_stop_2637_);
if (v___x_2643_ == 0)
{
uint8_t v___x_2644_; lean_object* v___y_2646_; lean_object* v___x_2661_; 
v___x_2644_ = 1;
v___x_2661_ = lean_array_uget_borrowed(v_as_2635_, v_i_2636_);
switch(lean_obj_tag(v___x_2661_))
{
case 0:
{
lean_object* v_code_2662_; 
v_code_2662_ = lean_ctor_get(v___x_2661_, 2);
lean_inc_ref(v_code_2662_);
v___y_2646_ = v_code_2662_;
goto v___jp_2645_;
}
case 1:
{
lean_object* v_code_2663_; 
v_code_2663_ = lean_ctor_get(v___x_2661_, 1);
lean_inc_ref(v_code_2663_);
v___y_2646_ = v_code_2663_;
goto v___jp_2645_;
}
default: 
{
lean_object* v_code_2664_; 
v_code_2664_ = lean_ctor_get(v___x_2661_, 0);
lean_inc_ref(v_code_2664_);
v___y_2646_ = v_code_2664_;
goto v___jp_2645_;
}
}
v___jp_2645_:
{
lean_object* v___x_2647_; 
lean_inc_ref(v_f_2634_);
v___x_2647_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2633_, v_f_2634_, v___y_2646_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2660_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2650_ = v___x_2647_;
v_isShared_2651_ = v_isSharedCheck_2660_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2660_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
uint8_t v___x_2652_; 
v___x_2652_ = lean_unbox(v_a_2648_);
lean_dec(v_a_2648_);
if (v___x_2652_ == 0)
{
size_t v___x_2653_; size_t v___x_2654_; 
lean_del_object(v___x_2650_);
v___x_2653_ = ((size_t)1ULL);
v___x_2654_ = lean_usize_add(v_i_2636_, v___x_2653_);
v_i_2636_ = v___x_2654_;
goto _start;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2658_; 
lean_dec_ref(v_f_2634_);
v___x_2656_ = lean_box(v___x_2644_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2656_);
v___x_2658_ = v___x_2650_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_dec_ref(v_f_2634_);
return v___x_2647_;
}
}
}
else
{
uint8_t v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec_ref(v_f_2634_);
v___x_2665_ = 0;
v___x_2666_ = lean_box(v___x_2665_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0___boxed(lean_object* v_pu_2668_, lean_object* v_f_2669_, lean_object* v_as_2670_, lean_object* v_i_2671_, lean_object* v_stop_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
uint8_t v_pu_boxed_2678_; size_t v_i_boxed_2679_; size_t v_stop_boxed_2680_; lean_object* v_res_2681_; 
v_pu_boxed_2678_ = lean_unbox(v_pu_2668_);
v_i_boxed_2679_ = lean_unbox_usize(v_i_2671_);
lean_dec(v_i_2671_);
v_stop_boxed_2680_ = lean_unbox_usize(v_stop_2672_);
lean_dec(v_stop_2672_);
v_res_2681_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_boxed_2678_, v_f_2669_, v_as_2670_, v_i_boxed_2679_, v_stop_boxed_2680_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v_as_2670_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed(lean_object* v_pu_2682_, lean_object* v_f_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
uint8_t v_pu_boxed_2690_; lean_object* v_res_2691_; 
v_pu_boxed_2690_ = lean_unbox(v_pu_2682_);
v_res_2691_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_boxed_2690_, v_f_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(uint8_t v_pu_2692_, lean_object* v_f_2693_, lean_object* v_as_2694_, size_t v_i_2695_, size_t v_stop_2696_, lean_object* v_b_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
uint8_t v___x_2703_; 
v___x_2703_ = lean_usize_dec_eq(v_i_2695_, v_stop_2696_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v_value_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2704_ = lean_array_uget_borrowed(v_as_2694_, v_i_2695_);
v_value_2705_ = lean_ctor_get(v___x_2704_, 1);
v___x_2706_ = lean_box(v_pu_2692_);
lean_inc_ref(v_f_2693_);
v___x_2707_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed), 8, 2);
lean_closure_set(v___x_2707_, 0, v___x_2706_);
lean_closure_set(v___x_2707_, 1, v_f_2693_);
lean_inc_ref(v_value_2705_);
v___x_2708_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2705_, v___x_2707_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v_a_2711_; uint8_t v___x_2715_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2708_, 1);
v___x_2715_ = lean_unbox(v_a_2709_);
lean_dec(v_a_2709_);
if (v___x_2715_ == 0)
{
v_a_2711_ = v_b_2697_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2716_; 
lean_inc(v___x_2704_);
v___x_2716_ = lean_array_push(v_b_2697_, v___x_2704_);
v_a_2711_ = v___x_2716_;
goto v___jp_2710_;
}
v___jp_2710_:
{
size_t v___x_2712_; size_t v___x_2713_; 
v___x_2712_ = ((size_t)1ULL);
v___x_2713_ = lean_usize_add(v_i_2695_, v___x_2712_);
v_i_2695_ = v___x_2713_;
v_b_2697_ = v_a_2711_;
goto _start;
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec_ref(v_b_2697_);
lean_dec_ref(v_f_2693_);
v_a_2717_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2708_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2708_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v___x_2725_; 
lean_dec_ref(v_f_2693_);
v___x_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2725_, 0, v_b_2697_);
return v___x_2725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0___boxed(lean_object* v_pu_2726_, lean_object* v_f_2727_, lean_object* v_as_2728_, lean_object* v_i_2729_, lean_object* v_stop_2730_, lean_object* v_b_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
uint8_t v_pu_boxed_2737_; size_t v_i_boxed_2738_; size_t v_stop_boxed_2739_; lean_object* v_res_2740_; 
v_pu_boxed_2737_ = lean_unbox(v_pu_2726_);
v_i_boxed_2738_ = lean_unbox_usize(v_i_2729_);
lean_dec(v_i_2729_);
v_stop_boxed_2739_ = lean_unbox_usize(v_stop_2730_);
lean_dec(v_stop_2730_);
v_res_2740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_boxed_2737_, v_f_2727_, v_as_2728_, v_i_boxed_2738_, v_stop_boxed_2739_, v_b_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v_as_2728_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn(uint8_t v_pu_2741_, lean_object* v_f_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
v___x_2749_ = lean_unsigned_to_nat(0u);
v___x_2750_ = lean_array_get_size(v_a_2743_);
v___x_2751_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2752_ = lean_nat_dec_lt(v___x_2749_, v___x_2750_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; 
lean_dec_ref(v_f_2742_);
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
return v___x_2753_;
}
else
{
size_t v___x_2754_; size_t v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = ((size_t)0ULL);
v___x_2755_ = lean_usize_of_nat(v___x_2750_);
v___x_2756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2741_, v_f_2742_, v_a_2743_, v___x_2754_, v___x_2755_, v___x_2751_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn___boxed(lean_object* v_pu_2757_, lean_object* v_f_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
uint8_t v_pu_boxed_2765_; lean_object* v_res_2766_; 
v_pu_boxed_2765_ = lean_unbox(v_pu_2757_);
v_res_2766_ = l_Lean_Compiler_LCNF_Probe_filterByReturn(v_pu_boxed_2765_, v_f_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec_ref(v_a_2759_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(uint8_t v_pu_2767_, lean_object* v_f_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
switch(lean_obj_tag(v_a_2769_))
{
case 0:
{
lean_object* v_k_2775_; 
v_k_2775_ = lean_ctor_get(v_a_2769_, 1);
lean_inc_ref(v_k_2775_);
lean_dec_ref_known(v_a_2769_, 2);
v_a_2769_ = v_k_2775_;
goto _start;
}
case 1:
{
lean_object* v_decl_2777_; lean_object* v_k_2778_; lean_object* v_value_2779_; lean_object* v___x_2780_; 
v_decl_2777_ = lean_ctor_get(v_a_2769_, 0);
lean_inc_ref(v_decl_2777_);
v_k_2778_ = lean_ctor_get(v_a_2769_, 1);
lean_inc_ref(v_k_2778_);
lean_dec_ref_known(v_a_2769_, 2);
v_value_2779_ = lean_ctor_get(v_decl_2777_, 4);
lean_inc_ref(v_value_2779_);
lean_dec_ref(v_decl_2777_);
lean_inc_ref(v_f_2768_);
v___x_2780_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2767_, v_f_2768_, v_value_2779_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; uint8_t v___x_2782_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
v___x_2782_ = lean_unbox(v_a_2781_);
lean_dec(v_a_2781_);
if (v___x_2782_ == 0)
{
lean_dec_ref_known(v___x_2780_, 1);
v_a_2769_ = v_k_2778_;
goto _start;
}
else
{
lean_dec_ref(v_k_2778_);
lean_dec_ref(v_f_2768_);
return v___x_2780_;
}
}
else
{
lean_dec_ref(v_k_2778_);
lean_dec_ref(v_f_2768_);
return v___x_2780_;
}
}
case 2:
{
lean_object* v_decl_2784_; lean_object* v_k_2785_; lean_object* v_value_2786_; lean_object* v___x_2787_; 
v_decl_2784_ = lean_ctor_get(v_a_2769_, 0);
lean_inc_ref(v_decl_2784_);
v_k_2785_ = lean_ctor_get(v_a_2769_, 1);
lean_inc_ref(v_k_2785_);
lean_dec_ref_known(v_a_2769_, 2);
v_value_2786_ = lean_ctor_get(v_decl_2784_, 4);
lean_inc_ref(v_value_2786_);
lean_dec_ref(v_decl_2784_);
lean_inc_ref(v_f_2768_);
v___x_2787_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2767_, v_f_2768_, v_value_2786_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; uint8_t v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
v___x_2789_ = lean_unbox(v_a_2788_);
lean_dec(v_a_2788_);
if (v___x_2789_ == 0)
{
lean_dec_ref_known(v___x_2787_, 1);
v_a_2769_ = v_k_2785_;
goto _start;
}
else
{
lean_dec_ref(v_k_2785_);
lean_dec_ref(v_f_2768_);
return v___x_2787_;
}
}
else
{
lean_dec_ref(v_k_2785_);
lean_dec_ref(v_f_2768_);
return v___x_2787_;
}
}
case 4:
{
lean_object* v_cases_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2810_; 
v_cases_2791_ = lean_ctor_get(v_a_2769_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_a_2769_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2793_ = v_a_2769_;
v_isShared_2794_ = v_isSharedCheck_2810_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_cases_2791_);
lean_dec(v_a_2769_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2810_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_alts_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v_alts_2795_ = lean_ctor_get(v_cases_2791_, 3);
lean_inc_ref(v_alts_2795_);
lean_dec_ref(v_cases_2791_);
v___x_2796_ = lean_unsigned_to_nat(0u);
v___x_2797_ = lean_array_get_size(v_alts_2795_);
v___x_2798_ = lean_nat_dec_lt(v___x_2796_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
lean_dec_ref(v_alts_2795_);
lean_dec_ref(v_f_2768_);
v___x_2799_ = lean_box(v___x_2798_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set_tag(v___x_2793_, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2799_);
v___x_2801_ = v___x_2793_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
else
{
if (v___x_2798_ == 0)
{
lean_object* v___x_2803_; lean_object* v___x_2805_; 
lean_dec_ref(v_alts_2795_);
lean_dec_ref(v_f_2768_);
v___x_2803_ = lean_box(v___x_2798_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set_tag(v___x_2793_, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2803_);
v___x_2805_ = v___x_2793_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
else
{
size_t v___x_2807_; size_t v___x_2808_; lean_object* v___x_2809_; 
lean_del_object(v___x_2793_);
v___x_2807_ = ((size_t)0ULL);
v___x_2808_ = lean_usize_of_nat(v___x_2797_);
v___x_2809_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_2767_, v_f_2768_, v_alts_2795_, v___x_2807_, v___x_2808_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
lean_dec_ref(v_alts_2795_);
return v___x_2809_;
}
}
}
}
case 6:
{
lean_object* v_type_2811_; lean_object* v___x_2812_; 
v_type_2811_ = lean_ctor_get(v_a_2769_, 0);
lean_inc_ref(v_type_2811_);
lean_dec_ref_known(v_a_2769_, 1);
lean_inc(v_a_2773_);
lean_inc_ref(v_a_2772_);
lean_inc(v_a_2771_);
lean_inc_ref(v_a_2770_);
v___x_2812_ = lean_apply_6(v_f_2768_, v_type_2811_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, lean_box(0));
return v___x_2812_;
}
case 7:
{
lean_object* v_k_2813_; 
v_k_2813_ = lean_ctor_get(v_a_2769_, 3);
lean_inc_ref(v_k_2813_);
lean_dec_ref_known(v_a_2769_, 4);
v_a_2769_ = v_k_2813_;
goto _start;
}
case 8:
{
lean_object* v_k_2815_; 
v_k_2815_ = lean_ctor_get(v_a_2769_, 3);
lean_inc_ref(v_k_2815_);
lean_dec_ref_known(v_a_2769_, 4);
v_a_2769_ = v_k_2815_;
goto _start;
}
case 9:
{
lean_object* v_k_2817_; 
v_k_2817_ = lean_ctor_get(v_a_2769_, 5);
lean_inc_ref(v_k_2817_);
lean_dec_ref_known(v_a_2769_, 6);
v_a_2769_ = v_k_2817_;
goto _start;
}
case 10:
{
lean_object* v_k_2819_; 
v_k_2819_ = lean_ctor_get(v_a_2769_, 2);
lean_inc_ref(v_k_2819_);
lean_dec_ref_known(v_a_2769_, 3);
v_a_2769_ = v_k_2819_;
goto _start;
}
case 11:
{
lean_object* v_k_2821_; 
v_k_2821_ = lean_ctor_get(v_a_2769_, 2);
lean_inc_ref(v_k_2821_);
lean_dec_ref_known(v_a_2769_, 3);
v_a_2769_ = v_k_2821_;
goto _start;
}
case 12:
{
lean_object* v_k_2823_; 
v_k_2823_ = lean_ctor_get(v_a_2769_, 3);
lean_inc_ref(v_k_2823_);
lean_dec_ref_known(v_a_2769_, 4);
v_a_2769_ = v_k_2823_;
goto _start;
}
case 13:
{
lean_object* v_k_2825_; 
v_k_2825_ = lean_ctor_get(v_a_2769_, 1);
lean_inc_ref(v_k_2825_);
lean_dec_ref_known(v_a_2769_, 2);
v_a_2769_ = v_k_2825_;
goto _start;
}
default: 
{
uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_dec_ref(v_a_2769_);
lean_dec_ref(v_f_2768_);
v___x_2827_ = 0;
v___x_2828_ = lean_box(v___x_2827_);
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
return v___x_2829_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(uint8_t v_pu_2830_, lean_object* v_f_2831_, lean_object* v_as_2832_, size_t v_i_2833_, size_t v_stop_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
uint8_t v___x_2840_; 
v___x_2840_ = lean_usize_dec_eq(v_i_2833_, v_stop_2834_);
if (v___x_2840_ == 0)
{
uint8_t v___x_2841_; lean_object* v___y_2843_; lean_object* v___x_2858_; 
v___x_2841_ = 1;
v___x_2858_ = lean_array_uget_borrowed(v_as_2832_, v_i_2833_);
switch(lean_obj_tag(v___x_2858_))
{
case 0:
{
lean_object* v_code_2859_; 
v_code_2859_ = lean_ctor_get(v___x_2858_, 2);
lean_inc_ref(v_code_2859_);
v___y_2843_ = v_code_2859_;
goto v___jp_2842_;
}
case 1:
{
lean_object* v_code_2860_; 
v_code_2860_ = lean_ctor_get(v___x_2858_, 1);
lean_inc_ref(v_code_2860_);
v___y_2843_ = v_code_2860_;
goto v___jp_2842_;
}
default: 
{
lean_object* v_code_2861_; 
v_code_2861_ = lean_ctor_get(v___x_2858_, 0);
lean_inc_ref(v_code_2861_);
v___y_2843_ = v_code_2861_;
goto v___jp_2842_;
}
}
v___jp_2842_:
{
lean_object* v___x_2844_; 
lean_inc_ref(v_f_2831_);
v___x_2844_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2830_, v_f_2831_, v___y_2843_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2857_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2857_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2857_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_unbox(v_a_2845_);
lean_dec(v_a_2845_);
if (v___x_2849_ == 0)
{
size_t v___x_2850_; size_t v___x_2851_; 
lean_del_object(v___x_2847_);
v___x_2850_ = ((size_t)1ULL);
v___x_2851_ = lean_usize_add(v_i_2833_, v___x_2850_);
v_i_2833_ = v___x_2851_;
goto _start;
}
else
{
lean_object* v___x_2853_; lean_object* v___x_2855_; 
lean_dec_ref(v_f_2831_);
v___x_2853_ = lean_box(v___x_2841_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2853_);
v___x_2855_ = v___x_2847_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_dec_ref(v_f_2831_);
return v___x_2844_;
}
}
}
else
{
uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
lean_dec_ref(v_f_2831_);
v___x_2862_ = 0;
v___x_2863_ = lean_box(v___x_2862_);
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0___boxed(lean_object* v_pu_2865_, lean_object* v_f_2866_, lean_object* v_as_2867_, lean_object* v_i_2868_, lean_object* v_stop_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
uint8_t v_pu_boxed_2875_; size_t v_i_boxed_2876_; size_t v_stop_boxed_2877_; lean_object* v_res_2878_; 
v_pu_boxed_2875_ = lean_unbox(v_pu_2865_);
v_i_boxed_2876_ = lean_unbox_usize(v_i_2868_);
lean_dec(v_i_2868_);
v_stop_boxed_2877_ = lean_unbox_usize(v_stop_2869_);
lean_dec(v_stop_2869_);
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_boxed_2875_, v_f_2866_, v_as_2867_, v_i_boxed_2876_, v_stop_boxed_2877_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec_ref(v_as_2867_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed(lean_object* v_pu_2879_, lean_object* v_f_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
uint8_t v_pu_boxed_2887_; lean_object* v_res_2888_; 
v_pu_boxed_2887_ = lean_unbox(v_pu_2879_);
v_res_2888_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_boxed_2887_, v_f_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(uint8_t v_pu_2889_, lean_object* v_f_2890_, lean_object* v_as_2891_, size_t v_i_2892_, size_t v_stop_2893_, lean_object* v_b_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
uint8_t v___x_2900_; 
v___x_2900_ = lean_usize_dec_eq(v_i_2892_, v_stop_2893_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v_value_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2901_ = lean_array_uget_borrowed(v_as_2891_, v_i_2892_);
v_value_2902_ = lean_ctor_get(v___x_2901_, 1);
v___x_2903_ = lean_box(v_pu_2889_);
lean_inc_ref(v_f_2890_);
v___x_2904_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed), 8, 2);
lean_closure_set(v___x_2904_, 0, v___x_2903_);
lean_closure_set(v___x_2904_, 1, v_f_2890_);
lean_inc_ref(v_value_2902_);
v___x_2905_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2902_, v___x_2904_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v_a_2908_; uint8_t v___x_2912_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2912_ = lean_unbox(v_a_2906_);
lean_dec(v_a_2906_);
if (v___x_2912_ == 0)
{
v_a_2908_ = v_b_2894_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_2913_; 
lean_inc(v___x_2901_);
v___x_2913_ = lean_array_push(v_b_2894_, v___x_2901_);
v_a_2908_ = v___x_2913_;
goto v___jp_2907_;
}
v___jp_2907_:
{
size_t v___x_2909_; size_t v___x_2910_; 
v___x_2909_ = ((size_t)1ULL);
v___x_2910_ = lean_usize_add(v_i_2892_, v___x_2909_);
v_i_2892_ = v___x_2910_;
v_b_2894_ = v_a_2908_;
goto _start;
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v_b_2894_);
lean_dec_ref(v_f_2890_);
v_a_2914_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2905_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2905_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_object* v___x_2922_; 
lean_dec_ref(v_f_2890_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v_b_2894_);
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0___boxed(lean_object* v_pu_2923_, lean_object* v_f_2924_, lean_object* v_as_2925_, lean_object* v_i_2926_, lean_object* v_stop_2927_, lean_object* v_b_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
uint8_t v_pu_boxed_2934_; size_t v_i_boxed_2935_; size_t v_stop_boxed_2936_; lean_object* v_res_2937_; 
v_pu_boxed_2934_ = lean_unbox(v_pu_2923_);
v_i_boxed_2935_ = lean_unbox_usize(v_i_2926_);
lean_dec(v_i_2926_);
v_stop_boxed_2936_ = lean_unbox_usize(v_stop_2927_);
lean_dec(v_stop_2927_);
v_res_2937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_boxed_2934_, v_f_2924_, v_as_2925_, v_i_boxed_2935_, v_stop_boxed_2936_, v_b_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v_as_2925_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach(uint8_t v_pu_2938_, lean_object* v_f_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2946_ = lean_unsigned_to_nat(0u);
v___x_2947_ = lean_array_get_size(v_a_2940_);
v___x_2948_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2949_ = lean_nat_dec_lt(v___x_2946_, v___x_2947_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; 
lean_dec_ref(v_f_2939_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
return v___x_2950_;
}
else
{
size_t v___x_2951_; size_t v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = ((size_t)0ULL);
v___x_2952_ = lean_usize_of_nat(v___x_2947_);
v___x_2953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_2938_, v_f_2939_, v_a_2940_, v___x_2951_, v___x_2952_, v___x_2948_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_);
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach___boxed(lean_object* v_pu_2954_, lean_object* v_f_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
uint8_t v_pu_boxed_2962_; lean_object* v_res_2963_; 
v_pu_boxed_2962_ = lean_unbox(v_pu_2954_);
v_res_2963_ = l_Lean_Compiler_LCNF_Probe_filterByUnreach(v_pu_boxed_2962_, v_f_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec_ref(v_a_2956_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(lean_object* v_decl_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_toSignature_2970_; lean_object* v_name_2971_; lean_object* v___x_2972_; 
v_toSignature_2970_ = lean_ctor_get(v_decl_2964_, 0);
v_name_2971_ = lean_ctor_get(v_toSignature_2970_, 0);
lean_inc(v_name_2971_);
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v_name_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed(lean_object* v_decl_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(v_decl_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec_ref(v_decl_2973_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg(lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___x_2987_; lean_object* v_toApplicative_2988_; lean_object* v_toFunctor_2989_; lean_object* v_toSeq_2990_; lean_object* v_toSeqLeft_2991_; lean_object* v_toSeqRight_2992_; lean_object* v___f_2993_; lean_object* v___f_2994_; lean_object* v___f_2995_; lean_object* v___f_2996_; lean_object* v___x_2997_; lean_object* v___f_2998_; lean_object* v___f_2999_; lean_object* v___f_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v_toApplicative_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3036_; 
v___x_2987_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_2988_ = lean_ctor_get(v___x_2987_, 0);
v_toFunctor_2989_ = lean_ctor_get(v_toApplicative_2988_, 0);
v_toSeq_2990_ = lean_ctor_get(v_toApplicative_2988_, 2);
v_toSeqLeft_2991_ = lean_ctor_get(v_toApplicative_2988_, 3);
v_toSeqRight_2992_ = lean_ctor_get(v_toApplicative_2988_, 4);
v___f_2993_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_2994_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2989_, 2);
v___f_2995_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2995_, 0, v_toFunctor_2989_);
v___f_2996_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2996_, 0, v_toFunctor_2989_);
v___x_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___f_2995_);
lean_ctor_set(v___x_2997_, 1, v___f_2996_);
lean_inc(v_toSeqRight_2992_);
v___f_2998_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2998_, 0, v_toSeqRight_2992_);
lean_inc(v_toSeqLeft_2991_);
v___f_2999_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2999_, 0, v_toSeqLeft_2991_);
lean_inc(v_toSeq_2990_);
v___f_3000_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3000_, 0, v_toSeq_2990_);
v___x_3001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2997_);
lean_ctor_set(v___x_3001_, 1, v___f_2993_);
lean_ctor_set(v___x_3001_, 2, v___f_3000_);
lean_ctor_set(v___x_3001_, 3, v___f_2999_);
lean_ctor_set(v___x_3001_, 4, v___f_2998_);
v___x_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
lean_ctor_set(v___x_3002_, 1, v___f_2994_);
v___x_3003_ = l_StateRefT_x27_instMonad___redArg(v___x_3002_);
v_toApplicative_3004_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3036_ == 0)
{
lean_object* v_unused_3037_; 
v_unused_3037_ = lean_ctor_get(v___x_3003_, 1);
lean_dec(v_unused_3037_);
v___x_3006_ = v___x_3003_;
v_isShared_3007_ = v_isSharedCheck_3036_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_toApplicative_3004_);
lean_dec(v___x_3003_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3036_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v_toFunctor_3008_; lean_object* v_toSeq_3009_; lean_object* v_toSeqLeft_3010_; lean_object* v_toSeqRight_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3034_; 
v_toFunctor_3008_ = lean_ctor_get(v_toApplicative_3004_, 0);
v_toSeq_3009_ = lean_ctor_get(v_toApplicative_3004_, 2);
v_toSeqLeft_3010_ = lean_ctor_get(v_toApplicative_3004_, 3);
v_toSeqRight_3011_ = lean_ctor_get(v_toApplicative_3004_, 4);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_toApplicative_3004_);
if (v_isSharedCheck_3034_ == 0)
{
lean_object* v_unused_3035_; 
v_unused_3035_ = lean_ctor_get(v_toApplicative_3004_, 1);
lean_dec(v_unused_3035_);
v___x_3013_ = v_toApplicative_3004_;
v_isShared_3014_ = v_isSharedCheck_3034_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_toSeqRight_3011_);
lean_inc(v_toSeqLeft_3010_);
lean_inc(v_toSeq_3009_);
lean_inc(v_toFunctor_3008_);
lean_dec(v_toApplicative_3004_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3034_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___f_3015_; lean_object* v___f_3016_; lean_object* v___f_3017_; lean_object* v___f_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v___f_3021_; lean_object* v___f_3022_; lean_object* v___f_3023_; lean_object* v___x_3025_; 
v___f_3015_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3016_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3017_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3008_);
v___f_3018_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3018_, 0, v_toFunctor_3008_);
v___f_3019_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3019_, 0, v_toFunctor_3008_);
v___x_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___f_3018_);
lean_ctor_set(v___x_3020_, 1, v___f_3019_);
v___f_3021_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3021_, 0, v_toSeqRight_3011_);
v___f_3022_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3022_, 0, v_toSeqLeft_3010_);
v___f_3023_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3023_, 0, v_toSeq_3009_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 4, v___f_3021_);
lean_ctor_set(v___x_3013_, 3, v___f_3022_);
lean_ctor_set(v___x_3013_, 2, v___f_3023_);
lean_ctor_set(v___x_3013_, 1, v___f_3016_);
lean_ctor_set(v___x_3013_, 0, v___x_3020_);
v___x_3025_ = v___x_3013_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___f_3016_);
lean_ctor_set(v_reuseFailAlloc_3033_, 2, v___f_3023_);
lean_ctor_set(v_reuseFailAlloc_3033_, 3, v___f_3022_);
lean_ctor_set(v_reuseFailAlloc_3033_, 4, v___f_3021_);
v___x_3025_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3027_; 
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 1, v___f_3017_);
lean_ctor_set(v___x_3006_, 0, v___x_3025_);
v___x_3027_ = v___x_3006_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v___f_3017_);
v___x_3027_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
size_t v_sz_3028_; size_t v___x_3029_; lean_object* v___x_127__overap_3030_; lean_object* v___x_3031_; 
v_sz_3028_ = lean_array_size(v_a_2981_);
v___x_3029_ = ((size_t)0ULL);
v___x_127__overap_3030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3027_, v___f_3015_, v_sz_3028_, v___x_3029_, v_a_2981_);
lean_inc(v_a_2985_);
lean_inc_ref(v_a_2984_);
lean_inc(v_a_2983_);
lean_inc_ref(v_a_2982_);
v___x_3031_ = lean_apply_5(v___x_127__overap_3030_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, lean_box(0));
return v___x_3031_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___boxed(lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg(v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames(uint8_t v_pu_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v___x_3052_; lean_object* v_toApplicative_3053_; lean_object* v_toFunctor_3054_; lean_object* v_toSeq_3055_; lean_object* v_toSeqLeft_3056_; lean_object* v_toSeqRight_3057_; lean_object* v___f_3058_; lean_object* v___f_3059_; lean_object* v___f_3060_; lean_object* v___f_3061_; lean_object* v___x_3062_; lean_object* v___f_3063_; lean_object* v___f_3064_; lean_object* v___f_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v_toApplicative_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3101_; 
v___x_3052_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3053_ = lean_ctor_get(v___x_3052_, 0);
v_toFunctor_3054_ = lean_ctor_get(v_toApplicative_3053_, 0);
v_toSeq_3055_ = lean_ctor_get(v_toApplicative_3053_, 2);
v_toSeqLeft_3056_ = lean_ctor_get(v_toApplicative_3053_, 3);
v_toSeqRight_3057_ = lean_ctor_get(v_toApplicative_3053_, 4);
v___f_3058_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3059_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3054_, 2);
v___f_3060_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3060_, 0, v_toFunctor_3054_);
v___f_3061_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3061_, 0, v_toFunctor_3054_);
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___f_3060_);
lean_ctor_set(v___x_3062_, 1, v___f_3061_);
lean_inc(v_toSeqRight_3057_);
v___f_3063_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3063_, 0, v_toSeqRight_3057_);
lean_inc(v_toSeqLeft_3056_);
v___f_3064_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3064_, 0, v_toSeqLeft_3056_);
lean_inc(v_toSeq_3055_);
v___f_3065_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3065_, 0, v_toSeq_3055_);
v___x_3066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3062_);
lean_ctor_set(v___x_3066_, 1, v___f_3058_);
lean_ctor_set(v___x_3066_, 2, v___f_3065_);
lean_ctor_set(v___x_3066_, 3, v___f_3064_);
lean_ctor_set(v___x_3066_, 4, v___f_3063_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v___f_3059_);
v___x_3068_ = l_StateRefT_x27_instMonad___redArg(v___x_3067_);
v_toApplicative_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; 
v_unused_3102_ = lean_ctor_get(v___x_3068_, 1);
lean_dec(v_unused_3102_);
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3101_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_toApplicative_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3101_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v_toFunctor_3073_; lean_object* v_toSeq_3074_; lean_object* v_toSeqLeft_3075_; lean_object* v_toSeqRight_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3099_; 
v_toFunctor_3073_ = lean_ctor_get(v_toApplicative_3069_, 0);
v_toSeq_3074_ = lean_ctor_get(v_toApplicative_3069_, 2);
v_toSeqLeft_3075_ = lean_ctor_get(v_toApplicative_3069_, 3);
v_toSeqRight_3076_ = lean_ctor_get(v_toApplicative_3069_, 4);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_toApplicative_3069_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v_toApplicative_3069_, 1);
lean_dec(v_unused_3100_);
v___x_3078_ = v_toApplicative_3069_;
v_isShared_3079_ = v_isSharedCheck_3099_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_toSeqRight_3076_);
lean_inc(v_toSeqLeft_3075_);
lean_inc(v_toSeq_3074_);
lean_inc(v_toFunctor_3073_);
lean_dec(v_toApplicative_3069_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3099_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___f_3080_; lean_object* v___f_3081_; lean_object* v___f_3082_; lean_object* v___f_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; lean_object* v___f_3086_; lean_object* v___f_3087_; lean_object* v___f_3088_; lean_object* v___x_3090_; 
v___f_3080_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3081_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3082_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3073_);
v___f_3083_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3083_, 0, v_toFunctor_3073_);
v___f_3084_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3084_, 0, v_toFunctor_3073_);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___f_3083_);
lean_ctor_set(v___x_3085_, 1, v___f_3084_);
v___f_3086_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3086_, 0, v_toSeqRight_3076_);
v___f_3087_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3087_, 0, v_toSeqLeft_3075_);
v___f_3088_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3088_, 0, v_toSeq_3074_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 4, v___f_3086_);
lean_ctor_set(v___x_3078_, 3, v___f_3087_);
lean_ctor_set(v___x_3078_, 2, v___f_3088_);
lean_ctor_set(v___x_3078_, 1, v___f_3081_);
lean_ctor_set(v___x_3078_, 0, v___x_3085_);
v___x_3090_ = v___x_3078_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___f_3081_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v___f_3088_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v___f_3087_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v___f_3086_);
v___x_3090_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3092_; 
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 1, v___f_3082_);
lean_ctor_set(v___x_3071_, 0, v___x_3090_);
v___x_3092_ = v___x_3071_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___f_3082_);
v___x_3092_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
size_t v_sz_3093_; size_t v___x_3094_; lean_object* v___x_185__overap_3095_; lean_object* v___x_3096_; 
v_sz_3093_ = lean_array_size(v_a_3046_);
v___x_3094_ = ((size_t)0ULL);
v___x_185__overap_3095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3092_, v___f_3080_, v_sz_3093_, v___x_3094_, v_a_3046_);
lean_inc(v_a_3050_);
lean_inc_ref(v_a_3049_);
lean_inc(v_a_3048_);
lean_inc_ref(v_a_3047_);
v___x_3096_ = lean_apply_5(v___x_185__overap_3095_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, lean_box(0));
return v___x_3096_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___boxed(lean_object* v_pu_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_){
_start:
{
uint8_t v_pu_boxed_3110_; lean_object* v_res_3111_; 
v_pu_boxed_3110_ = lean_unbox(v_pu_3103_);
v_res_3111_ = l_Lean_Compiler_LCNF_Probe_declNames(v_pu_boxed_3110_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_);
lean_dec(v_a_3108_);
lean_dec_ref(v_a_3107_);
lean_dec(v_a_3106_);
lean_dec_ref(v_a_3105_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(lean_object* v_inst_3112_, lean_object* v_x_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_apply_1(v_inst_3112_, v_x_3113_);
v___x_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed(lean_object* v_inst_3121_, lean_object* v_x_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(v_inst_3121_, v_x_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg(lean_object* v_inst_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v___x_3136_; lean_object* v_toApplicative_3137_; lean_object* v_toFunctor_3138_; lean_object* v_toSeq_3139_; lean_object* v_toSeqLeft_3140_; lean_object* v_toSeqRight_3141_; lean_object* v___f_3142_; lean_object* v___f_3143_; lean_object* v___f_3144_; lean_object* v___f_3145_; lean_object* v___x_3146_; lean_object* v___f_3147_; lean_object* v___f_3148_; lean_object* v___f_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_toApplicative_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3185_; 
v___x_3136_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3137_ = lean_ctor_get(v___x_3136_, 0);
v_toFunctor_3138_ = lean_ctor_get(v_toApplicative_3137_, 0);
v_toSeq_3139_ = lean_ctor_get(v_toApplicative_3137_, 2);
v_toSeqLeft_3140_ = lean_ctor_get(v_toApplicative_3137_, 3);
v_toSeqRight_3141_ = lean_ctor_get(v_toApplicative_3137_, 4);
v___f_3142_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3143_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3138_, 2);
v___f_3144_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3144_, 0, v_toFunctor_3138_);
v___f_3145_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3145_, 0, v_toFunctor_3138_);
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___f_3144_);
lean_ctor_set(v___x_3146_, 1, v___f_3145_);
lean_inc(v_toSeqRight_3141_);
v___f_3147_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3147_, 0, v_toSeqRight_3141_);
lean_inc(v_toSeqLeft_3140_);
v___f_3148_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3148_, 0, v_toSeqLeft_3140_);
lean_inc(v_toSeq_3139_);
v___f_3149_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3149_, 0, v_toSeq_3139_);
v___x_3150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3146_);
lean_ctor_set(v___x_3150_, 1, v___f_3142_);
lean_ctor_set(v___x_3150_, 2, v___f_3149_);
lean_ctor_set(v___x_3150_, 3, v___f_3148_);
lean_ctor_set(v___x_3150_, 4, v___f_3147_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___f_3143_);
v___x_3152_ = l_StateRefT_x27_instMonad___redArg(v___x_3151_);
v_toApplicative_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3185_ == 0)
{
lean_object* v_unused_3186_; 
v_unused_3186_ = lean_ctor_get(v___x_3152_, 1);
lean_dec(v_unused_3186_);
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3185_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_toApplicative_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3185_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_toFunctor_3157_; lean_object* v_toSeq_3158_; lean_object* v_toSeqLeft_3159_; lean_object* v_toSeqRight_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3183_; 
v_toFunctor_3157_ = lean_ctor_get(v_toApplicative_3153_, 0);
v_toSeq_3158_ = lean_ctor_get(v_toApplicative_3153_, 2);
v_toSeqLeft_3159_ = lean_ctor_get(v_toApplicative_3153_, 3);
v_toSeqRight_3160_ = lean_ctor_get(v_toApplicative_3153_, 4);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_toApplicative_3153_);
if (v_isSharedCheck_3183_ == 0)
{
lean_object* v_unused_3184_; 
v_unused_3184_ = lean_ctor_get(v_toApplicative_3153_, 1);
lean_dec(v_unused_3184_);
v___x_3162_ = v_toApplicative_3153_;
v_isShared_3163_ = v_isSharedCheck_3183_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_toSeqRight_3160_);
lean_inc(v_toSeqLeft_3159_);
lean_inc(v_toSeq_3158_);
lean_inc(v_toFunctor_3157_);
lean_dec(v_toApplicative_3153_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3183_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___f_3164_; lean_object* v___f_3165_; lean_object* v___f_3166_; lean_object* v___f_3167_; lean_object* v___f_3168_; lean_object* v___x_3169_; lean_object* v___f_3170_; lean_object* v___f_3171_; lean_object* v___f_3172_; lean_object* v___x_3174_; 
v___f_3164_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3164_, 0, v_inst_3129_);
v___f_3165_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3166_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3157_);
v___f_3167_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3167_, 0, v_toFunctor_3157_);
v___f_3168_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3168_, 0, v_toFunctor_3157_);
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___f_3167_);
lean_ctor_set(v___x_3169_, 1, v___f_3168_);
v___f_3170_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3170_, 0, v_toSeqRight_3160_);
v___f_3171_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3171_, 0, v_toSeqLeft_3159_);
v___f_3172_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3172_, 0, v_toSeq_3158_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 4, v___f_3170_);
lean_ctor_set(v___x_3162_, 3, v___f_3171_);
lean_ctor_set(v___x_3162_, 2, v___f_3172_);
lean_ctor_set(v___x_3162_, 1, v___f_3165_);
lean_ctor_set(v___x_3162_, 0, v___x_3169_);
v___x_3174_ = v___x_3162_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___f_3165_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v___f_3172_);
lean_ctor_set(v_reuseFailAlloc_3182_, 3, v___f_3171_);
lean_ctor_set(v_reuseFailAlloc_3182_, 4, v___f_3170_);
v___x_3174_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
lean_object* v___x_3176_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 1, v___f_3166_);
lean_ctor_set(v___x_3155_, 0, v___x_3174_);
v___x_3176_ = v___x_3155_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v___f_3166_);
v___x_3176_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
size_t v_sz_3177_; size_t v___x_3178_; lean_object* v___x_129__overap_3179_; lean_object* v___x_3180_; 
v_sz_3177_ = lean_array_size(v_a_3130_);
v___x_3178_ = ((size_t)0ULL);
v___x_129__overap_3179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3176_, v___f_3164_, v_sz_3177_, v___x_3178_, v_a_3130_);
lean_inc(v_a_3134_);
lean_inc_ref(v_a_3133_);
lean_inc(v_a_3132_);
lean_inc_ref(v_a_3131_);
v___x_3180_ = lean_apply_5(v___x_129__overap_3179_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, lean_box(0));
return v___x_3180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___boxed(lean_object* v_inst_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_Compiler_LCNF_Probe_toString___redArg(v_inst_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString(lean_object* v_00_u03b1_3195_, lean_object* v_inst_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___x_3203_; lean_object* v_toApplicative_3204_; lean_object* v_toFunctor_3205_; lean_object* v_toSeq_3206_; lean_object* v_toSeqLeft_3207_; lean_object* v_toSeqRight_3208_; lean_object* v___f_3209_; lean_object* v___f_3210_; lean_object* v___f_3211_; lean_object* v___f_3212_; lean_object* v___x_3213_; lean_object* v___f_3214_; lean_object* v___f_3215_; lean_object* v___f_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v_toApplicative_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3252_; 
v___x_3203_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3204_ = lean_ctor_get(v___x_3203_, 0);
v_toFunctor_3205_ = lean_ctor_get(v_toApplicative_3204_, 0);
v_toSeq_3206_ = lean_ctor_get(v_toApplicative_3204_, 2);
v_toSeqLeft_3207_ = lean_ctor_get(v_toApplicative_3204_, 3);
v_toSeqRight_3208_ = lean_ctor_get(v_toApplicative_3204_, 4);
v___f_3209_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3210_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3205_, 2);
v___f_3211_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3211_, 0, v_toFunctor_3205_);
v___f_3212_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3212_, 0, v_toFunctor_3205_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___f_3211_);
lean_ctor_set(v___x_3213_, 1, v___f_3212_);
lean_inc(v_toSeqRight_3208_);
v___f_3214_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3214_, 0, v_toSeqRight_3208_);
lean_inc(v_toSeqLeft_3207_);
v___f_3215_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3215_, 0, v_toSeqLeft_3207_);
lean_inc(v_toSeq_3206_);
v___f_3216_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3216_, 0, v_toSeq_3206_);
v___x_3217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3213_);
lean_ctor_set(v___x_3217_, 1, v___f_3209_);
lean_ctor_set(v___x_3217_, 2, v___f_3216_);
lean_ctor_set(v___x_3217_, 3, v___f_3215_);
lean_ctor_set(v___x_3217_, 4, v___f_3214_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v___f_3210_);
v___x_3219_ = l_StateRefT_x27_instMonad___redArg(v___x_3218_);
v_toApplicative_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v___x_3219_, 1);
lean_dec(v_unused_3253_);
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3252_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_toApplicative_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3252_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v_toFunctor_3224_; lean_object* v_toSeq_3225_; lean_object* v_toSeqLeft_3226_; lean_object* v_toSeqRight_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3250_; 
v_toFunctor_3224_ = lean_ctor_get(v_toApplicative_3220_, 0);
v_toSeq_3225_ = lean_ctor_get(v_toApplicative_3220_, 2);
v_toSeqLeft_3226_ = lean_ctor_get(v_toApplicative_3220_, 3);
v_toSeqRight_3227_ = lean_ctor_get(v_toApplicative_3220_, 4);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_toApplicative_3220_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v_toApplicative_3220_, 1);
lean_dec(v_unused_3251_);
v___x_3229_ = v_toApplicative_3220_;
v_isShared_3230_ = v_isSharedCheck_3250_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_toSeqRight_3227_);
lean_inc(v_toSeqLeft_3226_);
lean_inc(v_toSeq_3225_);
lean_inc(v_toFunctor_3224_);
lean_dec(v_toApplicative_3220_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3250_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___f_3231_; lean_object* v___f_3232_; lean_object* v___f_3233_; lean_object* v___f_3234_; lean_object* v___f_3235_; lean_object* v___x_3236_; lean_object* v___f_3237_; lean_object* v___f_3238_; lean_object* v___f_3239_; lean_object* v___x_3241_; 
v___f_3231_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3231_, 0, v_inst_3196_);
v___f_3232_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3233_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3224_);
v___f_3234_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3234_, 0, v_toFunctor_3224_);
v___f_3235_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3235_, 0, v_toFunctor_3224_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___f_3234_);
lean_ctor_set(v___x_3236_, 1, v___f_3235_);
v___f_3237_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3237_, 0, v_toSeqRight_3227_);
v___f_3238_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3238_, 0, v_toSeqLeft_3226_);
v___f_3239_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3239_, 0, v_toSeq_3225_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___f_3237_);
lean_ctor_set(v___x_3229_, 3, v___f_3238_);
lean_ctor_set(v___x_3229_, 2, v___f_3239_);
lean_ctor_set(v___x_3229_, 1, v___f_3232_);
lean_ctor_set(v___x_3229_, 0, v___x_3236_);
v___x_3241_ = v___x_3229_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v___f_3232_);
lean_ctor_set(v_reuseFailAlloc_3249_, 2, v___f_3239_);
lean_ctor_set(v_reuseFailAlloc_3249_, 3, v___f_3238_);
lean_ctor_set(v_reuseFailAlloc_3249_, 4, v___f_3237_);
v___x_3241_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3243_; 
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 1, v___f_3233_);
lean_ctor_set(v___x_3222_, 0, v___x_3241_);
v___x_3243_ = v___x_3222_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v___f_3233_);
v___x_3243_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
size_t v_sz_3244_; size_t v___x_3245_; lean_object* v___x_190__overap_3246_; lean_object* v___x_3247_; 
v_sz_3244_ = lean_array_size(v_a_3197_);
v___x_3245_ = ((size_t)0ULL);
v___x_190__overap_3246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3243_, v___f_3231_, v_sz_3244_, v___x_3245_, v_a_3197_);
lean_inc(v_a_3201_);
lean_inc_ref(v_a_3200_);
lean_inc(v_a_3199_);
lean_inc_ref(v_a_3198_);
v___x_3247_ = lean_apply_5(v___x_190__overap_3246_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, lean_box(0));
return v___x_3247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___boxed(lean_object* v_00_u03b1_3254_, lean_object* v_inst_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_Compiler_LCNF_Probe_toString(v_00_u03b1_3254_, v_inst_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg(lean_object* v_data_3263_){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3265_ = lean_array_get_size(v_data_3263_);
v___x_3266_ = lean_unsigned_to_nat(1u);
v___x_3267_ = lean_mk_empty_array_with_capacity(v___x_3266_);
v___x_3268_ = lean_array_push(v___x_3267_, v___x_3265_);
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg___boxed(lean_object* v_data_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_Compiler_LCNF_Probe_count___redArg(v_data_3270_);
lean_dec_ref(v_data_3270_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count(lean_object* v_00_u03b1_3273_, lean_object* v_data_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3280_ = lean_array_get_size(v_data_3274_);
v___x_3281_ = lean_unsigned_to_nat(1u);
v___x_3282_ = lean_mk_empty_array_with_capacity(v___x_3281_);
v___x_3283_ = lean_array_push(v___x_3282_, v___x_3280_);
v___x_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___boxed(lean_object* v_00_u03b1_3285_, lean_object* v_data_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_Lean_Compiler_LCNF_Probe_count(v_00_u03b1_3285_, v_data_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec_ref(v_data_3286_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg(lean_object* v_data_3294_){
_start:
{
lean_object* v___y_3297_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3302_ = lean_unsigned_to_nat(0u);
v___x_3303_ = lean_array_get_size(v_data_3294_);
v___x_3304_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3305_ = lean_nat_dec_lt(v___x_3302_, v___x_3303_);
if (v___x_3305_ == 0)
{
lean_dec_ref(v_data_3294_);
v___y_3297_ = v___x_3302_;
goto v___jp_3296_;
}
else
{
lean_object* v___f_3306_; uint8_t v___x_3307_; 
v___f_3306_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3307_ = lean_nat_dec_le(v___x_3303_, v___x_3303_);
if (v___x_3307_ == 0)
{
if (v___x_3305_ == 0)
{
lean_dec_ref(v_data_3294_);
v___y_3297_ = v___x_3302_;
goto v___jp_3296_;
}
else
{
size_t v___x_3308_; size_t v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = ((size_t)0ULL);
v___x_3309_ = lean_usize_of_nat(v___x_3303_);
v___x_3310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3304_, v___f_3306_, v_data_3294_, v___x_3308_, v___x_3309_, v___x_3302_);
v___y_3297_ = v___x_3310_;
goto v___jp_3296_;
}
}
else
{
size_t v___x_3311_; size_t v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = ((size_t)0ULL);
v___x_3312_ = lean_usize_of_nat(v___x_3303_);
v___x_3313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3304_, v___f_3306_, v_data_3294_, v___x_3311_, v___x_3312_, v___x_3302_);
v___y_3297_ = v___x_3313_;
goto v___jp_3296_;
}
}
v___jp_3296_:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3298_ = lean_unsigned_to_nat(1u);
v___x_3299_ = lean_mk_empty_array_with_capacity(v___x_3298_);
v___x_3300_ = lean_array_push(v___x_3299_, v___y_3297_);
v___x_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg___boxed(lean_object* v_data_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Compiler_LCNF_Probe_sum___redArg(v_data_3314_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum(lean_object* v_data_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v___y_3324_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; 
v___x_3329_ = lean_unsigned_to_nat(0u);
v___x_3330_ = lean_array_get_size(v_data_3317_);
v___x_3331_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3332_ = lean_nat_dec_lt(v___x_3329_, v___x_3330_);
if (v___x_3332_ == 0)
{
lean_dec_ref(v_data_3317_);
v___y_3324_ = v___x_3329_;
goto v___jp_3323_;
}
else
{
lean_object* v___f_3333_; uint8_t v___x_3334_; 
v___f_3333_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3334_ = lean_nat_dec_le(v___x_3330_, v___x_3330_);
if (v___x_3334_ == 0)
{
if (v___x_3332_ == 0)
{
lean_dec_ref(v_data_3317_);
v___y_3324_ = v___x_3329_;
goto v___jp_3323_;
}
else
{
size_t v___x_3335_; size_t v___x_3336_; lean_object* v___x_3337_; 
v___x_3335_ = ((size_t)0ULL);
v___x_3336_ = lean_usize_of_nat(v___x_3330_);
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3331_, v___f_3333_, v_data_3317_, v___x_3335_, v___x_3336_, v___x_3329_);
v___y_3324_ = v___x_3337_;
goto v___jp_3323_;
}
}
else
{
size_t v___x_3338_; size_t v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = ((size_t)0ULL);
v___x_3339_ = lean_usize_of_nat(v___x_3330_);
v___x_3340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3331_, v___f_3333_, v_data_3317_, v___x_3338_, v___x_3339_, v___x_3329_);
v___y_3324_ = v___x_3340_;
goto v___jp_3323_;
}
}
v___jp_3323_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3325_ = lean_unsigned_to_nat(1u);
v___x_3326_ = lean_mk_empty_array_with_capacity(v___x_3325_);
v___x_3327_ = lean_array_push(v___x_3326_, v___y_3324_);
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3327_);
return v___x_3328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___boxed(lean_object* v_data_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_){
_start:
{
lean_object* v_res_3347_; 
v_res_3347_ = l_Lean_Compiler_LCNF_Probe_sum(v_data_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
return v_res_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg(lean_object* v_n_3348_, lean_object* v_data_3349_){
_start:
{
lean_object* v_lower_3352_; lean_object* v_upper_3353_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3357_ = lean_array_get_size(v_data_3349_);
v___x_3358_ = lean_nat_sub(v___x_3357_, v_n_3348_);
v___x_3359_ = lean_unsigned_to_nat(0u);
v___x_3360_ = lean_nat_dec_le(v___x_3358_, v___x_3359_);
if (v___x_3360_ == 0)
{
v_lower_3352_ = v___x_3358_;
v_upper_3353_ = v___x_3357_;
goto v___jp_3351_;
}
else
{
lean_dec(v___x_3358_);
v_lower_3352_ = v___x_3359_;
v_upper_3353_ = v___x_3357_;
goto v___jp_3351_;
}
v___jp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3354_ = l_Array_toSubarray___redArg(v_data_3349_, v_lower_3352_, v_upper_3353_);
v___x_3355_ = l_Subarray_copy___redArg(v___x_3354_);
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
return v___x_3356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg___boxed(lean_object* v_n_3361_, lean_object* v_data_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Compiler_LCNF_Probe_tail___redArg(v_n_3361_, v_data_3362_);
lean_dec(v_n_3361_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail(lean_object* v_00_u03b1_3365_, lean_object* v_n_3366_, lean_object* v_data_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_lower_3374_; lean_object* v_upper_3375_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3379_ = lean_array_get_size(v_data_3367_);
v___x_3380_ = lean_nat_sub(v___x_3379_, v_n_3366_);
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = lean_nat_dec_le(v___x_3380_, v___x_3381_);
if (v___x_3382_ == 0)
{
v_lower_3374_ = v___x_3380_;
v_upper_3375_ = v___x_3379_;
goto v___jp_3373_;
}
else
{
lean_dec(v___x_3380_);
v_lower_3374_ = v___x_3381_;
v_upper_3375_ = v___x_3379_;
goto v___jp_3373_;
}
v___jp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3376_ = l_Array_toSubarray___redArg(v_data_3367_, v_lower_3374_, v_upper_3375_);
v___x_3377_ = l_Subarray_copy___redArg(v___x_3376_);
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___boxed(lean_object* v_00_u03b1_3383_, lean_object* v_n_3384_, lean_object* v_data_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_Compiler_LCNF_Probe_tail(v_00_u03b1_3383_, v_n_3384_, v_data_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec(v_n_3384_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg(lean_object* v_n_3392_, lean_object* v_data_3393_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = l_Array_toSubarray___redArg(v_data_3393_, v___x_3395_, v_n_3392_);
v___x_3397_ = l_Subarray_copy___redArg(v___x_3396_);
v___x_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg___boxed(lean_object* v_n_3399_, lean_object* v_data_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_Compiler_LCNF_Probe_head___redArg(v_n_3399_, v_data_3400_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head(lean_object* v_00_u03b1_3403_, lean_object* v_n_3404_, lean_object* v_data_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3411_ = lean_unsigned_to_nat(0u);
v___x_3412_ = l_Array_toSubarray___redArg(v_data_3405_, v___x_3411_, v_n_3404_);
v___x_3413_ = l_Subarray_copy___redArg(v___x_3412_);
v___x_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___boxed(lean_object* v_00_u03b1_3415_, lean_object* v_n_3416_, lean_object* v_data_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_Compiler_LCNF_Probe_head(v_00_u03b1_3415_, v_n_3416_, v_data_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
lean_dec(v_a_3421_);
lean_dec_ref(v_a_3420_);
lean_dec(v_a_3419_);
lean_dec_ref(v_a_3418_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(lean_object* v_probe_3429_, lean_object* v___x_3430_, lean_object* v_inst_3431_, lean_object* v___x_3432_, lean_object* v___x_3433_, lean_object* v_toMonadRef_3434_, lean_object* v___f_3435_, lean_object* v_decls_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
lean_inc(v___y_3440_);
lean_inc_ref(v___y_3439_);
lean_inc(v___y_3438_);
lean_inc_ref(v___y_3437_);
lean_inc_ref(v_decls_3436_);
v___x_3442_ = lean_apply_6(v_probe_3429_, v_decls_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, lean_box(0));
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_options_3443_; uint8_t v_hasTrace_3444_; 
v_options_3443_ = lean_ctor_get(v___y_3439_, 1);
v_hasTrace_3444_ = lean_ctor_get_uint8(v_options_3443_, sizeof(void*)*1);
if (v_hasTrace_3444_ == 0)
{
lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec_ref(v___f_3435_);
lean_dec_ref(v_toMonadRef_3434_);
lean_dec_ref(v___x_3433_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v_inst_3431_);
lean_dec_ref(v___x_3430_);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3451_ == 0)
{
lean_object* v_unused_3452_; 
v_unused_3452_ = lean_ctor_get(v___x_3442_, 0);
lean_dec(v_unused_3452_);
v___x_3446_ = v___x_3442_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_dec(v___x_3442_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v_decls_3436_);
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_decls_3436_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
else
{
lean_object* v_toCold_3453_; lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3491_; 
v_toCold_3453_ = lean_ctor_get(v___y_3439_, 0);
v_a_3454_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3456_ = v___x_3442_;
v_isShared_3457_ = v_isSharedCheck_3491_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3442_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3491_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v_inheritedTraceOptions_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; uint8_t v___x_3463_; 
v_inheritedTraceOptions_3458_ = lean_ctor_get(v_toCold_3453_, 4);
v___x_3459_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0));
v___x_3460_ = l_Lean_Name_mkStr2(v___x_3459_, v___x_3430_);
v___x_3461_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2));
lean_inc(v___x_3460_);
v___x_3462_ = l_Lean_Name_append(v___x_3461_, v___x_3460_);
v___x_3463_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3458_, v_options_3443_, v___x_3462_);
lean_dec(v___x_3462_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3465_; 
lean_dec(v___x_3460_);
lean_dec(v_a_3454_);
lean_dec_ref(v___f_3435_);
lean_dec_ref(v_toMonadRef_3434_);
lean_dec_ref(v___x_3433_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v_inst_3431_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v_decls_3436_);
v___x_3465_ = v___x_3456_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_decls_3436_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
else
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_945__overap_3473_; lean_object* v___x_3474_; 
lean_del_object(v___x_3456_);
v___x_3467_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3));
v___x_3468_ = lean_array_to_list(v_a_3454_);
v___x_3469_ = l_List_toString___redArg(v_inst_3431_, v___x_3468_);
v___x_3470_ = lean_string_append(v___x_3467_, v___x_3469_);
lean_dec_ref(v___x_3469_);
v___x_3471_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
v___x_3472_ = l_Lean_MessageData_ofFormat(v___x_3471_);
v___x_945__overap_3473_ = l_Lean_addTrace___redArg(v___x_3432_, v___x_3433_, v_toMonadRef_3434_, v___f_3435_, v___x_3460_, v___x_3472_);
lean_inc(v___y_3440_);
lean_inc_ref(v___y_3439_);
lean_inc(v___y_3438_);
lean_inc_ref(v___y_3437_);
v___x_3474_ = lean_apply_5(v___x_945__overap_3473_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, lean_box(0));
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; 
v_unused_3482_ = lean_ctor_get(v___x_3474_, 0);
lean_dec(v_unused_3482_);
v___x_3476_ = v___x_3474_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_dec(v___x_3474_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v_decls_3436_);
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_decls_3436_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v_decls_3436_);
v_a_3483_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3474_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3474_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec_ref(v_decls_3436_);
lean_dec_ref(v___f_3435_);
lean_dec_ref(v_toMonadRef_3434_);
lean_dec_ref(v___x_3433_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v_inst_3431_);
lean_dec_ref(v___x_3430_);
v_a_3492_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3442_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3442_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed(lean_object* v_probe_3500_, lean_object* v___x_3501_, lean_object* v_inst_3502_, lean_object* v___x_3503_, lean_object* v___x_3504_, lean_object* v_toMonadRef_3505_, lean_object* v___f_3506_, lean_object* v_decls_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(v_probe_3500_, v___x_3501_, v_inst_3502_, v___x_3503_, v___x_3504_, v_toMonadRef_3505_, v___f_3506_, v_decls_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3513_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2(void){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = l_Lean_Core_instMonadTraceCoreM;
v___x_3517_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3518_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3517_, v___x_3516_);
return v___x_3518_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___f_3520_; lean_object* v___x_3521_; 
v___x_3519_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2);
v___f_3520_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___x_3521_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3520_, v___x_3519_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3524_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_3525_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3526_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5));
v___x_3527_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3526_, v___x_3525_, v___x_3524_);
return v___x_3527_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___f_3529_; lean_object* v___f_3530_; lean_object* v___x_3531_; 
v___x_3528_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6);
v___f_3529_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___f_3530_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4));
v___x_3531_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3530_, v___f_3529_, v___x_3528_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg(lean_object* v_inst_3536_, uint8_t v_phase_3537_, lean_object* v_probe_3538_){
_start:
{
lean_object* v___x_3539_; lean_object* v_toApplicative_3540_; lean_object* v_toFunctor_3541_; lean_object* v_toSeq_3542_; lean_object* v_toSeqLeft_3543_; lean_object* v_toSeqRight_3544_; lean_object* v___f_3545_; lean_object* v___f_3546_; lean_object* v___f_3547_; lean_object* v___f_3548_; lean_object* v___x_3549_; lean_object* v___f_3550_; lean_object* v___f_3551_; lean_object* v___f_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v_toApplicative_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3593_; 
v___x_3539_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3540_ = lean_ctor_get(v___x_3539_, 0);
v_toFunctor_3541_ = lean_ctor_get(v_toApplicative_3540_, 0);
v_toSeq_3542_ = lean_ctor_get(v_toApplicative_3540_, 2);
v_toSeqLeft_3543_ = lean_ctor_get(v_toApplicative_3540_, 3);
v_toSeqRight_3544_ = lean_ctor_get(v_toApplicative_3540_, 4);
v___f_3545_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3546_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3541_, 2);
v___f_3547_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3547_, 0, v_toFunctor_3541_);
v___f_3548_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3548_, 0, v_toFunctor_3541_);
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___f_3547_);
lean_ctor_set(v___x_3549_, 1, v___f_3548_);
lean_inc(v_toSeqRight_3544_);
v___f_3550_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3550_, 0, v_toSeqRight_3544_);
lean_inc(v_toSeqLeft_3543_);
v___f_3551_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3551_, 0, v_toSeqLeft_3543_);
lean_inc(v_toSeq_3542_);
v___f_3552_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3552_, 0, v_toSeq_3542_);
v___x_3553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3549_);
lean_ctor_set(v___x_3553_, 1, v___f_3545_);
lean_ctor_set(v___x_3553_, 2, v___f_3552_);
lean_ctor_set(v___x_3553_, 3, v___f_3551_);
lean_ctor_set(v___x_3553_, 4, v___f_3550_);
v___x_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
lean_ctor_set(v___x_3554_, 1, v___f_3546_);
v___x_3555_ = l_StateRefT_x27_instMonad___redArg(v___x_3554_);
v_toApplicative_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; 
v_unused_3594_ = lean_ctor_get(v___x_3555_, 1);
lean_dec(v_unused_3594_);
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3593_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_toApplicative_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3593_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v_toFunctor_3560_; lean_object* v_toSeq_3561_; lean_object* v_toSeqLeft_3562_; lean_object* v_toSeqRight_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3591_; 
v_toFunctor_3560_ = lean_ctor_get(v_toApplicative_3556_, 0);
v_toSeq_3561_ = lean_ctor_get(v_toApplicative_3556_, 2);
v_toSeqLeft_3562_ = lean_ctor_get(v_toApplicative_3556_, 3);
v_toSeqRight_3563_ = lean_ctor_get(v_toApplicative_3556_, 4);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_toApplicative_3556_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; 
v_unused_3592_ = lean_ctor_get(v_toApplicative_3556_, 1);
lean_dec(v_unused_3592_);
v___x_3565_ = v_toApplicative_3556_;
v_isShared_3566_ = v_isSharedCheck_3591_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_toSeqRight_3563_);
lean_inc(v_toSeqLeft_3562_);
lean_inc(v_toSeq_3561_);
lean_inc(v_toFunctor_3560_);
lean_dec(v_toApplicative_3556_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3591_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___f_3567_; lean_object* v___f_3568_; lean_object* v___f_3569_; lean_object* v___f_3570_; lean_object* v___x_3571_; lean_object* v___f_3572_; lean_object* v___f_3573_; lean_object* v___f_3574_; lean_object* v___x_3576_; 
v___f_3567_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3568_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3560_);
v___f_3569_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3569_, 0, v_toFunctor_3560_);
v___f_3570_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3570_, 0, v_toFunctor_3560_);
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___f_3569_);
lean_ctor_set(v___x_3571_, 1, v___f_3570_);
v___f_3572_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3572_, 0, v_toSeqRight_3563_);
v___f_3573_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3573_, 0, v_toSeqLeft_3562_);
v___f_3574_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3574_, 0, v_toSeq_3561_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 4, v___f_3572_);
lean_ctor_set(v___x_3565_, 3, v___f_3573_);
lean_ctor_set(v___x_3565_, 2, v___f_3574_);
lean_ctor_set(v___x_3565_, 1, v___f_3567_);
lean_ctor_set(v___x_3565_, 0, v___x_3571_);
v___x_3576_ = v___x_3565_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3571_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v___f_3567_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v___f_3574_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v___f_3573_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v___f_3572_);
v___x_3576_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3578_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 1, v___f_3568_);
lean_ctor_set(v___x_3558_, 0, v___x_3576_);
v___x_3578_ = v___x_3558_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v___f_3568_);
v___x_3578_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v_toMonadRef_3581_; lean_object* v___f_3582_; lean_object* v___x_3583_; uint8_t v___x_3584_; lean_object* v___x_3585_; lean_object* v___f_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3579_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3);
v___x_3580_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7);
v_toMonadRef_3581_ = lean_ctor_get(v___x_3580_, 0);
v___f_3582_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8));
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = 0;
v___x_3585_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__9));
lean_inc_ref(v_toMonadRef_3581_);
v___f_3586_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_3586_, 0, v_probe_3538_);
lean_closure_set(v___f_3586_, 1, v___x_3585_);
lean_closure_set(v___f_3586_, 2, v_inst_3536_);
lean_closure_set(v___f_3586_, 3, v___x_3578_);
lean_closure_set(v___f_3586_, 4, v___x_3579_);
lean_closure_set(v___f_3586_, 5, v_toMonadRef_3581_);
lean_closure_set(v___f_3586_, 6, v___f_3582_);
v___x_3587_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__10));
v___x_3588_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3588_, 0, v___x_3583_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
lean_ctor_set(v___x_3588_, 2, v___f_3586_);
lean_ctor_set_uint8(v___x_3588_, sizeof(void*)*3, v_phase_3537_);
lean_ctor_set_uint8(v___x_3588_, sizeof(void*)*3 + 1, v_phase_3537_);
lean_ctor_set_uint8(v___x_3588_, sizeof(void*)*3 + 2, v___x_3584_);
return v___x_3588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(lean_object* v_inst_3595_, lean_object* v_phase_3596_, lean_object* v_probe_3597_){
_start:
{
uint8_t v_phase_boxed_3598_; lean_object* v_res_3599_; 
v_phase_boxed_3598_ = lean_unbox(v_phase_3596_);
v_res_3599_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3595_, v_phase_boxed_3598_, v_probe_3597_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass(lean_object* v_00_u03b2_3600_, lean_object* v_inst_3601_, uint8_t v_phase_3602_, lean_object* v_probe_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3601_, v_phase_3602_, v_probe_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___boxed(lean_object* v_00_u03b2_3605_, lean_object* v_inst_3606_, lean_object* v_phase_3607_, lean_object* v_probe_3608_){
_start:
{
uint8_t v_phase_boxed_3609_; lean_object* v_res_3610_; 
v_phase_boxed_3609_ = lean_unbox(v_phase_3607_);
v_res_3610_ = l_Lean_Compiler_LCNF_Probe_toPass(v_00_u03b2_3605_, v_inst_3606_, v_phase_boxed_3609_, v_probe_3608_);
return v_res_3610_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = lean_unsigned_to_nat(4008565020u);
v___x_3670_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3671_ = l_Lean_Name_num___override(v___x_3670_, v___x_3669_);
return v___x_3671_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3673_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3674_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3675_ = l_Lean_Name_str___override(v___x_3674_, v___x_3673_);
return v___x_3675_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3678_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3679_ = l_Lean_Name_str___override(v___x_3678_, v___x_3677_);
return v___x_3679_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3680_ = lean_unsigned_to_nat(2u);
v___x_3681_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3682_ = l_Lean_Name_num___override(v___x_3681_, v___x_3680_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3684_; uint8_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3684_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3685_ = 1;
v___x_3686_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3687_ = l_Lean_registerTraceClass(v___x_3684_, v___x_3685_, v___x_3686_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2____boxed(lean_object* v_a_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
return v_res_3689_;
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
