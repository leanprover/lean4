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
lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_instMonadFunctor___aux__1___boxed, .m_arity = 7, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instAddMessageContextCompilerM___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5_value)} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6_value;
static const lean_string_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "probe"};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(210, 226, 36, 16, 11, 213, 189, 181)}};
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(60, 150, 55, 23, 179, 120, 143, 48)}};
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
lean_object* v___x_15_; lean_object* v_toApplicative_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_77_; 
v___x_15_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; 
v_unused_78_ = lean_ctor_get(v___x_15_, 1);
lean_dec(v_unused_78_);
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_77_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_toApplicative_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_77_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v_toFunctor_20_; lean_object* v_toSeq_21_; lean_object* v_toSeqLeft_22_; lean_object* v_toSeqRight_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_75_; 
v_toFunctor_20_ = lean_ctor_get(v_toApplicative_16_, 0);
v_toSeq_21_ = lean_ctor_get(v_toApplicative_16_, 2);
v_toSeqLeft_22_ = lean_ctor_get(v_toApplicative_16_, 3);
v_toSeqRight_23_ = lean_ctor_get(v_toApplicative_16_, 4);
v_isSharedCheck_75_ = !lean_is_exclusive(v_toApplicative_16_);
if (v_isSharedCheck_75_ == 0)
{
lean_object* v_unused_76_; 
v_unused_76_ = lean_ctor_get(v_toApplicative_16_, 1);
lean_dec(v_unused_76_);
v___x_25_ = v_toApplicative_16_;
v_isShared_26_ = v_isSharedCheck_75_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_toSeqRight_23_);
lean_inc(v_toSeqLeft_22_);
lean_inc(v_toSeq_21_);
lean_inc(v_toFunctor_20_);
lean_dec(v_toApplicative_16_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_75_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___x_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___x_36_; 
v___f_27_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_28_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref(v_toFunctor_20_);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_29_, 0, v_toFunctor_20_);
v___f_30_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_30_, 0, v_toFunctor_20_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___f_29_);
lean_ctor_set(v___x_31_, 1, v___f_30_);
v___f_32_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_32_, 0, v_toSeqRight_23_);
v___f_33_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_33_, 0, v_toSeqLeft_22_);
v___f_34_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_34_, 0, v_toSeq_21_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 4, v___f_32_);
lean_ctor_set(v___x_25_, 3, v___f_33_);
lean_ctor_set(v___x_25_, 2, v___f_34_);
lean_ctor_set(v___x_25_, 1, v___f_27_);
lean_ctor_set(v___x_25_, 0, v___x_31_);
v___x_36_ = v___x_25_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___f_27_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v___f_34_);
lean_ctor_set(v_reuseFailAlloc_74_, 3, v___f_33_);
lean_ctor_set(v_reuseFailAlloc_74_, 4, v___f_32_);
v___x_36_ = v_reuseFailAlloc_74_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_38_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 1, v___f_28_);
lean_ctor_set(v___x_18_, 0, v___x_36_);
v___x_38_ = v___x_18_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v___f_28_);
v___x_38_ = v_reuseFailAlloc_73_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; lean_object* v_toApplicative_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_71_; 
v___x_39_ = l_StateRefT_x27_instMonad___redArg(v___x_38_);
v_toApplicative_40_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_71_ == 0)
{
lean_object* v_unused_72_; 
v_unused_72_ = lean_ctor_get(v___x_39_, 1);
lean_dec(v_unused_72_);
v___x_42_ = v___x_39_;
v_isShared_43_ = v_isSharedCheck_71_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_toApplicative_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_71_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_toFunctor_44_; lean_object* v_toSeq_45_; lean_object* v_toSeqLeft_46_; lean_object* v_toSeqRight_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_69_; 
v_toFunctor_44_ = lean_ctor_get(v_toApplicative_40_, 0);
v_toSeq_45_ = lean_ctor_get(v_toApplicative_40_, 2);
v_toSeqLeft_46_ = lean_ctor_get(v_toApplicative_40_, 3);
v_toSeqRight_47_ = lean_ctor_get(v_toApplicative_40_, 4);
v_isSharedCheck_69_ = !lean_is_exclusive(v_toApplicative_40_);
if (v_isSharedCheck_69_ == 0)
{
lean_object* v_unused_70_; 
v_unused_70_ = lean_ctor_get(v_toApplicative_40_, 1);
lean_dec(v_unused_70_);
v___x_49_ = v_toApplicative_40_;
v_isShared_50_ = v_isSharedCheck_69_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_toSeqRight_47_);
lean_inc(v_toSeqLeft_46_);
lean_inc(v_toSeq_45_);
lean_inc(v_toFunctor_44_);
lean_dec(v_toApplicative_40_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_69_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___f_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_60_; 
v___f_51_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_52_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_44_);
v___f_53_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_53_, 0, v_toFunctor_44_);
v___f_54_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_54_, 0, v_toFunctor_44_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___f_53_);
lean_ctor_set(v___x_55_, 1, v___f_54_);
v___f_56_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_56_, 0, v_toSeqRight_47_);
v___f_57_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_57_, 0, v_toSeqLeft_46_);
v___f_58_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_58_, 0, v_toSeq_45_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 4, v___f_56_);
lean_ctor_set(v___x_49_, 3, v___f_57_);
lean_ctor_set(v___x_49_, 2, v___f_58_);
lean_ctor_set(v___x_49_, 1, v___f_51_);
lean_ctor_set(v___x_49_, 0, v___x_55_);
v___x_60_ = v___x_49_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v___f_51_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v___f_58_);
lean_ctor_set(v_reuseFailAlloc_68_, 3, v___f_57_);
lean_ctor_set(v_reuseFailAlloc_68_, 4, v___f_56_);
v___x_60_ = v_reuseFailAlloc_68_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_62_; 
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___f_52_);
lean_ctor_set(v___x_42_, 0, v___x_60_);
v___x_62_ = v___x_42_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___f_52_);
v___x_62_ = v_reuseFailAlloc_67_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
size_t v_sz_63_; size_t v___x_64_; lean_object* v___x_7__overap_65_; lean_object* v___x_66_; 
v_sz_63_ = lean_array_size(v_data_9_);
v___x_64_ = ((size_t)0ULL);
v___x_7__overap_65_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_62_, v_f_8_, v_sz_63_, v___x_64_, v_data_9_);
lean_inc(v_a_13_);
lean_inc_ref(v_a_12_);
lean_inc(v_a_11_);
lean_inc_ref(v_a_10_);
v___x_66_ = lean_apply_5(v___x_7__overap_65_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, lean_box(0));
return v___x_66_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg___boxed(lean_object* v_f_79_, lean_object* v_data_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Compiler_LCNF_Probe_map___redArg(v_f_79_, v_data_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_f_89_, lean_object* v_data_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; lean_object* v_toApplicative_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_158_; 
v___x_96_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v___x_96_, 1);
lean_dec(v_unused_159_);
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_158_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_toApplicative_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_158_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_toFunctor_101_; lean_object* v_toSeq_102_; lean_object* v_toSeqLeft_103_; lean_object* v_toSeqRight_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_156_; 
v_toFunctor_101_ = lean_ctor_get(v_toApplicative_97_, 0);
v_toSeq_102_ = lean_ctor_get(v_toApplicative_97_, 2);
v_toSeqLeft_103_ = lean_ctor_get(v_toApplicative_97_, 3);
v_toSeqRight_104_ = lean_ctor_get(v_toApplicative_97_, 4);
v_isSharedCheck_156_ = !lean_is_exclusive(v_toApplicative_97_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v_toApplicative_97_, 1);
lean_dec(v_unused_157_);
v___x_106_ = v_toApplicative_97_;
v_isShared_107_ = v_isSharedCheck_156_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_toSeqRight_104_);
lean_inc(v_toSeqLeft_103_);
lean_inc(v_toSeq_102_);
lean_inc(v_toFunctor_101_);
lean_dec(v_toApplicative_97_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_156_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___f_108_; lean_object* v___f_109_; lean_object* v___f_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___x_117_; 
v___f_108_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_109_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref(v_toFunctor_101_);
v___f_110_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_110_, 0, v_toFunctor_101_);
v___f_111_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_111_, 0, v_toFunctor_101_);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___f_110_);
lean_ctor_set(v___x_112_, 1, v___f_111_);
v___f_113_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_113_, 0, v_toSeqRight_104_);
v___f_114_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_114_, 0, v_toSeqLeft_103_);
v___f_115_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_115_, 0, v_toSeq_102_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 4, v___f_113_);
lean_ctor_set(v___x_106_, 3, v___f_114_);
lean_ctor_set(v___x_106_, 2, v___f_115_);
lean_ctor_set(v___x_106_, 1, v___f_108_);
lean_ctor_set(v___x_106_, 0, v___x_112_);
v___x_117_ = v___x_106_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___f_108_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v___f_115_);
lean_ctor_set(v_reuseFailAlloc_155_, 3, v___f_114_);
lean_ctor_set(v_reuseFailAlloc_155_, 4, v___f_113_);
v___x_117_ = v_reuseFailAlloc_155_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_119_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v___f_109_);
lean_ctor_set(v___x_99_, 0, v___x_117_);
v___x_119_ = v___x_99_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___f_109_);
v___x_119_ = v_reuseFailAlloc_154_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; lean_object* v_toApplicative_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_152_; 
v___x_120_ = l_StateRefT_x27_instMonad___redArg(v___x_119_);
v_toApplicative_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_152_ == 0)
{
lean_object* v_unused_153_; 
v_unused_153_ = lean_ctor_get(v___x_120_, 1);
lean_dec(v_unused_153_);
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_152_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_toApplicative_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_152_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v_toFunctor_125_; lean_object* v_toSeq_126_; lean_object* v_toSeqLeft_127_; lean_object* v_toSeqRight_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_150_; 
v_toFunctor_125_ = lean_ctor_get(v_toApplicative_121_, 0);
v_toSeq_126_ = lean_ctor_get(v_toApplicative_121_, 2);
v_toSeqLeft_127_ = lean_ctor_get(v_toApplicative_121_, 3);
v_toSeqRight_128_ = lean_ctor_get(v_toApplicative_121_, 4);
v_isSharedCheck_150_ = !lean_is_exclusive(v_toApplicative_121_);
if (v_isSharedCheck_150_ == 0)
{
lean_object* v_unused_151_; 
v_unused_151_ = lean_ctor_get(v_toApplicative_121_, 1);
lean_dec(v_unused_151_);
v___x_130_ = v_toApplicative_121_;
v_isShared_131_ = v_isSharedCheck_150_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_toSeqRight_128_);
lean_inc(v_toSeqLeft_127_);
lean_inc(v_toSeq_126_);
lean_inc(v_toFunctor_125_);
lean_dec(v_toApplicative_121_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_150_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___x_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___x_141_; 
v___f_132_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_133_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_125_);
v___f_134_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_134_, 0, v_toFunctor_125_);
v___f_135_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_135_, 0, v_toFunctor_125_);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v___f_134_);
lean_ctor_set(v___x_136_, 1, v___f_135_);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_137_, 0, v_toSeqRight_128_);
v___f_138_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_138_, 0, v_toSeqLeft_127_);
v___f_139_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_139_, 0, v_toSeq_126_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 4, v___f_137_);
lean_ctor_set(v___x_130_, 3, v___f_138_);
lean_ctor_set(v___x_130_, 2, v___f_139_);
lean_ctor_set(v___x_130_, 1, v___f_132_);
lean_ctor_set(v___x_130_, 0, v___x_136_);
v___x_141_ = v___x_130_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___f_132_);
lean_ctor_set(v_reuseFailAlloc_149_, 2, v___f_139_);
lean_ctor_set(v_reuseFailAlloc_149_, 3, v___f_138_);
lean_ctor_set(v_reuseFailAlloc_149_, 4, v___f_137_);
v___x_141_ = v_reuseFailAlloc_149_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_143_; 
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___f_133_);
lean_ctor_set(v___x_123_, 0, v___x_141_);
v___x_143_ = v___x_123_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___f_133_);
v___x_143_ = v_reuseFailAlloc_148_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
size_t v_sz_144_; size_t v___x_145_; lean_object* v___x_57__overap_146_; lean_object* v___x_147_; 
v_sz_144_ = lean_array_size(v_data_90_);
v___x_145_ = ((size_t)0ULL);
v___x_57__overap_146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_143_, v_f_89_, v_sz_144_, v___x_145_, v_data_90_);
lean_inc(v_a_94_);
lean_inc_ref(v_a_93_);
lean_inc(v_a_92_);
lean_inc_ref(v_a_91_);
v___x_147_ = lean_apply_5(v___x_57__overap_146_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, lean_box(0));
return v___x_147_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map___boxed(lean_object* v_00_u03b1_160_, lean_object* v_00_u03b2_161_, lean_object* v_f_162_, lean_object* v_data_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Compiler_LCNF_Probe_map(v_00_u03b1_160_, v_00_u03b2_161_, v_f_162_, v_data_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0(lean_object* v_f_170_, lean_object* v_acc_171_, lean_object* v_a_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; 
lean_inc(v___y_176_);
lean_inc_ref(v___y_175_);
lean_inc(v___y_174_);
lean_inc_ref(v___y_173_);
lean_inc(v_a_172_);
v___x_178_ = lean_apply_6(v_f_170_, v_a_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, lean_box(0));
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_191_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_191_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_191_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_191_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
uint8_t v___x_183_; 
v___x_183_ = lean_unbox(v_a_179_);
lean_dec(v_a_179_);
if (v___x_183_ == 0)
{
lean_object* v___x_185_; 
lean_dec(v_a_172_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v_acc_171_);
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_acc_171_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_array_push(v_acc_171_, v_a_172_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_187_);
v___x_189_ = v___x_181_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec(v_a_172_);
lean_dec_ref(v_acc_171_);
v_a_192_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_178_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_178_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed(lean_object* v_f_200_, lean_object* v_acc_201_, lean_object* v_a_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0(v_f_200_, v_acc_201_, v_a_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg(lean_object* v_f_211_, lean_object* v_data_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; lean_object* v_toApplicative_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_292_; 
v___x_218_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v___x_218_, 1);
lean_dec(v_unused_293_);
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_292_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_toApplicative_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_292_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v_toFunctor_223_; lean_object* v_toSeq_224_; lean_object* v_toSeqLeft_225_; lean_object* v_toSeqRight_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_290_; 
v_toFunctor_223_ = lean_ctor_get(v_toApplicative_219_, 0);
v_toSeq_224_ = lean_ctor_get(v_toApplicative_219_, 2);
v_toSeqLeft_225_ = lean_ctor_get(v_toApplicative_219_, 3);
v_toSeqRight_226_ = lean_ctor_get(v_toApplicative_219_, 4);
v_isSharedCheck_290_ = !lean_is_exclusive(v_toApplicative_219_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; 
v_unused_291_ = lean_ctor_get(v_toApplicative_219_, 1);
lean_dec(v_unused_291_);
v___x_228_ = v_toApplicative_219_;
v_isShared_229_ = v_isSharedCheck_290_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_toSeqRight_226_);
lean_inc(v_toSeqLeft_225_);
lean_inc(v_toSeq_224_);
lean_inc(v_toFunctor_223_);
lean_dec(v_toApplicative_219_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_290_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___x_239_; 
v___f_230_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_231_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref(v_toFunctor_223_);
v___f_232_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_232_, 0, v_toFunctor_223_);
v___f_233_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_233_, 0, v_toFunctor_223_);
v___x_234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_234_, 0, v___f_232_);
lean_ctor_set(v___x_234_, 1, v___f_233_);
v___f_235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_235_, 0, v_toSeqRight_226_);
v___f_236_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_236_, 0, v_toSeqLeft_225_);
v___f_237_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_237_, 0, v_toSeq_224_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 4, v___f_235_);
lean_ctor_set(v___x_228_, 3, v___f_236_);
lean_ctor_set(v___x_228_, 2, v___f_237_);
lean_ctor_set(v___x_228_, 1, v___f_230_);
lean_ctor_set(v___x_228_, 0, v___x_234_);
v___x_239_ = v___x_228_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___f_230_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v___f_237_);
lean_ctor_set(v_reuseFailAlloc_289_, 3, v___f_236_);
lean_ctor_set(v_reuseFailAlloc_289_, 4, v___f_235_);
v___x_239_ = v_reuseFailAlloc_289_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_241_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v___f_231_);
lean_ctor_set(v___x_221_, 0, v___x_239_);
v___x_241_ = v___x_221_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___f_231_);
v___x_241_ = v_reuseFailAlloc_288_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v_toApplicative_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_286_; 
v___x_242_ = l_StateRefT_x27_instMonad___redArg(v___x_241_);
v_toApplicative_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v___x_242_, 1);
lean_dec(v_unused_287_);
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_286_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_toApplicative_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_286_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_toFunctor_247_; lean_object* v_toSeq_248_; lean_object* v_toSeqLeft_249_; lean_object* v_toSeqRight_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_284_; 
v_toFunctor_247_ = lean_ctor_get(v_toApplicative_243_, 0);
v_toSeq_248_ = lean_ctor_get(v_toApplicative_243_, 2);
v_toSeqLeft_249_ = lean_ctor_get(v_toApplicative_243_, 3);
v_toSeqRight_250_ = lean_ctor_get(v_toApplicative_243_, 4);
v_isSharedCheck_284_ = !lean_is_exclusive(v_toApplicative_243_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v_toApplicative_243_, 1);
lean_dec(v_unused_285_);
v___x_252_ = v_toApplicative_243_;
v_isShared_253_ = v_isSharedCheck_284_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_toSeqRight_250_);
lean_inc(v_toSeqLeft_249_);
lean_inc(v_toSeq_248_);
lean_inc(v_toFunctor_247_);
lean_dec(v_toApplicative_243_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_284_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___f_254_; lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___f_259_; lean_object* v___f_260_; lean_object* v___f_261_; lean_object* v___x_263_; 
v___f_254_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_255_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_247_);
v___f_256_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_256_, 0, v_toFunctor_247_);
v___f_257_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_257_, 0, v_toFunctor_247_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___f_256_);
lean_ctor_set(v___x_258_, 1, v___f_257_);
v___f_259_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_259_, 0, v_toSeqRight_250_);
v___f_260_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_260_, 0, v_toSeqLeft_249_);
v___f_261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_261_, 0, v_toSeq_248_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 4, v___f_259_);
lean_ctor_set(v___x_252_, 3, v___f_260_);
lean_ctor_set(v___x_252_, 2, v___f_261_);
lean_ctor_set(v___x_252_, 1, v___f_254_);
lean_ctor_set(v___x_252_, 0, v___x_258_);
v___x_263_ = v___x_252_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___f_254_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v___f_261_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v___f_260_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v___f_259_);
v___x_263_ = v_reuseFailAlloc_283_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_265_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v___f_255_);
lean_ctor_set(v___x_245_, 0, v___x_263_);
v___x_265_ = v___x_245_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_263_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v___f_255_);
v___x_265_ = v_reuseFailAlloc_282_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_array_get_size(v_data_212_);
v___x_268_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0));
v___x_269_ = lean_nat_dec_lt(v___x_266_, v___x_267_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
lean_dec_ref(v___x_265_);
lean_dec_ref(v_data_212_);
lean_dec_ref(v_f_211_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
return v___x_270_;
}
else
{
lean_object* v___f_271_; uint8_t v___x_272_; 
v___f_271_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_271_, 0, v_f_211_);
v___x_272_ = lean_nat_dec_le(v___x_267_, v___x_267_);
if (v___x_272_ == 0)
{
if (v___x_269_ == 0)
{
lean_object* v___x_273_; 
lean_dec_ref(v___f_271_);
lean_dec_ref(v___x_265_);
lean_dec_ref(v_data_212_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_268_);
return v___x_273_;
}
else
{
size_t v___x_274_; size_t v___x_275_; lean_object* v___x_359__overap_276_; lean_object* v___x_277_; 
v___x_274_ = ((size_t)0ULL);
v___x_275_ = lean_usize_of_nat(v___x_267_);
v___x_359__overap_276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_265_, v___f_271_, v_data_212_, v___x_274_, v___x_275_, v___x_268_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
v___x_277_ = lean_apply_5(v___x_359__overap_276_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, lean_box(0));
return v___x_277_;
}
}
else
{
size_t v___x_278_; size_t v___x_279_; lean_object* v___x_364__overap_280_; lean_object* v___x_281_; 
v___x_278_ = ((size_t)0ULL);
v___x_279_ = lean_usize_of_nat(v___x_267_);
v___x_364__overap_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_265_, v___f_271_, v_data_212_, v___x_278_, v___x_279_, v___x_268_);
lean_inc(v_a_216_);
lean_inc_ref(v_a_215_);
lean_inc(v_a_214_);
lean_inc_ref(v_a_213_);
v___x_281_ = lean_apply_5(v___x_364__overap_280_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, lean_box(0));
return v___x_281_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___boxed(lean_object* v_f_294_, lean_object* v_data_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Compiler_LCNF_Probe_filter___redArg(v_f_294_, v_data_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter(lean_object* v_00_u03b1_302_, lean_object* v_f_303_, lean_object* v_data_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v___x_310_; lean_object* v_toApplicative_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_384_; 
v___x_310_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v___x_310_, 1);
lean_dec(v_unused_385_);
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_384_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_toApplicative_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_384_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_toFunctor_315_; lean_object* v_toSeq_316_; lean_object* v_toSeqLeft_317_; lean_object* v_toSeqRight_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_382_; 
v_toFunctor_315_ = lean_ctor_get(v_toApplicative_311_, 0);
v_toSeq_316_ = lean_ctor_get(v_toApplicative_311_, 2);
v_toSeqLeft_317_ = lean_ctor_get(v_toApplicative_311_, 3);
v_toSeqRight_318_ = lean_ctor_get(v_toApplicative_311_, 4);
v_isSharedCheck_382_ = !lean_is_exclusive(v_toApplicative_311_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v_toApplicative_311_, 1);
lean_dec(v_unused_383_);
v___x_320_ = v_toApplicative_311_;
v_isShared_321_ = v_isSharedCheck_382_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_toSeqRight_318_);
lean_inc(v_toSeqLeft_317_);
lean_inc(v_toSeq_316_);
lean_inc(v_toFunctor_315_);
lean_dec(v_toApplicative_311_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_382_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___f_322_; lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___x_326_; lean_object* v___f_327_; lean_object* v___f_328_; lean_object* v___f_329_; lean_object* v___x_331_; 
v___f_322_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_323_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref(v_toFunctor_315_);
v___f_324_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_324_, 0, v_toFunctor_315_);
v___f_325_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_325_, 0, v_toFunctor_315_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___f_324_);
lean_ctor_set(v___x_326_, 1, v___f_325_);
v___f_327_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_327_, 0, v_toSeqRight_318_);
v___f_328_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_328_, 0, v_toSeqLeft_317_);
v___f_329_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_329_, 0, v_toSeq_316_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v___f_327_);
lean_ctor_set(v___x_320_, 3, v___f_328_);
lean_ctor_set(v___x_320_, 2, v___f_329_);
lean_ctor_set(v___x_320_, 1, v___f_322_);
lean_ctor_set(v___x_320_, 0, v___x_326_);
v___x_331_ = v___x_320_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___f_322_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v___f_329_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v___f_328_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v___f_327_);
v___x_331_ = v_reuseFailAlloc_381_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___f_323_);
lean_ctor_set(v___x_313_, 0, v___x_331_);
v___x_333_ = v___x_313_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___f_323_);
v___x_333_ = v_reuseFailAlloc_380_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; lean_object* v_toApplicative_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_378_; 
v___x_334_ = l_StateRefT_x27_instMonad___redArg(v___x_333_);
v_toApplicative_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v___x_334_, 1);
lean_dec(v_unused_379_);
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_378_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_toApplicative_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_378_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_toFunctor_339_; lean_object* v_toSeq_340_; lean_object* v_toSeqLeft_341_; lean_object* v_toSeqRight_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_376_; 
v_toFunctor_339_ = lean_ctor_get(v_toApplicative_335_, 0);
v_toSeq_340_ = lean_ctor_get(v_toApplicative_335_, 2);
v_toSeqLeft_341_ = lean_ctor_get(v_toApplicative_335_, 3);
v_toSeqRight_342_ = lean_ctor_get(v_toApplicative_335_, 4);
v_isSharedCheck_376_ = !lean_is_exclusive(v_toApplicative_335_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v_toApplicative_335_, 1);
lean_dec(v_unused_377_);
v___x_344_ = v_toApplicative_335_;
v_isShared_345_ = v_isSharedCheck_376_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_toSeqRight_342_);
lean_inc(v_toSeqLeft_341_);
lean_inc(v_toSeq_340_);
lean_inc(v_toFunctor_339_);
lean_dec(v_toApplicative_335_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_376_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___f_351_; lean_object* v___f_352_; lean_object* v___f_353_; lean_object* v___x_355_; 
v___f_346_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_347_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_339_);
v___f_348_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_348_, 0, v_toFunctor_339_);
v___f_349_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_349_, 0, v_toFunctor_339_);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___f_348_);
lean_ctor_set(v___x_350_, 1, v___f_349_);
v___f_351_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_351_, 0, v_toSeqRight_342_);
v___f_352_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_352_, 0, v_toSeqLeft_341_);
v___f_353_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_353_, 0, v_toSeq_340_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 4, v___f_351_);
lean_ctor_set(v___x_344_, 3, v___f_352_);
lean_ctor_set(v___x_344_, 2, v___f_353_);
lean_ctor_set(v___x_344_, 1, v___f_346_);
lean_ctor_set(v___x_344_, 0, v___x_350_);
v___x_355_ = v___x_344_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___f_346_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v___f_353_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v___f_352_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v___f_351_);
v___x_355_ = v_reuseFailAlloc_375_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v___f_347_);
lean_ctor_set(v___x_337_, 0, v___x_355_);
v___x_357_ = v___x_337_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___f_347_);
v___x_357_ = v_reuseFailAlloc_374_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_array_get_size(v_data_304_);
v___x_360_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0));
v___x_361_ = lean_nat_dec_lt(v___x_358_, v___x_359_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec_ref(v___x_357_);
lean_dec_ref(v_data_304_);
lean_dec_ref(v_f_303_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
return v___x_362_;
}
else
{
lean_object* v___f_363_; uint8_t v___x_364_; 
v___f_363_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_363_, 0, v_f_303_);
v___x_364_ = lean_nat_dec_le(v___x_359_, v___x_359_);
if (v___x_364_ == 0)
{
if (v___x_361_ == 0)
{
lean_object* v___x_365_; 
lean_dec_ref(v___f_363_);
lean_dec_ref(v___x_357_);
lean_dec_ref(v_data_304_);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_360_);
return v___x_365_;
}
else
{
size_t v___x_366_; size_t v___x_367_; lean_object* v___x_448__overap_368_; lean_object* v___x_369_; 
v___x_366_ = ((size_t)0ULL);
v___x_367_ = lean_usize_of_nat(v___x_359_);
v___x_448__overap_368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_357_, v___f_363_, v_data_304_, v___x_366_, v___x_367_, v___x_360_);
lean_inc(v_a_308_);
lean_inc_ref(v_a_307_);
lean_inc(v_a_306_);
lean_inc_ref(v_a_305_);
v___x_369_ = lean_apply_5(v___x_448__overap_368_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, lean_box(0));
return v___x_369_;
}
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_451__overap_372_; lean_object* v___x_373_; 
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_359_);
v___x_451__overap_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_357_, v___f_363_, v_data_304_, v___x_370_, v___x_371_, v___x_360_);
lean_inc(v_a_308_);
lean_inc_ref(v_a_307_);
lean_inc(v_a_306_);
lean_inc_ref(v_a_305_);
v___x_373_ = lean_apply_5(v___x_451__overap_372_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, lean_box(0));
return v___x_373_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___boxed(lean_object* v_00_u03b1_386_, lean_object* v_f_387_, lean_object* v_data_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Compiler_LCNF_Probe_filter(v_00_u03b1_386_, v_f_387_, v_data_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
return v_res_394_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(lean_object* v_inst_395_, lean_object* v_x1_396_, lean_object* v_x2_397_){
_start:
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = lean_apply_2(v_inst_395_, v_x1_396_, v_x2_397_);
v___x_399_ = lean_unbox(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed(lean_object* v_inst_400_, lean_object* v_x1_401_, lean_object* v_x2_402_){
_start:
{
uint8_t v_res_403_; lean_object* v_r_404_; 
v_res_403_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(v_inst_400_, v_x1_401_, v_x2_402_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg(lean_object* v_inst_405_, lean_object* v_data_406_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = lean_array_get_size(v_data_406_);
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_nat_dec_eq(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___f_411_; lean_object* v___y_413_; lean_object* v___y_414_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___y_420_; uint8_t v___x_422_; 
v___f_411_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_411_, 0, v_inst_405_);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = lean_nat_sub(v___x_408_, v___x_417_);
v___x_422_ = lean_nat_dec_le(v___x_409_, v___x_418_);
if (v___x_422_ == 0)
{
lean_inc(v___x_418_);
v___y_420_ = v___x_418_;
goto v___jp_419_;
}
else
{
v___y_420_ = v___x_409_;
goto v___jp_419_;
}
v___jp_412_:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_411_, v___x_408_, v_data_406_, v___y_413_, v___y_414_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_414_);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
v___jp_419_:
{
uint8_t v___x_421_; 
v___x_421_ = lean_nat_dec_le(v___y_420_, v___x_418_);
if (v___x_421_ == 0)
{
lean_dec(v___x_418_);
lean_inc(v___y_420_);
v___y_413_ = v___y_420_;
v___y_414_ = v___y_420_;
goto v___jp_412_;
}
else
{
v___y_413_ = v___y_420_;
v___y_414_ = v___x_418_;
goto v___jp_412_;
}
}
}
else
{
lean_object* v___x_423_; 
lean_dec_ref(v_inst_405_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_data_406_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg___boxed(lean_object* v_inst_424_, lean_object* v_data_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg(v_inst_424_, v_data_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted(lean_object* v_00_u03b1_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_data_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_438_ = lean_array_get_size(v_data_432_);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_nat_dec_eq(v___x_438_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___f_441_; lean_object* v___y_443_; lean_object* v___y_444_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___y_450_; uint8_t v___x_452_; 
v___f_441_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_441_, 0, v_inst_431_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_sub(v___x_438_, v___x_447_);
v___x_452_ = lean_nat_dec_le(v___x_439_, v___x_448_);
if (v___x_452_ == 0)
{
lean_inc(v___x_448_);
v___y_450_ = v___x_448_;
goto v___jp_449_;
}
else
{
v___y_450_ = v___x_439_;
goto v___jp_449_;
}
v___jp_442_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_441_, v___x_438_, v_data_432_, v___y_443_, v___y_444_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_444_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
v___jp_449_:
{
uint8_t v___x_451_; 
v___x_451_ = lean_nat_dec_le(v___y_450_, v___x_448_);
if (v___x_451_ == 0)
{
lean_dec(v___x_448_);
lean_inc(v___y_450_);
v___y_443_ = v___y_450_;
v___y_444_ = v___y_450_;
goto v___jp_442_;
}
else
{
v___y_443_ = v___y_450_;
v___y_444_ = v___x_448_;
goto v___jp_442_;
}
}
}
else
{
lean_object* v___x_453_; 
lean_dec_ref(v_inst_431_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v_data_432_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___boxed(lean_object* v_00_u03b1_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_data_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Compiler_LCNF_Probe_sorted(v_00_u03b1_454_, v_inst_455_, v_inst_456_, v_inst_457_, v_data_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_inst_455_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(uint8_t v_pu_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = l_Lean_Compiler_LCNF_Decl_size(v_pu_465_, v_x_466_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_x_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed(lean_object* v_pu_469_, lean_object* v_x_470_){
_start:
{
uint8_t v_pu_boxed_471_; lean_object* v_res_472_; 
v_pu_boxed_471_ = lean_unbox(v_pu_469_);
v_res_472_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(v_pu_boxed_471_, v_x_470_);
return v_res_472_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v_fst_475_; lean_object* v_snd_476_; lean_object* v_fst_477_; lean_object* v_snd_478_; uint8_t v___x_479_; 
v_fst_475_ = lean_ctor_get(v_x_473_, 0);
v_snd_476_ = lean_ctor_get(v_x_473_, 1);
v_fst_477_ = lean_ctor_get(v_x_474_, 0);
v_snd_478_ = lean_ctor_get(v_x_474_, 1);
v___x_479_ = lean_nat_dec_eq(v_fst_475_, v_fst_477_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
v___x_480_ = lean_nat_dec_lt(v_fst_475_, v_fst_477_);
return v___x_480_;
}
else
{
lean_object* v_toSignature_481_; lean_object* v_toSignature_482_; lean_object* v_name_483_; lean_object* v_name_484_; uint8_t v___x_485_; 
v_toSignature_481_ = lean_ctor_get(v_snd_476_, 0);
v_toSignature_482_ = lean_ctor_get(v_snd_478_, 0);
v_name_483_ = lean_ctor_get(v_toSignature_481_, 0);
v_name_484_ = lean_ctor_get(v_toSignature_482_, 0);
v___x_485_ = l_Lean_Name_lt(v_name_483_, v_name_484_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1___boxed(lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
uint8_t v_res_488_; lean_object* v_r_489_; 
v_res_488_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(v_x_486_, v_x_487_);
lean_dec_ref(v_x_487_);
lean_dec_ref(v_x_486_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(uint8_t v_pu_510_, lean_object* v_decls_511_){
_start:
{
lean_object* v___x_513_; lean_object* v___f_514_; lean_object* v___x_515_; size_t v_sz_516_; size_t v___x_517_; lean_object* v_decls_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_513_ = lean_box(v_pu_510_);
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_514_, 0, v___x_513_);
v___x_515_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v_sz_516_ = lean_array_size(v_decls_511_);
v___x_517_ = ((size_t)0ULL);
v_decls_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_515_, v___f_514_, v_sz_516_, v___x_517_, v_decls_511_);
v___x_519_ = lean_array_get_size(v_decls_518_);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_nat_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___f_522_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___y_531_; uint8_t v___x_533_; 
v___f_522_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10));
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_sub(v___x_519_, v___x_528_);
v___x_533_ = lean_nat_dec_le(v___x_520_, v___x_529_);
if (v___x_533_ == 0)
{
lean_inc(v___x_529_);
v___y_531_ = v___x_529_;
goto v___jp_530_;
}
else
{
v___y_531_ = v___x_520_;
goto v___jp_530_;
}
v___jp_523_:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_522_, v___x_519_, v_decls_518_, v___y_524_, v___y_525_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_525_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
v___jp_530_:
{
uint8_t v___x_532_; 
v___x_532_ = lean_nat_dec_le(v___y_531_, v___x_529_);
if (v___x_532_ == 0)
{
lean_dec(v___x_529_);
lean_inc(v___y_531_);
v___y_524_ = v___y_531_;
v___y_525_ = v___y_531_;
goto v___jp_523_;
}
else
{
v___y_524_ = v___y_531_;
v___y_525_ = v___x_529_;
goto v___jp_523_;
}
}
}
else
{
lean_object* v___x_534_; 
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v_decls_518_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___boxed(lean_object* v_pu_535_, lean_object* v_decls_536_, lean_object* v_a_537_){
_start:
{
uint8_t v_pu_boxed_538_; lean_object* v_res_539_; 
v_pu_boxed_538_ = lean_unbox(v_pu_535_);
v_res_539_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(v_pu_boxed_538_, v_decls_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize(uint8_t v_pu_540_, lean_object* v_decls_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_547_; lean_object* v___f_548_; lean_object* v___x_549_; size_t v_sz_550_; size_t v___x_551_; lean_object* v_decls_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_547_ = lean_box(v_pu_540_);
v___f_548_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_548_, 0, v___x_547_);
v___x_549_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v_sz_550_ = lean_array_size(v_decls_541_);
v___x_551_ = ((size_t)0ULL);
v_decls_552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_549_, v___f_548_, v_sz_550_, v___x_551_, v_decls_541_);
v___x_553_ = lean_array_get_size(v_decls_552_);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_nat_dec_eq(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___f_556_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___y_565_; uint8_t v___x_567_; 
v___f_556_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10));
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_sub(v___x_553_, v___x_562_);
v___x_567_ = lean_nat_dec_le(v___x_554_, v___x_563_);
if (v___x_567_ == 0)
{
lean_inc(v___x_563_);
v___y_565_ = v___x_563_;
goto v___jp_564_;
}
else
{
v___y_565_ = v___x_554_;
goto v___jp_564_;
}
v___jp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_556_, v___x_553_, v_decls_552_, v___y_558_, v___y_559_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
v___jp_564_:
{
uint8_t v___x_566_; 
v___x_566_ = lean_nat_dec_le(v___y_565_, v___x_563_);
if (v___x_566_ == 0)
{
lean_dec(v___x_563_);
lean_inc(v___y_565_);
v___y_558_ = v___y_565_;
v___y_559_ = v___y_565_;
goto v___jp_557_;
}
else
{
v___y_558_ = v___y_565_;
v___y_559_ = v___x_563_;
goto v___jp_557_;
}
}
}
else
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v_decls_552_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___boxed(lean_object* v_pu_569_, lean_object* v_decls_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
uint8_t v_pu_boxed_576_; lean_object* v_res_577_; 
v_pu_boxed_576_ = lean_unbox(v_pu_569_);
v_res_577_ = l_Lean_Compiler_LCNF_Probe_sortedBySize(v_pu_boxed_576_, v_decls_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(lean_object* v_inst_578_, lean_object* v_inst_579_, lean_object* v_a_580_, lean_object* v_x_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; 
lean_inc(v_a_580_);
lean_inc_ref(v_inst_579_);
lean_inc_ref(v_inst_578_);
v___x_588_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_578_, v_inst_579_, v___y_582_, v_a_580_);
if (lean_obj_tag(v___x_588_) == 1)
{
lean_object* v_val_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_600_; 
v_val_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_600_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_val_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_add(v_val_589_, v___x_593_);
lean_dec(v_val_589_);
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_578_, v_inst_579_, v___y_582_, v_a_580_, v___x_594_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_595_);
v___x_597_ = v___x_591_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_599_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; 
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v___x_588_);
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_578_, v_inst_579_, v___y_582_, v_a_580_, v___x_601_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed(lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_a_607_, lean_object* v_x_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(v_inst_605_, v_inst_606_, v_a_607_, v_x_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__1(lean_object* v_x1_616_, lean_object* v_x2_617_, lean_object* v_x3_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v_x2_617_);
lean_ctor_set(v___x_619_, 1, v_x3_618_);
v___x_620_ = lean_array_push(v_x1_616_, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__2(lean_object* v___x_621_, lean_object* v___f_622_, lean_object* v_acc_623_, lean_object* v_l_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_621_, v___f_622_, v_acc_623_, v_l_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg(lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_data_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_638_; lean_object* v_toApplicative_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_748_; 
v___x_638_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_748_ == 0)
{
lean_object* v_unused_749_; 
v_unused_749_ = lean_ctor_get(v___x_638_, 1);
lean_dec(v_unused_749_);
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_748_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_toApplicative_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_748_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v_toFunctor_643_; lean_object* v_toSeq_644_; lean_object* v_toSeqLeft_645_; lean_object* v_toSeqRight_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_746_; 
v_toFunctor_643_ = lean_ctor_get(v_toApplicative_639_, 0);
v_toSeq_644_ = lean_ctor_get(v_toApplicative_639_, 2);
v_toSeqLeft_645_ = lean_ctor_get(v_toApplicative_639_, 3);
v_toSeqRight_646_ = lean_ctor_get(v_toApplicative_639_, 4);
v_isSharedCheck_746_ = !lean_is_exclusive(v_toApplicative_639_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v_toApplicative_639_, 1);
lean_dec(v_unused_747_);
v___x_648_ = v_toApplicative_639_;
v_isShared_649_ = v_isSharedCheck_746_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_toSeqRight_646_);
lean_inc(v_toSeqLeft_645_);
lean_inc(v_toSeq_644_);
lean_inc(v_toFunctor_643_);
lean_dec(v_toApplicative_639_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_746_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___f_650_; lean_object* v___f_651_; lean_object* v___f_652_; lean_object* v___f_653_; lean_object* v___x_654_; lean_object* v___f_655_; lean_object* v___f_656_; lean_object* v___f_657_; lean_object* v___x_659_; 
v___f_650_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_651_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref(v_toFunctor_643_);
v___f_652_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_652_, 0, v_toFunctor_643_);
v___f_653_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_653_, 0, v_toFunctor_643_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___f_652_);
lean_ctor_set(v___x_654_, 1, v___f_653_);
v___f_655_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_655_, 0, v_toSeqRight_646_);
v___f_656_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_656_, 0, v_toSeqLeft_645_);
v___f_657_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_657_, 0, v_toSeq_644_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 4, v___f_655_);
lean_ctor_set(v___x_648_, 3, v___f_656_);
lean_ctor_set(v___x_648_, 2, v___f_657_);
lean_ctor_set(v___x_648_, 1, v___f_650_);
lean_ctor_set(v___x_648_, 0, v___x_654_);
v___x_659_ = v___x_648_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___f_650_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v___f_657_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v___f_656_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v___f_655_);
v___x_659_ = v_reuseFailAlloc_745_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_661_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___f_651_);
lean_ctor_set(v___x_641_, 0, v___x_659_);
v___x_661_ = v___x_641_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___f_651_);
v___x_661_ = v_reuseFailAlloc_744_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v_toApplicative_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_742_; 
v___x_662_ = l_StateRefT_x27_instMonad___redArg(v___x_661_);
v_toApplicative_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_662_, 1);
lean_dec(v_unused_743_);
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_742_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_toApplicative_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_742_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_toFunctor_667_; lean_object* v_toSeq_668_; lean_object* v_toSeqLeft_669_; lean_object* v_toSeqRight_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_740_; 
v_toFunctor_667_ = lean_ctor_get(v_toApplicative_663_, 0);
v_toSeq_668_ = lean_ctor_get(v_toApplicative_663_, 2);
v_toSeqLeft_669_ = lean_ctor_get(v_toApplicative_663_, 3);
v_toSeqRight_670_ = lean_ctor_get(v_toApplicative_663_, 4);
v_isSharedCheck_740_ = !lean_is_exclusive(v_toApplicative_663_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_toApplicative_663_, 1);
lean_dec(v_unused_741_);
v___x_672_ = v_toApplicative_663_;
v_isShared_673_ = v_isSharedCheck_740_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_toSeqRight_670_);
lean_inc(v_toSeqLeft_669_);
lean_inc(v_toSeq_668_);
lean_inc(v_toFunctor_667_);
lean_dec(v_toApplicative_663_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_740_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___f_677_; lean_object* v___f_678_; lean_object* v___x_679_; lean_object* v___f_680_; lean_object* v___f_681_; lean_object* v___f_682_; lean_object* v___x_684_; 
v___f_674_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_674_, 0, v_inst_630_);
lean_closure_set(v___f_674_, 1, v_inst_631_);
v___f_675_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_676_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_667_);
v___f_677_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_677_, 0, v_toFunctor_667_);
v___f_678_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_678_, 0, v_toFunctor_667_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___f_677_);
lean_ctor_set(v___x_679_, 1, v___f_678_);
v___f_680_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_680_, 0, v_toSeqRight_670_);
v___f_681_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_681_, 0, v_toSeqLeft_669_);
v___f_682_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_682_, 0, v_toSeq_668_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 4, v___f_680_);
lean_ctor_set(v___x_672_, 3, v___f_681_);
lean_ctor_set(v___x_672_, 2, v___f_682_);
lean_ctor_set(v___x_672_, 1, v___f_675_);
lean_ctor_set(v___x_672_, 0, v___x_679_);
v___x_684_ = v___x_672_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___f_675_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v___f_682_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v___f_681_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v___f_680_);
v___x_684_ = v_reuseFailAlloc_739_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_686_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___f_676_);
lean_ctor_set(v___x_665_, 0, v___x_684_);
v___x_686_ = v___x_665_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___f_676_);
v___x_686_ = v_reuseFailAlloc_738_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v_map_696_; size_t v_sz_697_; size_t v___x_698_; lean_object* v___x_747__overap_699_; lean_object* v___x_700_; 
v___x_687_ = lean_array_get_size(v_data_632_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_unsigned_to_nat(4u);
v___x_690_ = lean_nat_mul(v___x_687_, v___x_689_);
v___x_691_ = lean_unsigned_to_nat(3u);
v___x_692_ = lean_nat_div(v___x_690_, v___x_691_);
lean_dec(v___x_690_);
v___x_693_ = l_Nat_nextPowerOfTwo(v___x_692_);
lean_dec(v___x_692_);
v___x_694_ = lean_box(0);
v___x_695_ = lean_mk_array(v___x_693_, v___x_694_);
v_map_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_map_696_, 0, v___x_688_);
lean_ctor_set(v_map_696_, 1, v___x_695_);
v_sz_697_ = lean_array_size(v_data_632_);
v___x_698_ = ((size_t)0ULL);
v___x_747__overap_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_686_, v_data_632_, v___f_674_, v_sz_697_, v___x_698_, v_map_696_);
lean_inc(v_a_636_);
lean_inc_ref(v_a_635_);
lean_inc(v_a_634_);
lean_inc_ref(v_a_633_);
v___x_700_ = lean_apply_5(v___x_747__overap_699_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, lean_box(0));
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_729_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_729_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_729_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_729_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_size_705_; lean_object* v_buckets_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_size_705_ = lean_ctor_get(v_a_701_, 0);
lean_inc(v_size_705_);
v_buckets_706_ = lean_ctor_get(v_a_701_, 1);
lean_inc_ref(v_buckets_706_);
lean_dec(v_a_701_);
v___x_707_ = lean_mk_empty_array_with_capacity(v_size_705_);
lean_dec(v_size_705_);
v___x_708_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_709_ = lean_array_get_size(v_buckets_706_);
v___x_710_ = lean_nat_dec_lt(v___x_688_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v_buckets_706_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_712_ = v___x_703_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
else
{
lean_object* v___f_714_; uint8_t v___x_715_; 
v___f_714_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1));
v___x_715_ = lean_nat_dec_le(v___x_709_, v___x_709_);
if (v___x_715_ == 0)
{
if (v___x_710_ == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v_buckets_706_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_717_ = v___x_703_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_707_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
size_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_719_ = lean_usize_of_nat(v___x_709_);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_708_, v___f_714_, v_buckets_706_, v___x_698_, v___x_719_, v___x_707_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_720_);
v___x_722_ = v___x_703_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
size_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_724_ = lean_usize_of_nat(v___x_709_);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_708_, v___f_714_, v_buckets_706_, v___x_698_, v___x_724_, v___x_707_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_725_);
v___x_727_ = v___x_703_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_700_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_700_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___boxed(lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_data_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_750_, v_inst_751_, v_data_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique(lean_object* v_00_u03b1_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_data_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_761_, v_inst_762_, v_data_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___boxed(lean_object* v_00_u03b1_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_data_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Compiler_LCNF_Probe_countUnique(v_00_u03b1_770_, v_inst_771_, v_inst_772_, v_inst_773_, v_data_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec_ref(v_inst_771_);
return v_res_780_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(lean_object* v_l_781_, lean_object* v_r_782_){
_start:
{
lean_object* v_snd_783_; lean_object* v_snd_784_; uint8_t v___x_785_; 
v_snd_783_ = lean_ctor_get(v_l_781_, 1);
v_snd_784_ = lean_ctor_get(v_r_782_, 1);
v___x_785_ = lean_nat_dec_lt(v_snd_783_, v_snd_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0___boxed(lean_object* v_l_786_, lean_object* v_r_787_){
_start:
{
uint8_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(v_l_786_, v_r_787_);
lean_dec_ref(v_r_787_);
lean_dec_ref(v_l_786_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_791_, v_inst_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
v___x_801_ = lean_array_get_size(v_a_800_);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_nat_dec_eq(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_821_; 
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_799_, 0);
lean_dec(v_unused_822_);
v___x_805_ = v___x_799_;
v_isShared_806_ = v_isSharedCheck_821_;
goto v_resetjp_804_;
}
else
{
lean_dec(v___x_799_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_821_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___f_807_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___y_818_; uint8_t v___x_820_; 
v___f_807_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_sub(v___x_801_, v___x_815_);
v___x_820_ = lean_nat_dec_le(v___x_802_, v___x_816_);
if (v___x_820_ == 0)
{
lean_inc(v___x_816_);
v___y_818_ = v___x_816_;
goto v___jp_817_;
}
else
{
v___y_818_ = v___x_802_;
goto v___jp_817_;
}
v___jp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_807_, v___x_801_, v_a_800_, v___y_809_, v___y_810_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_810_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_811_);
v___x_813_ = v___x_805_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
v___jp_817_:
{
uint8_t v___x_819_; 
v___x_819_ = lean_nat_dec_le(v___y_818_, v___x_816_);
if (v___x_819_ == 0)
{
lean_dec(v___x_816_);
lean_inc(v___y_818_);
v___y_809_ = v___y_818_;
v___y_810_ = v___y_818_;
goto v___jp_808_;
}
else
{
v___y_809_ = v___y_818_;
v___y_810_ = v___x_816_;
goto v___jp_808_;
}
}
}
}
else
{
lean_dec(v_a_800_);
return v___x_799_;
}
}
else
{
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___boxed(lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(v_inst_823_, v_inst_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted(lean_object* v_00_u03b1_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_834_, v_inst_835_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
v___x_845_ = lean_array_get_size(v_a_844_);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_nat_dec_eq(v___x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_865_; 
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v___x_843_, 0);
lean_dec(v_unused_866_);
v___x_849_ = v___x_843_;
v_isShared_850_ = v_isSharedCheck_865_;
goto v_resetjp_848_;
}
else
{
lean_dec(v___x_843_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_865_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___f_851_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___y_862_; uint8_t v___x_864_; 
v___f_851_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_859_ = lean_unsigned_to_nat(1u);
v___x_860_ = lean_nat_sub(v___x_845_, v___x_859_);
v___x_864_ = lean_nat_dec_le(v___x_846_, v___x_860_);
if (v___x_864_ == 0)
{
lean_inc(v___x_860_);
v___y_862_ = v___x_860_;
goto v___jp_861_;
}
else
{
v___y_862_ = v___x_846_;
goto v___jp_861_;
}
v___jp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_851_, v___x_845_, v_a_844_, v___y_853_, v___y_854_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_854_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_855_);
v___x_857_ = v___x_849_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
v___jp_861_:
{
uint8_t v___x_863_; 
v___x_863_ = lean_nat_dec_le(v___y_862_, v___x_860_);
if (v___x_863_ == 0)
{
lean_dec(v___x_860_);
lean_inc(v___y_862_);
v___y_853_ = v___y_862_;
v___y_854_ = v___y_862_;
goto v___jp_852_;
}
else
{
v___y_853_ = v___y_862_;
v___y_854_ = v___x_860_;
goto v___jp_852_;
}
}
}
}
else
{
lean_dec(v_a_844_);
return v___x_843_;
}
}
else
{
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___boxed(lean_object* v_00_u03b1_867_, lean_object* v_inst_868_, lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted(v_00_u03b1_867_, v_inst_868_, v_inst_869_, v_inst_870_, v_inst_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_inst_871_);
lean_dec_ref(v_inst_868_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(uint8_t v_pu_879_, lean_object* v_c_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
switch(lean_obj_tag(v_c_880_))
{
case 0:
{
lean_object* v_decl_887_; lean_object* v_k_888_; lean_object* v___x_889_; lean_object* v_value_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_decl_887_ = lean_ctor_get(v_c_880_, 0);
lean_inc_ref(v_decl_887_);
v_k_888_ = lean_ctor_get(v_c_880_, 1);
lean_inc_ref(v_k_888_);
lean_dec_ref(v_c_880_);
v___x_889_ = lean_st_ref_take(v_a_881_);
v_value_890_ = lean_ctor_get(v_decl_887_, 3);
lean_inc(v_value_890_);
lean_dec_ref(v_decl_887_);
v___x_891_ = lean_array_push(v___x_889_, v_value_890_);
v___x_892_ = lean_st_ref_set(v_a_881_, v___x_891_);
v_c_880_ = v_k_888_;
goto _start;
}
case 1:
{
lean_object* v_decl_894_; lean_object* v_k_895_; lean_object* v_value_896_; lean_object* v___x_897_; 
v_decl_894_ = lean_ctor_get(v_c_880_, 0);
lean_inc_ref(v_decl_894_);
v_k_895_ = lean_ctor_get(v_c_880_, 1);
lean_inc_ref(v_k_895_);
lean_dec_ref(v_c_880_);
v_value_896_ = lean_ctor_get(v_decl_894_, 4);
lean_inc_ref(v_value_896_);
lean_dec_ref(v_decl_894_);
v___x_897_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_879_, v_value_896_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_dec_ref(v___x_897_);
v_c_880_ = v_k_895_;
goto _start;
}
else
{
lean_dec_ref(v_k_895_);
return v___x_897_;
}
}
case 2:
{
lean_object* v_decl_899_; lean_object* v_k_900_; lean_object* v_value_901_; lean_object* v___x_902_; 
v_decl_899_ = lean_ctor_get(v_c_880_, 0);
lean_inc_ref(v_decl_899_);
v_k_900_ = lean_ctor_get(v_c_880_, 1);
lean_inc_ref(v_k_900_);
lean_dec_ref(v_c_880_);
v_value_901_ = lean_ctor_get(v_decl_899_, 4);
lean_inc_ref(v_value_901_);
lean_dec_ref(v_decl_899_);
v___x_902_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_879_, v_value_901_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_dec_ref(v___x_902_);
v_c_880_ = v_k_900_;
goto _start;
}
else
{
lean_dec_ref(v_k_900_);
return v___x_902_;
}
}
case 4:
{
lean_object* v_cases_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_926_; 
v_cases_904_ = lean_ctor_get(v_c_880_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_c_880_);
if (v_isSharedCheck_926_ == 0)
{
v___x_906_ = v_c_880_;
v_isShared_907_ = v_isSharedCheck_926_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_cases_904_);
lean_dec(v_c_880_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_926_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_alts_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_alts_908_ = lean_ctor_get(v_cases_904_, 3);
lean_inc_ref(v_alts_908_);
lean_dec_ref(v_cases_904_);
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_array_get_size(v_alts_908_);
v___x_911_ = lean_box(0);
v___x_912_ = lean_nat_dec_lt(v___x_909_, v___x_910_);
if (v___x_912_ == 0)
{
lean_object* v___x_914_; 
lean_dec_ref(v_alts_908_);
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 0);
lean_ctor_set(v___x_906_, 0, v___x_911_);
v___x_914_ = v___x_906_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_911_);
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
uint8_t v___x_916_; 
v___x_916_ = lean_nat_dec_le(v___x_910_, v___x_910_);
if (v___x_916_ == 0)
{
if (v___x_912_ == 0)
{
lean_object* v___x_918_; 
lean_dec_ref(v_alts_908_);
if (v_isShared_907_ == 0)
{
lean_ctor_set_tag(v___x_906_, 0);
lean_ctor_set(v___x_906_, 0, v___x_911_);
v___x_918_ = v___x_906_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_911_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
else
{
size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; 
lean_del_object(v___x_906_);
v___x_920_ = ((size_t)0ULL);
v___x_921_ = lean_usize_of_nat(v___x_910_);
v___x_922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_879_, v_alts_908_, v___x_920_, v___x_921_, v___x_911_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec_ref(v_alts_908_);
return v___x_922_;
}
}
else
{
size_t v___x_923_; size_t v___x_924_; lean_object* v___x_925_; 
lean_del_object(v___x_906_);
v___x_923_ = ((size_t)0ULL);
v___x_924_ = lean_usize_of_nat(v___x_910_);
v___x_925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_879_, v_alts_908_, v___x_923_, v___x_924_, v___x_911_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec_ref(v_alts_908_);
return v___x_925_;
}
}
}
}
case 7:
{
lean_object* v_k_927_; 
v_k_927_ = lean_ctor_get(v_c_880_, 3);
lean_inc_ref(v_k_927_);
lean_dec_ref(v_c_880_);
v_c_880_ = v_k_927_;
goto _start;
}
case 8:
{
lean_object* v_k_929_; 
v_k_929_ = lean_ctor_get(v_c_880_, 3);
lean_inc_ref(v_k_929_);
lean_dec_ref(v_c_880_);
v_c_880_ = v_k_929_;
goto _start;
}
case 9:
{
lean_object* v_k_931_; 
v_k_931_ = lean_ctor_get(v_c_880_, 5);
lean_inc_ref(v_k_931_);
lean_dec_ref(v_c_880_);
v_c_880_ = v_k_931_;
goto _start;
}
case 10:
{
lean_object* v_k_933_; 
v_k_933_ = lean_ctor_get(v_c_880_, 2);
lean_inc_ref(v_k_933_);
lean_dec_ref(v_c_880_);
v_c_880_ = v_k_933_;
goto _start;
}
case 11:
{
lean_object* v_k_935_; 
v_k_935_ = lean_ctor_get(v_c_880_, 2);
lean_inc_ref(v_k_935_);
lean_dec_ref(v_c_880_);
v_c_880_ = v_k_935_;
goto _start;
}
case 12:
{
lean_object* v_k_937_; 
v_k_937_ = lean_ctor_get(v_c_880_, 2);
lean_inc_ref(v_k_937_);
lean_dec_ref(v_c_880_);
v_c_880_ = v_k_937_;
goto _start;
}
case 13:
{
lean_object* v_k_939_; 
v_k_939_ = lean_ctor_get(v_c_880_, 1);
lean_inc_ref(v_k_939_);
lean_dec_ref(v_c_880_);
v_c_880_ = v_k_939_;
goto _start;
}
default: 
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec_ref(v_c_880_);
v___x_941_ = lean_box(0);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(uint8_t v_pu_943_, lean_object* v_as_944_, size_t v_i_945_, size_t v_stop_946_, lean_object* v_b_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___y_955_; uint8_t v___x_961_; 
v___x_961_ = lean_usize_dec_eq(v_i_945_, v_stop_946_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
v___x_962_ = lean_array_uget_borrowed(v_as_944_, v_i_945_);
switch(lean_obj_tag(v___x_962_))
{
case 0:
{
lean_object* v_code_963_; 
v_code_963_ = lean_ctor_get(v___x_962_, 2);
lean_inc_ref(v_code_963_);
v___y_955_ = v_code_963_;
goto v___jp_954_;
}
case 1:
{
lean_object* v_code_964_; 
v_code_964_ = lean_ctor_get(v___x_962_, 1);
lean_inc_ref(v_code_964_);
v___y_955_ = v_code_964_;
goto v___jp_954_;
}
default: 
{
lean_object* v_code_965_; 
v_code_965_ = lean_ctor_get(v___x_962_, 0);
lean_inc_ref(v_code_965_);
v___y_955_ = v_code_965_;
goto v___jp_954_;
}
}
}
else
{
lean_object* v___x_966_; 
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v_b_947_);
return v___x_966_;
}
v___jp_954_:
{
lean_object* v___x_956_; 
v___x_956_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_943_, v___y_955_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; size_t v___x_958_; size_t v___x_959_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v___x_956_);
v___x_958_ = ((size_t)1ULL);
v___x_959_ = lean_usize_add(v_i_945_, v___x_958_);
v_i_945_ = v___x_959_;
v_b_947_ = v_a_957_;
goto _start;
}
else
{
return v___x_956_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0___boxed(lean_object* v_pu_967_, lean_object* v_as_968_, lean_object* v_i_969_, lean_object* v_stop_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
uint8_t v_pu_boxed_978_; size_t v_i_boxed_979_; size_t v_stop_boxed_980_; lean_object* v_res_981_; 
v_pu_boxed_978_ = lean_unbox(v_pu_967_);
v_i_boxed_979_ = lean_unbox_usize(v_i_969_);
lean_dec(v_i_969_);
v_stop_boxed_980_ = lean_unbox_usize(v_stop_970_);
lean_dec(v_stop_970_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_boxed_978_, v_as_968_, v_i_boxed_979_, v_stop_boxed_980_, v_b_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v_as_968_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed(lean_object* v_pu_982_, lean_object* v_c_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
uint8_t v_pu_boxed_990_; lean_object* v_res_991_; 
v_pu_boxed_990_ = lean_unbox(v_pu_982_);
v_res_991_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_boxed_990_, v_c_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(lean_object* v_f_992_, lean_object* v_v_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
if (lean_obj_tag(v_v_993_) == 0)
{
lean_object* v_code_1000_; lean_object* v___x_1001_; 
v_code_1000_ = lean_ctor_get(v_v_993_, 0);
lean_inc_ref(v_code_1000_);
lean_dec_ref(v_v_993_);
lean_inc(v___y_998_);
lean_inc_ref(v___y_997_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc(v___y_994_);
v___x_1001_ = lean_apply_7(v_f_992_, v_code_1000_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, lean_box(0));
return v___x_1001_;
}
else
{
lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1009_; 
lean_dec_ref(v_f_992_);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_v_993_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_v_993_, 0);
lean_dec(v_unused_1010_);
v___x_1003_ = v_v_993_;
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
else
{
lean_dec(v_v_993_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1009_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_box(0);
if (v_isShared_1004_ == 0)
{
lean_ctor_set_tag(v___x_1003_, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1005_);
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg___boxed(lean_object* v_f_1011_, lean_object* v_v_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_1011_, v_v_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(uint8_t v_pu_1020_, lean_object* v_f_1021_, lean_object* v_v_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_1021_, v_v_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___boxed(lean_object* v_pu_1030_, lean_object* v_f_1031_, lean_object* v_v_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v_pu_boxed_1039_; lean_object* v_res_1040_; 
v_pu_boxed_1039_ = lean_unbox(v_pu_1030_);
v_res_1040_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(v_pu_boxed_1039_, v_f_1031_, v_v_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(uint8_t v_pu_1041_, lean_object* v_as_1042_, size_t v_i_1043_, size_t v_stop_1044_, lean_object* v_b_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_usize_dec_eq(v_i_1043_, v_stop_1044_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v_value_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1053_ = lean_array_uget_borrowed(v_as_1042_, v_i_1043_);
v_value_1054_ = lean_ctor_get(v___x_1053_, 1);
v___x_1055_ = lean_box(v_pu_1041_);
v___x_1056_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed), 8, 1);
lean_closure_set(v___x_1056_, 0, v___x_1055_);
lean_inc_ref(v_value_1054_);
v___x_1057_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v___x_1056_, v_value_1054_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; size_t v___x_1059_; size_t v___x_1060_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = ((size_t)1ULL);
v___x_1060_ = lean_usize_add(v_i_1043_, v___x_1059_);
v_i_1043_ = v___x_1060_;
v_b_1045_ = v_a_1058_;
goto _start;
}
else
{
return v___x_1057_;
}
}
else
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_b_1045_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1___boxed(lean_object* v_pu_1063_, lean_object* v_as_1064_, lean_object* v_i_1065_, lean_object* v_stop_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
uint8_t v_pu_boxed_1074_; size_t v_i_boxed_1075_; size_t v_stop_boxed_1076_; lean_object* v_res_1077_; 
v_pu_boxed_1074_ = lean_unbox(v_pu_1063_);
v_i_boxed_1075_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_stop_boxed_1076_ = lean_unbox_usize(v_stop_1066_);
lean_dec(v_stop_1066_);
v_res_1077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_boxed_1074_, v_as_1064_, v_i_boxed_1075_, v_stop_boxed_1076_, v_b_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v_as_1064_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(uint8_t v_pu_1078_, lean_object* v_decls_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = lean_array_get_size(v_decls_1079_);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_nat_dec_lt(v___x_1086_, v___x_1087_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
return v___x_1090_;
}
else
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_nat_dec_le(v___x_1087_, v___x_1087_);
if (v___x_1091_ == 0)
{
if (v___x_1089_ == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1088_);
return v___x_1092_;
}
else
{
size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = lean_usize_of_nat(v___x_1087_);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_1078_, v_decls_1079_, v___x_1093_, v___x_1094_, v___x_1088_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
return v___x_1095_;
}
}
else
{
size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = ((size_t)0ULL);
v___x_1097_ = lean_usize_of_nat(v___x_1087_);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_1078_, v_decls_1079_, v___x_1096_, v___x_1097_, v___x_1088_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start___boxed(lean_object* v_pu_1099_, lean_object* v_decls_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
uint8_t v_pu_boxed_1107_; lean_object* v_res_1108_; 
v_pu_boxed_1107_ = lean_unbox(v_pu_1099_);
v_res_1108_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_boxed_1107_, v_decls_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_decls_1100_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues(uint8_t v_pu_1111_, lean_object* v_decls_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0));
v___x_1119_ = lean_st_mk_ref(v___x_1118_);
v___x_1120_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_1111_, v_decls_1112_, v___x_1119_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v___x_1120_, 0);
lean_dec(v_unused_1129_);
v___x_1122_ = v___x_1120_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_dec(v___x_1120_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_st_ref_get(v___x_1119_);
lean_dec(v___x_1119_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v___x_1119_);
v_a_1130_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1120_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1120_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues___boxed(lean_object* v_pu_1138_, lean_object* v_decls_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
uint8_t v_pu_boxed_1145_; lean_object* v_res_1146_; 
v_pu_boxed_1145_ = lean_unbox(v_pu_1138_);
v_res_1146_ = l_Lean_Compiler_LCNF_Probe_getLetValues(v_pu_boxed_1145_, v_decls_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec_ref(v_decls_1139_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(uint8_t v_pu_1147_, lean_object* v_code_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
switch(lean_obj_tag(v_code_1148_))
{
case 0:
{
lean_object* v_k_1155_; 
v_k_1155_ = lean_ctor_get(v_code_1148_, 1);
lean_inc_ref(v_k_1155_);
lean_dec_ref(v_code_1148_);
v_code_1148_ = v_k_1155_;
goto _start;
}
case 1:
{
lean_object* v_decl_1157_; lean_object* v_k_1158_; lean_object* v_value_1159_; lean_object* v___x_1160_; 
v_decl_1157_ = lean_ctor_get(v_code_1148_, 0);
lean_inc_ref(v_decl_1157_);
v_k_1158_ = lean_ctor_get(v_code_1148_, 1);
lean_inc_ref(v_k_1158_);
lean_dec_ref(v_code_1148_);
v_value_1159_ = lean_ctor_get(v_decl_1157_, 4);
lean_inc_ref(v_value_1159_);
lean_dec_ref(v_decl_1157_);
v___x_1160_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1147_, v_value_1159_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_dec_ref(v___x_1160_);
v_code_1148_ = v_k_1158_;
goto _start;
}
else
{
lean_dec_ref(v_k_1158_);
return v___x_1160_;
}
}
case 2:
{
lean_object* v_decl_1162_; lean_object* v_k_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_value_1167_; lean_object* v___x_1168_; 
v_decl_1162_ = lean_ctor_get(v_code_1148_, 0);
lean_inc_ref(v_decl_1162_);
v_k_1163_ = lean_ctor_get(v_code_1148_, 1);
lean_inc_ref(v_k_1163_);
lean_dec_ref(v_code_1148_);
v___x_1164_ = lean_st_ref_take(v_a_1149_);
lean_inc_ref(v_decl_1162_);
v___x_1165_ = lean_array_push(v___x_1164_, v_decl_1162_);
v___x_1166_ = lean_st_ref_set(v_a_1149_, v___x_1165_);
v_value_1167_ = lean_ctor_get(v_decl_1162_, 4);
lean_inc_ref(v_value_1167_);
lean_dec_ref(v_decl_1162_);
v___x_1168_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1147_, v_value_1167_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_dec_ref(v___x_1168_);
v_code_1148_ = v_k_1163_;
goto _start;
}
else
{
lean_dec_ref(v_k_1163_);
return v___x_1168_;
}
}
case 4:
{
lean_object* v_cases_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1192_; 
v_cases_1170_ = lean_ctor_get(v_code_1148_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_code_1148_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1172_ = v_code_1148_;
v_isShared_1173_ = v_isSharedCheck_1192_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_cases_1170_);
lean_dec(v_code_1148_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1192_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v_alts_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_alts_1174_ = lean_ctor_get(v_cases_1170_, 3);
lean_inc_ref(v_alts_1174_);
lean_dec_ref(v_cases_1170_);
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_array_get_size(v_alts_1174_);
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_nat_dec_lt(v___x_1175_, v___x_1176_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1180_; 
lean_dec_ref(v_alts_1174_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set_tag(v___x_1172_, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1177_);
v___x_1180_ = v___x_1172_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1177_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
else
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_nat_dec_le(v___x_1176_, v___x_1176_);
if (v___x_1182_ == 0)
{
if (v___x_1178_ == 0)
{
lean_object* v___x_1184_; 
lean_dec_ref(v_alts_1174_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set_tag(v___x_1172_, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1177_);
v___x_1184_ = v___x_1172_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1177_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
else
{
size_t v___x_1186_; size_t v___x_1187_; lean_object* v___x_1188_; 
lean_del_object(v___x_1172_);
v___x_1186_ = ((size_t)0ULL);
v___x_1187_ = lean_usize_of_nat(v___x_1176_);
v___x_1188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1147_, v_alts_1174_, v___x_1186_, v___x_1187_, v___x_1177_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec_ref(v_alts_1174_);
return v___x_1188_;
}
}
else
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
lean_del_object(v___x_1172_);
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = lean_usize_of_nat(v___x_1176_);
v___x_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1147_, v_alts_1174_, v___x_1189_, v___x_1190_, v___x_1177_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec_ref(v_alts_1174_);
return v___x_1191_;
}
}
}
}
case 7:
{
lean_object* v_k_1193_; 
v_k_1193_ = lean_ctor_get(v_code_1148_, 3);
lean_inc_ref(v_k_1193_);
lean_dec_ref(v_code_1148_);
v_code_1148_ = v_k_1193_;
goto _start;
}
case 8:
{
lean_object* v_k_1195_; 
v_k_1195_ = lean_ctor_get(v_code_1148_, 3);
lean_inc_ref(v_k_1195_);
lean_dec_ref(v_code_1148_);
v_code_1148_ = v_k_1195_;
goto _start;
}
case 9:
{
lean_object* v_k_1197_; 
v_k_1197_ = lean_ctor_get(v_code_1148_, 5);
lean_inc_ref(v_k_1197_);
lean_dec_ref(v_code_1148_);
v_code_1148_ = v_k_1197_;
goto _start;
}
case 10:
{
lean_object* v_k_1199_; 
v_k_1199_ = lean_ctor_get(v_code_1148_, 2);
lean_inc_ref(v_k_1199_);
lean_dec_ref(v_code_1148_);
v_code_1148_ = v_k_1199_;
goto _start;
}
case 11:
{
lean_object* v_k_1201_; 
v_k_1201_ = lean_ctor_get(v_code_1148_, 2);
lean_inc_ref(v_k_1201_);
lean_dec_ref(v_code_1148_);
v_code_1148_ = v_k_1201_;
goto _start;
}
case 12:
{
lean_object* v_k_1203_; 
v_k_1203_ = lean_ctor_get(v_code_1148_, 2);
lean_inc_ref(v_k_1203_);
lean_dec_ref(v_code_1148_);
v_code_1148_ = v_k_1203_;
goto _start;
}
case 13:
{
lean_object* v_k_1205_; 
v_k_1205_ = lean_ctor_get(v_code_1148_, 1);
lean_inc_ref(v_k_1205_);
lean_dec_ref(v_code_1148_);
v_code_1148_ = v_k_1205_;
goto _start;
}
default: 
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
lean_dec_ref(v_code_1148_);
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(uint8_t v_pu_1209_, lean_object* v_as_1210_, size_t v_i_1211_, size_t v_stop_1212_, lean_object* v_b_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___y_1221_; uint8_t v___x_1227_; 
v___x_1227_ = lean_usize_dec_eq(v_i_1211_, v_stop_1212_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; 
v___x_1228_ = lean_array_uget_borrowed(v_as_1210_, v_i_1211_);
switch(lean_obj_tag(v___x_1228_))
{
case 0:
{
lean_object* v_code_1229_; 
v_code_1229_ = lean_ctor_get(v___x_1228_, 2);
lean_inc_ref(v_code_1229_);
v___y_1221_ = v_code_1229_;
goto v___jp_1220_;
}
case 1:
{
lean_object* v_code_1230_; 
v_code_1230_ = lean_ctor_get(v___x_1228_, 1);
lean_inc_ref(v_code_1230_);
v___y_1221_ = v_code_1230_;
goto v___jp_1220_;
}
default: 
{
lean_object* v_code_1231_; 
v_code_1231_ = lean_ctor_get(v___x_1228_, 0);
lean_inc_ref(v_code_1231_);
v___y_1221_ = v_code_1231_;
goto v___jp_1220_;
}
}
}
else
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v_b_1213_);
return v___x_1232_;
}
v___jp_1220_:
{
lean_object* v___x_1222_; 
v___x_1222_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1209_, v___y_1221_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; size_t v___x_1224_; size_t v___x_1225_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref(v___x_1222_);
v___x_1224_ = ((size_t)1ULL);
v___x_1225_ = lean_usize_add(v_i_1211_, v___x_1224_);
v_i_1211_ = v___x_1225_;
v_b_1213_ = v_a_1223_;
goto _start;
}
else
{
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0___boxed(lean_object* v_pu_1233_, lean_object* v_as_1234_, lean_object* v_i_1235_, lean_object* v_stop_1236_, lean_object* v_b_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v_pu_boxed_1244_; size_t v_i_boxed_1245_; size_t v_stop_boxed_1246_; lean_object* v_res_1247_; 
v_pu_boxed_1244_ = lean_unbox(v_pu_1233_);
v_i_boxed_1245_ = lean_unbox_usize(v_i_1235_);
lean_dec(v_i_1235_);
v_stop_boxed_1246_ = lean_unbox_usize(v_stop_1236_);
lean_dec(v_stop_1236_);
v_res_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_boxed_1244_, v_as_1234_, v_i_boxed_1245_, v_stop_boxed_1246_, v_b_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v_as_1234_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed(lean_object* v_pu_1248_, lean_object* v_code_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
uint8_t v_pu_boxed_1256_; lean_object* v_res_1257_; 
v_pu_boxed_1256_ = lean_unbox(v_pu_1248_);
v_res_1257_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_boxed_1256_, v_code_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(lean_object* v_f_1258_, lean_object* v_v_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
if (lean_obj_tag(v_v_1259_) == 0)
{
lean_object* v_code_1266_; lean_object* v___x_1267_; 
v_code_1266_ = lean_ctor_get(v_v_1259_, 0);
lean_inc_ref(v_code_1266_);
lean_dec_ref(v_v_1259_);
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc(v___y_1260_);
v___x_1267_ = lean_apply_7(v_f_1258_, v_code_1266_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, lean_box(0));
return v___x_1267_;
}
else
{
lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_f_1258_);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_v_1259_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v_v_1259_, 0);
lean_dec(v_unused_1276_);
v___x_1269_ = v_v_1259_;
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v_v_1259_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_box(0);
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1271_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg___boxed(lean_object* v_f_1277_, lean_object* v_v_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1277_, v_v_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(uint8_t v_pu_1286_, lean_object* v_f_1287_, lean_object* v_v_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1287_, v_v_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___boxed(lean_object* v_pu_1296_, lean_object* v_f_1297_, lean_object* v_v_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v_pu_boxed_1305_; lean_object* v_res_1306_; 
v_pu_boxed_1305_ = lean_unbox(v_pu_1296_);
v_res_1306_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(v_pu_boxed_1305_, v_f_1297_, v_v_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(uint8_t v_pu_1307_, lean_object* v_as_1308_, size_t v_i_1309_, size_t v_stop_1310_, lean_object* v_b_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_usize_dec_eq(v_i_1309_, v_stop_1310_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; lean_object* v_value_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1319_ = lean_array_uget_borrowed(v_as_1308_, v_i_1309_);
v_value_1320_ = lean_ctor_get(v___x_1319_, 1);
v___x_1321_ = lean_box(v_pu_1307_);
v___x_1322_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed), 8, 1);
lean_closure_set(v___x_1322_, 0, v___x_1321_);
lean_inc_ref(v_value_1320_);
v___x_1323_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v___x_1322_, v_value_1320_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; size_t v___x_1325_; size_t v___x_1326_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = ((size_t)1ULL);
v___x_1326_ = lean_usize_add(v_i_1309_, v___x_1325_);
v_i_1309_ = v___x_1326_;
v_b_1311_ = v_a_1324_;
goto _start;
}
else
{
return v___x_1323_;
}
}
else
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_b_1311_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1___boxed(lean_object* v_pu_1329_, lean_object* v_as_1330_, lean_object* v_i_1331_, lean_object* v_stop_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v_pu_boxed_1340_; size_t v_i_boxed_1341_; size_t v_stop_boxed_1342_; lean_object* v_res_1343_; 
v_pu_boxed_1340_ = lean_unbox(v_pu_1329_);
v_i_boxed_1341_ = lean_unbox_usize(v_i_1331_);
lean_dec(v_i_1331_);
v_stop_boxed_1342_ = lean_unbox_usize(v_stop_1332_);
lean_dec(v_stop_1332_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_boxed_1340_, v_as_1330_, v_i_boxed_1341_, v_stop_boxed_1342_, v_b_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v_as_1330_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(uint8_t v_pu_1344_, lean_object* v_decls_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = lean_array_get_size(v_decls_1345_);
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_nat_dec_lt(v___x_1352_, v___x_1353_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
return v___x_1356_;
}
else
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_nat_dec_le(v___x_1353_, v___x_1353_);
if (v___x_1357_ == 0)
{
if (v___x_1355_ == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1354_);
return v___x_1358_;
}
else
{
size_t v___x_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = lean_usize_of_nat(v___x_1353_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1344_, v_decls_1345_, v___x_1359_, v___x_1360_, v___x_1354_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
return v___x_1361_;
}
}
else
{
size_t v___x_1362_; size_t v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = lean_usize_of_nat(v___x_1353_);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1344_, v_decls_1345_, v___x_1362_, v___x_1363_, v___x_1354_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start___boxed(lean_object* v_pu_1365_, lean_object* v_decls_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
uint8_t v_pu_boxed_1373_; lean_object* v_res_1374_; 
v_pu_boxed_1373_ = lean_unbox(v_pu_1365_);
v_res_1374_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_boxed_1373_, v_decls_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_decls_1366_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps(uint8_t v_pu_1377_, lean_object* v_decls_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getJps___closed__0));
v___x_1385_ = lean_st_mk_ref(v___x_1384_);
v___x_1386_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_1377_, v_decls_1378_, v___x_1385_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1394_; 
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v___x_1386_, 0);
lean_dec(v_unused_1395_);
v___x_1388_ = v___x_1386_;
v_isShared_1389_ = v_isSharedCheck_1394_;
goto v_resetjp_1387_;
}
else
{
lean_dec(v___x_1386_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1394_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1390_ = lean_st_ref_get(v___x_1385_);
lean_dec(v___x_1385_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1390_);
v___x_1392_ = v___x_1388_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v___x_1385_);
v_a_1396_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1386_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1386_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps___boxed(lean_object* v_pu_1404_, lean_object* v_decls_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
uint8_t v_pu_boxed_1411_; lean_object* v_res_1412_; 
v_pu_boxed_1411_ = lean_unbox(v_pu_1404_);
v_res_1412_ = l_Lean_Compiler_LCNF_Probe_getJps(v_pu_boxed_1411_, v_decls_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec_ref(v_decls_1405_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(uint8_t v_pu_1413_, lean_object* v_f_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
switch(lean_obj_tag(v_a_1415_))
{
case 0:
{
lean_object* v_decl_1421_; lean_object* v_k_1422_; lean_object* v___x_1423_; 
v_decl_1421_ = lean_ctor_get(v_a_1415_, 0);
lean_inc_ref(v_decl_1421_);
v_k_1422_ = lean_ctor_get(v_a_1415_, 1);
lean_inc_ref(v_k_1422_);
lean_dec_ref(v_a_1415_);
lean_inc_ref(v_f_1414_);
lean_inc(v_a_1419_);
lean_inc_ref(v_a_1418_);
lean_inc(v_a_1417_);
lean_inc_ref(v_a_1416_);
v___x_1423_ = lean_apply_6(v_f_1414_, v_decl_1421_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, lean_box(0));
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; uint8_t v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
v___x_1425_ = lean_unbox(v_a_1424_);
lean_dec(v_a_1424_);
if (v___x_1425_ == 0)
{
lean_dec_ref(v___x_1423_);
v_a_1415_ = v_k_1422_;
goto _start;
}
else
{
lean_dec_ref(v_k_1422_);
lean_dec_ref(v_f_1414_);
return v___x_1423_;
}
}
else
{
lean_dec_ref(v_k_1422_);
lean_dec_ref(v_f_1414_);
return v___x_1423_;
}
}
case 1:
{
lean_object* v_decl_1427_; lean_object* v_k_1428_; lean_object* v_value_1429_; lean_object* v___x_1430_; 
v_decl_1427_ = lean_ctor_get(v_a_1415_, 0);
lean_inc_ref(v_decl_1427_);
v_k_1428_ = lean_ctor_get(v_a_1415_, 1);
lean_inc_ref(v_k_1428_);
lean_dec_ref(v_a_1415_);
v_value_1429_ = lean_ctor_get(v_decl_1427_, 4);
lean_inc_ref(v_value_1429_);
lean_dec_ref(v_decl_1427_);
lean_inc_ref(v_f_1414_);
v___x_1430_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1413_, v_f_1414_, v_value_1429_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; uint8_t v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
v___x_1432_ = lean_unbox(v_a_1431_);
lean_dec(v_a_1431_);
if (v___x_1432_ == 0)
{
lean_dec_ref(v___x_1430_);
v_a_1415_ = v_k_1428_;
goto _start;
}
else
{
lean_dec_ref(v_k_1428_);
lean_dec_ref(v_f_1414_);
return v___x_1430_;
}
}
else
{
lean_dec_ref(v_k_1428_);
lean_dec_ref(v_f_1414_);
return v___x_1430_;
}
}
case 2:
{
lean_object* v_decl_1434_; lean_object* v_k_1435_; lean_object* v_value_1436_; lean_object* v___x_1437_; 
v_decl_1434_ = lean_ctor_get(v_a_1415_, 0);
lean_inc_ref(v_decl_1434_);
v_k_1435_ = lean_ctor_get(v_a_1415_, 1);
lean_inc_ref(v_k_1435_);
lean_dec_ref(v_a_1415_);
v_value_1436_ = lean_ctor_get(v_decl_1434_, 4);
lean_inc_ref(v_value_1436_);
lean_dec_ref(v_decl_1434_);
lean_inc_ref(v_f_1414_);
v___x_1437_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1413_, v_f_1414_, v_value_1436_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; uint8_t v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
v___x_1439_ = lean_unbox(v_a_1438_);
lean_dec(v_a_1438_);
if (v___x_1439_ == 0)
{
lean_dec_ref(v___x_1437_);
v_a_1415_ = v_k_1435_;
goto _start;
}
else
{
lean_dec_ref(v_k_1435_);
lean_dec_ref(v_f_1414_);
return v___x_1437_;
}
}
else
{
lean_dec_ref(v_k_1435_);
lean_dec_ref(v_f_1414_);
return v___x_1437_;
}
}
case 4:
{
lean_object* v_cases_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1460_; 
v_cases_1441_ = lean_ctor_get(v_a_1415_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_a_1415_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1443_ = v_a_1415_;
v_isShared_1444_ = v_isSharedCheck_1460_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_cases_1441_);
lean_dec(v_a_1415_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1460_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v_alts_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_alts_1445_ = lean_ctor_get(v_cases_1441_, 3);
lean_inc_ref(v_alts_1445_);
lean_dec_ref(v_cases_1441_);
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = lean_array_get_size(v_alts_1445_);
v___x_1448_ = lean_nat_dec_lt(v___x_1446_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_dec_ref(v_alts_1445_);
lean_dec_ref(v_f_1414_);
v___x_1449_ = lean_box(v___x_1448_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set_tag(v___x_1443_, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1449_);
v___x_1451_ = v___x_1443_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
else
{
if (v___x_1448_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1455_; 
lean_dec_ref(v_alts_1445_);
lean_dec_ref(v_f_1414_);
v___x_1453_ = lean_box(v___x_1448_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set_tag(v___x_1443_, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1453_);
v___x_1455_ = v___x_1443_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
else
{
size_t v___x_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
lean_del_object(v___x_1443_);
v___x_1457_ = ((size_t)0ULL);
v___x_1458_ = lean_usize_of_nat(v___x_1447_);
v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_1413_, v_f_1414_, v_alts_1445_, v___x_1457_, v___x_1458_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
lean_dec_ref(v_alts_1445_);
return v___x_1459_;
}
}
}
}
case 7:
{
lean_object* v_k_1461_; 
v_k_1461_ = lean_ctor_get(v_a_1415_, 3);
lean_inc_ref(v_k_1461_);
lean_dec_ref(v_a_1415_);
v_a_1415_ = v_k_1461_;
goto _start;
}
case 8:
{
lean_object* v_k_1463_; 
v_k_1463_ = lean_ctor_get(v_a_1415_, 3);
lean_inc_ref(v_k_1463_);
lean_dec_ref(v_a_1415_);
v_a_1415_ = v_k_1463_;
goto _start;
}
case 9:
{
lean_object* v_k_1465_; 
v_k_1465_ = lean_ctor_get(v_a_1415_, 5);
lean_inc_ref(v_k_1465_);
lean_dec_ref(v_a_1415_);
v_a_1415_ = v_k_1465_;
goto _start;
}
case 10:
{
lean_object* v_k_1467_; 
v_k_1467_ = lean_ctor_get(v_a_1415_, 2);
lean_inc_ref(v_k_1467_);
lean_dec_ref(v_a_1415_);
v_a_1415_ = v_k_1467_;
goto _start;
}
case 11:
{
lean_object* v_k_1469_; 
v_k_1469_ = lean_ctor_get(v_a_1415_, 2);
lean_inc_ref(v_k_1469_);
lean_dec_ref(v_a_1415_);
v_a_1415_ = v_k_1469_;
goto _start;
}
case 12:
{
lean_object* v_k_1471_; 
v_k_1471_ = lean_ctor_get(v_a_1415_, 2);
lean_inc_ref(v_k_1471_);
lean_dec_ref(v_a_1415_);
v_a_1415_ = v_k_1471_;
goto _start;
}
case 13:
{
lean_object* v_k_1473_; 
v_k_1473_ = lean_ctor_get(v_a_1415_, 1);
lean_inc_ref(v_k_1473_);
lean_dec_ref(v_a_1415_);
v_a_1415_ = v_k_1473_;
goto _start;
}
default: 
{
uint8_t v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_dec_ref(v_a_1415_);
lean_dec_ref(v_f_1414_);
v___x_1475_ = 0;
v___x_1476_ = lean_box(v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(uint8_t v_pu_1478_, lean_object* v_f_1479_, lean_object* v_as_1480_, size_t v_i_1481_, size_t v_stop_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_usize_dec_eq(v_i_1481_, v_stop_1482_);
if (v___x_1488_ == 0)
{
uint8_t v___x_1489_; lean_object* v___y_1491_; lean_object* v___x_1506_; 
v___x_1489_ = 1;
v___x_1506_ = lean_array_uget_borrowed(v_as_1480_, v_i_1481_);
switch(lean_obj_tag(v___x_1506_))
{
case 0:
{
lean_object* v_code_1507_; 
v_code_1507_ = lean_ctor_get(v___x_1506_, 2);
lean_inc_ref(v_code_1507_);
v___y_1491_ = v_code_1507_;
goto v___jp_1490_;
}
case 1:
{
lean_object* v_code_1508_; 
v_code_1508_ = lean_ctor_get(v___x_1506_, 1);
lean_inc_ref(v_code_1508_);
v___y_1491_ = v_code_1508_;
goto v___jp_1490_;
}
default: 
{
lean_object* v_code_1509_; 
v_code_1509_ = lean_ctor_get(v___x_1506_, 0);
lean_inc_ref(v_code_1509_);
v___y_1491_ = v_code_1509_;
goto v___jp_1490_;
}
}
v___jp_1490_:
{
lean_object* v___x_1492_; 
lean_inc_ref(v_f_1479_);
v___x_1492_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1478_, v_f_1479_, v___y_1491_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1505_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1505_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1505_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_unbox(v_a_1493_);
lean_dec(v_a_1493_);
if (v___x_1497_ == 0)
{
size_t v___x_1498_; size_t v___x_1499_; 
lean_del_object(v___x_1495_);
v___x_1498_ = ((size_t)1ULL);
v___x_1499_ = lean_usize_add(v_i_1481_, v___x_1498_);
v_i_1481_ = v___x_1499_;
goto _start;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_dec_ref(v_f_1479_);
v___x_1501_ = lean_box(v___x_1489_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1501_);
v___x_1503_ = v___x_1495_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_dec_ref(v_f_1479_);
return v___x_1492_;
}
}
}
else
{
uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec_ref(v_f_1479_);
v___x_1510_ = 0;
v___x_1511_ = lean_box(v___x_1510_);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0___boxed(lean_object* v_pu_1513_, lean_object* v_f_1514_, lean_object* v_as_1515_, lean_object* v_i_1516_, lean_object* v_stop_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v_pu_boxed_1523_; size_t v_i_boxed_1524_; size_t v_stop_boxed_1525_; lean_object* v_res_1526_; 
v_pu_boxed_1523_ = lean_unbox(v_pu_1513_);
v_i_boxed_1524_ = lean_unbox_usize(v_i_1516_);
lean_dec(v_i_1516_);
v_stop_boxed_1525_ = lean_unbox_usize(v_stop_1517_);
lean_dec(v_stop_1517_);
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_boxed_1523_, v_f_1514_, v_as_1515_, v_i_boxed_1524_, v_stop_boxed_1525_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec_ref(v_as_1515_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed(lean_object* v_pu_1527_, lean_object* v_f_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
uint8_t v_pu_boxed_1535_; lean_object* v_res_1536_; 
v_pu_boxed_1535_ = lean_unbox(v_pu_1527_);
v_res_1536_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_boxed_1535_, v_f_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(lean_object* v_v_1537_, lean_object* v_f_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
if (lean_obj_tag(v_v_1537_) == 0)
{
lean_object* v_code_1544_; lean_object* v___x_1545_; 
v_code_1544_ = lean_ctor_get(v_v_1537_, 0);
lean_inc_ref(v_code_1544_);
lean_dec_ref(v_v_1537_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
v___x_1545_ = lean_apply_6(v_f_1538_, v_code_1544_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, lean_box(0));
return v___x_1545_;
}
else
{
lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v_f_1538_);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_v_1537_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v_v_1537_, 0);
lean_dec(v_unused_1555_);
v___x_1547_ = v_v_1537_;
v_isShared_1548_ = v_isSharedCheck_1554_;
goto v_resetjp_1546_;
}
else
{
lean_dec(v_v_1537_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1554_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1549_ = 0;
v___x_1550_ = lean_box(v___x_1549_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1550_);
v___x_1552_ = v___x_1547_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg___boxed(lean_object* v_v_1556_, lean_object* v_f_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1556_, v_f_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(uint8_t v_pu_1564_, lean_object* v_v_1565_, lean_object* v_f_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1565_, v_f_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___boxed(lean_object* v_pu_1573_, lean_object* v_v_1574_, lean_object* v_f_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v_pu_boxed_1581_; lean_object* v_res_1582_; 
v_pu_boxed_1581_ = lean_unbox(v_pu_1573_);
v_res_1582_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(v_pu_boxed_1581_, v_v_1574_, v_f_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(uint8_t v_pu_1583_, lean_object* v_f_1584_, lean_object* v_as_1585_, size_t v_i_1586_, size_t v_stop_1587_, lean_object* v_b_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_usize_dec_eq(v_i_1586_, v_stop_1587_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v_value_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1595_ = lean_array_uget_borrowed(v_as_1585_, v_i_1586_);
v_value_1596_ = lean_ctor_get(v___x_1595_, 1);
v___x_1597_ = lean_box(v_pu_1583_);
lean_inc_ref(v_f_1584_);
v___x_1598_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed), 8, 2);
lean_closure_set(v___x_1598_, 0, v___x_1597_);
lean_closure_set(v___x_1598_, 1, v_f_1584_);
lean_inc_ref(v_value_1596_);
v___x_1599_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1596_, v___x_1598_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v_a_1602_; uint8_t v___x_1606_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref(v___x_1599_);
v___x_1606_ = lean_unbox(v_a_1600_);
lean_dec(v_a_1600_);
if (v___x_1606_ == 0)
{
v_a_1602_ = v_b_1588_;
goto v___jp_1601_;
}
else
{
lean_object* v___x_1607_; 
lean_inc(v___x_1595_);
v___x_1607_ = lean_array_push(v_b_1588_, v___x_1595_);
v_a_1602_ = v___x_1607_;
goto v___jp_1601_;
}
v___jp_1601_:
{
size_t v___x_1603_; size_t v___x_1604_; 
v___x_1603_ = ((size_t)1ULL);
v___x_1604_ = lean_usize_add(v_i_1586_, v___x_1603_);
v_i_1586_ = v___x_1604_;
v_b_1588_ = v_a_1602_;
goto _start;
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec_ref(v_b_1588_);
lean_dec_ref(v_f_1584_);
v_a_1608_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1599_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1599_);
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
lean_object* v___x_1616_; 
lean_dec_ref(v_f_1584_);
v___x_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1616_, 0, v_b_1588_);
return v___x_1616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1___boxed(lean_object* v_pu_1617_, lean_object* v_f_1618_, lean_object* v_as_1619_, lean_object* v_i_1620_, lean_object* v_stop_1621_, lean_object* v_b_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
uint8_t v_pu_boxed_1628_; size_t v_i_boxed_1629_; size_t v_stop_boxed_1630_; lean_object* v_res_1631_; 
v_pu_boxed_1628_ = lean_unbox(v_pu_1617_);
v_i_boxed_1629_ = lean_unbox_usize(v_i_1620_);
lean_dec(v_i_1620_);
v_stop_boxed_1630_ = lean_unbox_usize(v_stop_1621_);
lean_dec(v_stop_1621_);
v_res_1631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_boxed_1628_, v_f_1618_, v_as_1619_, v_i_boxed_1629_, v_stop_boxed_1630_, v_b_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec_ref(v_as_1619_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet(uint8_t v_pu_1634_, lean_object* v_f_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1642_ = lean_unsigned_to_nat(0u);
v___x_1643_ = lean_array_get_size(v_a_1636_);
v___x_1644_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1645_ = lean_nat_dec_lt(v___x_1642_, v___x_1643_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref(v_f_1635_);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
return v___x_1646_;
}
else
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_nat_dec_le(v___x_1643_, v___x_1643_);
if (v___x_1647_ == 0)
{
if (v___x_1645_ == 0)
{
lean_object* v___x_1648_; 
lean_dec_ref(v_f_1635_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1644_);
return v___x_1648_;
}
else
{
size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = ((size_t)0ULL);
v___x_1650_ = lean_usize_of_nat(v___x_1643_);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1634_, v_f_1635_, v_a_1636_, v___x_1649_, v___x_1650_, v___x_1644_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1651_;
}
}
else
{
size_t v___x_1652_; size_t v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = ((size_t)0ULL);
v___x_1653_ = lean_usize_of_nat(v___x_1643_);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1634_, v_f_1635_, v_a_1636_, v___x_1652_, v___x_1653_, v___x_1644_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet___boxed(lean_object* v_pu_1655_, lean_object* v_f_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
uint8_t v_pu_boxed_1663_; lean_object* v_res_1664_; 
v_pu_boxed_1663_ = lean_unbox(v_pu_1655_);
v_res_1664_ = l_Lean_Compiler_LCNF_Probe_filterByLet(v_pu_boxed_1663_, v_f_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(uint8_t v_pu_1665_, lean_object* v_f_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
switch(lean_obj_tag(v_a_1667_))
{
case 0:
{
lean_object* v_k_1673_; 
v_k_1673_ = lean_ctor_get(v_a_1667_, 1);
lean_inc_ref(v_k_1673_);
lean_dec_ref(v_a_1667_);
v_a_1667_ = v_k_1673_;
goto _start;
}
case 1:
{
lean_object* v_decl_1675_; lean_object* v_k_1676_; lean_object* v___x_1677_; 
v_decl_1675_ = lean_ctor_get(v_a_1667_, 0);
lean_inc_ref(v_decl_1675_);
v_k_1676_ = lean_ctor_get(v_a_1667_, 1);
lean_inc_ref(v_k_1676_);
lean_dec_ref(v_a_1667_);
lean_inc_ref(v_f_1666_);
lean_inc(v_a_1671_);
lean_inc_ref(v_a_1670_);
lean_inc(v_a_1669_);
lean_inc_ref(v_a_1668_);
lean_inc_ref(v_decl_1675_);
v___x_1677_ = lean_apply_6(v_f_1666_, v_decl_1675_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, lean_box(0));
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; uint8_t v___x_1679_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
v___x_1679_ = lean_unbox(v_a_1678_);
lean_dec(v_a_1678_);
if (v___x_1679_ == 0)
{
lean_object* v_value_1680_; lean_object* v___x_1681_; 
lean_dec_ref(v___x_1677_);
v_value_1680_ = lean_ctor_get(v_decl_1675_, 4);
lean_inc_ref(v_value_1680_);
lean_dec_ref(v_decl_1675_);
lean_inc_ref(v_f_1666_);
v___x_1681_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1665_, v_f_1666_, v_value_1680_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; uint8_t v___x_1683_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
v___x_1683_ = lean_unbox(v_a_1682_);
lean_dec(v_a_1682_);
if (v___x_1683_ == 0)
{
lean_dec_ref(v___x_1681_);
v_a_1667_ = v_k_1676_;
goto _start;
}
else
{
lean_dec_ref(v_k_1676_);
lean_dec_ref(v_f_1666_);
return v___x_1681_;
}
}
else
{
lean_dec_ref(v_k_1676_);
lean_dec_ref(v_f_1666_);
return v___x_1681_;
}
}
else
{
lean_dec_ref(v_k_1676_);
lean_dec_ref(v_decl_1675_);
lean_dec_ref(v_f_1666_);
return v___x_1677_;
}
}
else
{
lean_dec_ref(v_k_1676_);
lean_dec_ref(v_decl_1675_);
lean_dec_ref(v_f_1666_);
return v___x_1677_;
}
}
case 2:
{
lean_object* v_k_1685_; 
v_k_1685_ = lean_ctor_get(v_a_1667_, 1);
lean_inc_ref(v_k_1685_);
lean_dec_ref(v_a_1667_);
v_a_1667_ = v_k_1685_;
goto _start;
}
case 4:
{
lean_object* v_cases_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1706_; 
v_cases_1687_ = lean_ctor_get(v_a_1667_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_a_1667_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1689_ = v_a_1667_;
v_isShared_1690_ = v_isSharedCheck_1706_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_cases_1687_);
lean_dec(v_a_1667_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1706_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v_alts_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v_alts_1691_ = lean_ctor_get(v_cases_1687_, 3);
lean_inc_ref(v_alts_1691_);
lean_dec_ref(v_cases_1687_);
v___x_1692_ = lean_unsigned_to_nat(0u);
v___x_1693_ = lean_array_get_size(v_alts_1691_);
v___x_1694_ = lean_nat_dec_lt(v___x_1692_, v___x_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
lean_dec_ref(v_alts_1691_);
lean_dec_ref(v_f_1666_);
v___x_1695_ = lean_box(v___x_1694_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1695_);
v___x_1697_ = v___x_1689_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
if (v___x_1694_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_dec_ref(v_alts_1691_);
lean_dec_ref(v_f_1666_);
v___x_1699_ = lean_box(v___x_1694_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set_tag(v___x_1689_, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1699_);
v___x_1701_ = v___x_1689_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
else
{
size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
lean_del_object(v___x_1689_);
v___x_1703_ = ((size_t)0ULL);
v___x_1704_ = lean_usize_of_nat(v___x_1693_);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_1665_, v_f_1666_, v_alts_1691_, v___x_1703_, v___x_1704_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
lean_dec_ref(v_alts_1691_);
return v___x_1705_;
}
}
}
}
case 7:
{
lean_object* v_k_1707_; 
v_k_1707_ = lean_ctor_get(v_a_1667_, 3);
lean_inc_ref(v_k_1707_);
lean_dec_ref(v_a_1667_);
v_a_1667_ = v_k_1707_;
goto _start;
}
case 8:
{
lean_object* v_k_1709_; 
v_k_1709_ = lean_ctor_get(v_a_1667_, 3);
lean_inc_ref(v_k_1709_);
lean_dec_ref(v_a_1667_);
v_a_1667_ = v_k_1709_;
goto _start;
}
case 9:
{
lean_object* v_k_1711_; 
v_k_1711_ = lean_ctor_get(v_a_1667_, 5);
lean_inc_ref(v_k_1711_);
lean_dec_ref(v_a_1667_);
v_a_1667_ = v_k_1711_;
goto _start;
}
case 10:
{
lean_object* v_k_1713_; 
v_k_1713_ = lean_ctor_get(v_a_1667_, 2);
lean_inc_ref(v_k_1713_);
lean_dec_ref(v_a_1667_);
v_a_1667_ = v_k_1713_;
goto _start;
}
case 11:
{
lean_object* v_k_1715_; 
v_k_1715_ = lean_ctor_get(v_a_1667_, 2);
lean_inc_ref(v_k_1715_);
lean_dec_ref(v_a_1667_);
v_a_1667_ = v_k_1715_;
goto _start;
}
case 12:
{
lean_object* v_k_1717_; 
v_k_1717_ = lean_ctor_get(v_a_1667_, 2);
lean_inc_ref(v_k_1717_);
lean_dec_ref(v_a_1667_);
v_a_1667_ = v_k_1717_;
goto _start;
}
case 13:
{
lean_object* v_k_1719_; 
v_k_1719_ = lean_ctor_get(v_a_1667_, 1);
lean_inc_ref(v_k_1719_);
lean_dec_ref(v_a_1667_);
v_a_1667_ = v_k_1719_;
goto _start;
}
default: 
{
uint8_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec_ref(v_a_1667_);
lean_dec_ref(v_f_1666_);
v___x_1721_ = 0;
v___x_1722_ = lean_box(v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(uint8_t v_pu_1724_, lean_object* v_f_1725_, lean_object* v_as_1726_, size_t v_i_1727_, size_t v_stop_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_usize_dec_eq(v_i_1727_, v_stop_1728_);
if (v___x_1734_ == 0)
{
uint8_t v___x_1735_; lean_object* v___y_1737_; lean_object* v___x_1752_; 
v___x_1735_ = 1;
v___x_1752_ = lean_array_uget_borrowed(v_as_1726_, v_i_1727_);
switch(lean_obj_tag(v___x_1752_))
{
case 0:
{
lean_object* v_code_1753_; 
v_code_1753_ = lean_ctor_get(v___x_1752_, 2);
lean_inc_ref(v_code_1753_);
v___y_1737_ = v_code_1753_;
goto v___jp_1736_;
}
case 1:
{
lean_object* v_code_1754_; 
v_code_1754_ = lean_ctor_get(v___x_1752_, 1);
lean_inc_ref(v_code_1754_);
v___y_1737_ = v_code_1754_;
goto v___jp_1736_;
}
default: 
{
lean_object* v_code_1755_; 
v_code_1755_ = lean_ctor_get(v___x_1752_, 0);
lean_inc_ref(v_code_1755_);
v___y_1737_ = v_code_1755_;
goto v___jp_1736_;
}
}
v___jp_1736_:
{
lean_object* v___x_1738_; 
lean_inc_ref(v_f_1725_);
v___x_1738_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1724_, v_f_1725_, v___y_1737_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1751_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1751_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1751_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_unbox(v_a_1739_);
lean_dec(v_a_1739_);
if (v___x_1743_ == 0)
{
size_t v___x_1744_; size_t v___x_1745_; 
lean_del_object(v___x_1741_);
v___x_1744_ = ((size_t)1ULL);
v___x_1745_ = lean_usize_add(v_i_1727_, v___x_1744_);
v_i_1727_ = v___x_1745_;
goto _start;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec_ref(v_f_1725_);
v___x_1747_ = lean_box(v___x_1735_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1747_);
v___x_1749_ = v___x_1741_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
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
else
{
lean_dec_ref(v_f_1725_);
return v___x_1738_;
}
}
}
else
{
uint8_t v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec_ref(v_f_1725_);
v___x_1756_ = 0;
v___x_1757_ = lean_box(v___x_1756_);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0___boxed(lean_object* v_pu_1759_, lean_object* v_f_1760_, lean_object* v_as_1761_, lean_object* v_i_1762_, lean_object* v_stop_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v_pu_boxed_1769_; size_t v_i_boxed_1770_; size_t v_stop_boxed_1771_; lean_object* v_res_1772_; 
v_pu_boxed_1769_ = lean_unbox(v_pu_1759_);
v_i_boxed_1770_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_stop_boxed_1771_ = lean_unbox_usize(v_stop_1763_);
lean_dec(v_stop_1763_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_boxed_1769_, v_f_1760_, v_as_1761_, v_i_boxed_1770_, v_stop_boxed_1771_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec_ref(v_as_1761_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed(lean_object* v_pu_1773_, lean_object* v_f_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
uint8_t v_pu_boxed_1781_; lean_object* v_res_1782_; 
v_pu_boxed_1781_ = lean_unbox(v_pu_1773_);
v_res_1782_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_boxed_1781_, v_f_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(uint8_t v_pu_1783_, lean_object* v_f_1784_, lean_object* v_as_1785_, size_t v_i_1786_, size_t v_stop_1787_, lean_object* v_b_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_usize_dec_eq(v_i_1786_, v_stop_1787_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v_value_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1795_ = lean_array_uget_borrowed(v_as_1785_, v_i_1786_);
v_value_1796_ = lean_ctor_get(v___x_1795_, 1);
v___x_1797_ = lean_box(v_pu_1783_);
lean_inc_ref(v_f_1784_);
v___x_1798_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed), 8, 2);
lean_closure_set(v___x_1798_, 0, v___x_1797_);
lean_closure_set(v___x_1798_, 1, v_f_1784_);
lean_inc_ref(v_value_1796_);
v___x_1799_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1796_, v___x_1798_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v_a_1802_; uint8_t v___x_1806_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref(v___x_1799_);
v___x_1806_ = lean_unbox(v_a_1800_);
lean_dec(v_a_1800_);
if (v___x_1806_ == 0)
{
v_a_1802_ = v_b_1788_;
goto v___jp_1801_;
}
else
{
lean_object* v___x_1807_; 
lean_inc(v___x_1795_);
v___x_1807_ = lean_array_push(v_b_1788_, v___x_1795_);
v_a_1802_ = v___x_1807_;
goto v___jp_1801_;
}
v___jp_1801_:
{
size_t v___x_1803_; size_t v___x_1804_; 
v___x_1803_ = ((size_t)1ULL);
v___x_1804_ = lean_usize_add(v_i_1786_, v___x_1803_);
v_i_1786_ = v___x_1804_;
v_b_1788_ = v_a_1802_;
goto _start;
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v_b_1788_);
lean_dec_ref(v_f_1784_);
v_a_1808_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1799_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1799_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v___x_1816_; 
lean_dec_ref(v_f_1784_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v_b_1788_);
return v___x_1816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0___boxed(lean_object* v_pu_1817_, lean_object* v_f_1818_, lean_object* v_as_1819_, lean_object* v_i_1820_, lean_object* v_stop_1821_, lean_object* v_b_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
uint8_t v_pu_boxed_1828_; size_t v_i_boxed_1829_; size_t v_stop_boxed_1830_; lean_object* v_res_1831_; 
v_pu_boxed_1828_ = lean_unbox(v_pu_1817_);
v_i_boxed_1829_ = lean_unbox_usize(v_i_1820_);
lean_dec(v_i_1820_);
v_stop_boxed_1830_ = lean_unbox_usize(v_stop_1821_);
lean_dec(v_stop_1821_);
v_res_1831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_boxed_1828_, v_f_1818_, v_as_1819_, v_i_boxed_1829_, v_stop_boxed_1830_, v_b_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec_ref(v_as_1819_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun(uint8_t v_pu_1832_, lean_object* v_f_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = lean_array_get_size(v_a_1834_);
v___x_1842_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1843_ = lean_nat_dec_lt(v___x_1840_, v___x_1841_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
lean_dec_ref(v_f_1833_);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
return v___x_1844_;
}
else
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_nat_dec_le(v___x_1841_, v___x_1841_);
if (v___x_1845_ == 0)
{
if (v___x_1843_ == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref(v_f_1833_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1842_);
return v___x_1846_;
}
else
{
size_t v___x_1847_; size_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = ((size_t)0ULL);
v___x_1848_ = lean_usize_of_nat(v___x_1841_);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1832_, v_f_1833_, v_a_1834_, v___x_1847_, v___x_1848_, v___x_1842_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
return v___x_1849_;
}
}
else
{
size_t v___x_1850_; size_t v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = ((size_t)0ULL);
v___x_1851_ = lean_usize_of_nat(v___x_1841_);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1832_, v_f_1833_, v_a_1834_, v___x_1850_, v___x_1851_, v___x_1842_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun___boxed(lean_object* v_pu_1853_, lean_object* v_f_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
uint8_t v_pu_boxed_1861_; lean_object* v_res_1862_; 
v_pu_boxed_1861_ = lean_unbox(v_pu_1853_);
v_res_1862_ = l_Lean_Compiler_LCNF_Probe_filterByFun(v_pu_boxed_1861_, v_f_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec_ref(v_a_1855_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(uint8_t v_pu_1863_, lean_object* v_f_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
switch(lean_obj_tag(v_a_1865_))
{
case 0:
{
lean_object* v_k_1871_; 
v_k_1871_ = lean_ctor_get(v_a_1865_, 1);
lean_inc_ref(v_k_1871_);
lean_dec_ref(v_a_1865_);
v_a_1865_ = v_k_1871_;
goto _start;
}
case 1:
{
lean_object* v_decl_1873_; lean_object* v_k_1874_; lean_object* v_value_1875_; lean_object* v___x_1876_; 
v_decl_1873_ = lean_ctor_get(v_a_1865_, 0);
lean_inc_ref(v_decl_1873_);
v_k_1874_ = lean_ctor_get(v_a_1865_, 1);
lean_inc_ref(v_k_1874_);
lean_dec_ref(v_a_1865_);
v_value_1875_ = lean_ctor_get(v_decl_1873_, 4);
lean_inc_ref(v_value_1875_);
lean_dec_ref(v_decl_1873_);
lean_inc_ref(v_f_1864_);
v___x_1876_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1863_, v_f_1864_, v_value_1875_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; uint8_t v___x_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
v___x_1878_ = lean_unbox(v_a_1877_);
lean_dec(v_a_1877_);
if (v___x_1878_ == 0)
{
lean_dec_ref(v___x_1876_);
v_a_1865_ = v_k_1874_;
goto _start;
}
else
{
lean_dec_ref(v_k_1874_);
lean_dec_ref(v_f_1864_);
return v___x_1876_;
}
}
else
{
lean_dec_ref(v_k_1874_);
lean_dec_ref(v_f_1864_);
return v___x_1876_;
}
}
case 2:
{
lean_object* v_decl_1880_; lean_object* v_k_1881_; lean_object* v___x_1882_; 
v_decl_1880_ = lean_ctor_get(v_a_1865_, 0);
lean_inc_ref(v_decl_1880_);
v_k_1881_ = lean_ctor_get(v_a_1865_, 1);
lean_inc_ref(v_k_1881_);
lean_dec_ref(v_a_1865_);
lean_inc_ref(v_f_1864_);
lean_inc(v_a_1869_);
lean_inc_ref(v_a_1868_);
lean_inc(v_a_1867_);
lean_inc_ref(v_a_1866_);
lean_inc_ref(v_decl_1880_);
v___x_1882_ = lean_apply_6(v_f_1864_, v_decl_1880_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, lean_box(0));
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; uint8_t v___x_1884_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
v___x_1884_ = lean_unbox(v_a_1883_);
lean_dec(v_a_1883_);
if (v___x_1884_ == 0)
{
lean_object* v_value_1885_; lean_object* v___x_1886_; 
lean_dec_ref(v___x_1882_);
v_value_1885_ = lean_ctor_get(v_decl_1880_, 4);
lean_inc_ref(v_value_1885_);
lean_dec_ref(v_decl_1880_);
lean_inc_ref(v_f_1864_);
v___x_1886_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1863_, v_f_1864_, v_value_1885_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; uint8_t v___x_1888_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
v___x_1888_ = lean_unbox(v_a_1887_);
lean_dec(v_a_1887_);
if (v___x_1888_ == 0)
{
lean_dec_ref(v___x_1886_);
v_a_1865_ = v_k_1881_;
goto _start;
}
else
{
lean_dec_ref(v_k_1881_);
lean_dec_ref(v_f_1864_);
return v___x_1886_;
}
}
else
{
lean_dec_ref(v_k_1881_);
lean_dec_ref(v_f_1864_);
return v___x_1886_;
}
}
else
{
lean_dec_ref(v_k_1881_);
lean_dec_ref(v_decl_1880_);
lean_dec_ref(v_f_1864_);
return v___x_1882_;
}
}
else
{
lean_dec_ref(v_k_1881_);
lean_dec_ref(v_decl_1880_);
lean_dec_ref(v_f_1864_);
return v___x_1882_;
}
}
case 4:
{
lean_object* v_cases_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1909_; 
v_cases_1890_ = lean_ctor_get(v_a_1865_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_a_1865_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1892_ = v_a_1865_;
v_isShared_1893_ = v_isSharedCheck_1909_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_cases_1890_);
lean_dec(v_a_1865_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1909_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v_alts_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v_alts_1894_ = lean_ctor_get(v_cases_1890_, 3);
lean_inc_ref(v_alts_1894_);
lean_dec_ref(v_cases_1890_);
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_array_get_size(v_alts_1894_);
v___x_1897_ = lean_nat_dec_lt(v___x_1895_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
lean_dec_ref(v_alts_1894_);
lean_dec_ref(v_f_1864_);
v___x_1898_ = lean_box(v___x_1897_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set_tag(v___x_1892_, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1898_);
v___x_1900_ = v___x_1892_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
else
{
if (v___x_1897_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
lean_dec_ref(v_alts_1894_);
lean_dec_ref(v_f_1864_);
v___x_1902_ = lean_box(v___x_1897_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set_tag(v___x_1892_, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1902_);
v___x_1904_ = v___x_1892_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
else
{
size_t v___x_1906_; size_t v___x_1907_; lean_object* v___x_1908_; 
lean_del_object(v___x_1892_);
v___x_1906_ = ((size_t)0ULL);
v___x_1907_ = lean_usize_of_nat(v___x_1896_);
v___x_1908_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_1863_, v_f_1864_, v_alts_1894_, v___x_1906_, v___x_1907_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
lean_dec_ref(v_alts_1894_);
return v___x_1908_;
}
}
}
}
case 7:
{
lean_object* v_k_1910_; 
v_k_1910_ = lean_ctor_get(v_a_1865_, 3);
lean_inc_ref(v_k_1910_);
lean_dec_ref(v_a_1865_);
v_a_1865_ = v_k_1910_;
goto _start;
}
case 8:
{
lean_object* v_k_1912_; 
v_k_1912_ = lean_ctor_get(v_a_1865_, 3);
lean_inc_ref(v_k_1912_);
lean_dec_ref(v_a_1865_);
v_a_1865_ = v_k_1912_;
goto _start;
}
case 9:
{
lean_object* v_k_1914_; 
v_k_1914_ = lean_ctor_get(v_a_1865_, 5);
lean_inc_ref(v_k_1914_);
lean_dec_ref(v_a_1865_);
v_a_1865_ = v_k_1914_;
goto _start;
}
case 10:
{
lean_object* v_k_1916_; 
v_k_1916_ = lean_ctor_get(v_a_1865_, 2);
lean_inc_ref(v_k_1916_);
lean_dec_ref(v_a_1865_);
v_a_1865_ = v_k_1916_;
goto _start;
}
case 11:
{
lean_object* v_k_1918_; 
v_k_1918_ = lean_ctor_get(v_a_1865_, 2);
lean_inc_ref(v_k_1918_);
lean_dec_ref(v_a_1865_);
v_a_1865_ = v_k_1918_;
goto _start;
}
case 12:
{
lean_object* v_k_1920_; 
v_k_1920_ = lean_ctor_get(v_a_1865_, 2);
lean_inc_ref(v_k_1920_);
lean_dec_ref(v_a_1865_);
v_a_1865_ = v_k_1920_;
goto _start;
}
case 13:
{
lean_object* v_k_1922_; 
v_k_1922_ = lean_ctor_get(v_a_1865_, 1);
lean_inc_ref(v_k_1922_);
lean_dec_ref(v_a_1865_);
v_a_1865_ = v_k_1922_;
goto _start;
}
default: 
{
uint8_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec_ref(v_a_1865_);
lean_dec_ref(v_f_1864_);
v___x_1924_ = 0;
v___x_1925_ = lean_box(v___x_1924_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(uint8_t v_pu_1927_, lean_object* v_f_1928_, lean_object* v_as_1929_, size_t v_i_1930_, size_t v_stop_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
uint8_t v___x_1937_; 
v___x_1937_ = lean_usize_dec_eq(v_i_1930_, v_stop_1931_);
if (v___x_1937_ == 0)
{
uint8_t v___x_1938_; lean_object* v___y_1940_; lean_object* v___x_1955_; 
v___x_1938_ = 1;
v___x_1955_ = lean_array_uget_borrowed(v_as_1929_, v_i_1930_);
switch(lean_obj_tag(v___x_1955_))
{
case 0:
{
lean_object* v_code_1956_; 
v_code_1956_ = lean_ctor_get(v___x_1955_, 2);
lean_inc_ref(v_code_1956_);
v___y_1940_ = v_code_1956_;
goto v___jp_1939_;
}
case 1:
{
lean_object* v_code_1957_; 
v_code_1957_ = lean_ctor_get(v___x_1955_, 1);
lean_inc_ref(v_code_1957_);
v___y_1940_ = v_code_1957_;
goto v___jp_1939_;
}
default: 
{
lean_object* v_code_1958_; 
v_code_1958_ = lean_ctor_get(v___x_1955_, 0);
lean_inc_ref(v_code_1958_);
v___y_1940_ = v_code_1958_;
goto v___jp_1939_;
}
}
v___jp_1939_:
{
lean_object* v___x_1941_; 
lean_inc_ref(v_f_1928_);
v___x_1941_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1927_, v_f_1928_, v___y_1940_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1954_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1944_ = v___x_1941_;
v_isShared_1945_ = v_isSharedCheck_1954_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1954_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_unbox(v_a_1942_);
lean_dec(v_a_1942_);
if (v___x_1946_ == 0)
{
size_t v___x_1947_; size_t v___x_1948_; 
lean_del_object(v___x_1944_);
v___x_1947_ = ((size_t)1ULL);
v___x_1948_ = lean_usize_add(v_i_1930_, v___x_1947_);
v_i_1930_ = v___x_1948_;
goto _start;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
lean_dec_ref(v_f_1928_);
v___x_1950_ = lean_box(v___x_1938_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1950_);
v___x_1952_ = v___x_1944_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_dec_ref(v_f_1928_);
return v___x_1941_;
}
}
}
else
{
uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec_ref(v_f_1928_);
v___x_1959_ = 0;
v___x_1960_ = lean_box(v___x_1959_);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0___boxed(lean_object* v_pu_1962_, lean_object* v_f_1963_, lean_object* v_as_1964_, lean_object* v_i_1965_, lean_object* v_stop_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
uint8_t v_pu_boxed_1972_; size_t v_i_boxed_1973_; size_t v_stop_boxed_1974_; lean_object* v_res_1975_; 
v_pu_boxed_1972_ = lean_unbox(v_pu_1962_);
v_i_boxed_1973_ = lean_unbox_usize(v_i_1965_);
lean_dec(v_i_1965_);
v_stop_boxed_1974_ = lean_unbox_usize(v_stop_1966_);
lean_dec(v_stop_1966_);
v_res_1975_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_boxed_1972_, v_f_1963_, v_as_1964_, v_i_boxed_1973_, v_stop_boxed_1974_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec_ref(v_as_1964_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed(lean_object* v_pu_1976_, lean_object* v_f_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
uint8_t v_pu_boxed_1984_; lean_object* v_res_1985_; 
v_pu_boxed_1984_ = lean_unbox(v_pu_1976_);
v_res_1985_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_boxed_1984_, v_f_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(uint8_t v_pu_1986_, lean_object* v_f_1987_, lean_object* v_as_1988_, size_t v_i_1989_, size_t v_stop_1990_, lean_object* v_b_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
uint8_t v___x_1997_; 
v___x_1997_ = lean_usize_dec_eq(v_i_1989_, v_stop_1990_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v_value_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1998_ = lean_array_uget_borrowed(v_as_1988_, v_i_1989_);
v_value_1999_ = lean_ctor_get(v___x_1998_, 1);
v___x_2000_ = lean_box(v_pu_1986_);
lean_inc_ref(v_f_1987_);
v___x_2001_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed), 8, 2);
lean_closure_set(v___x_2001_, 0, v___x_2000_);
lean_closure_set(v___x_2001_, 1, v_f_1987_);
lean_inc_ref(v_value_1999_);
v___x_2002_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1999_, v___x_2001_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v_a_2005_; uint8_t v___x_2009_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref(v___x_2002_);
v___x_2009_ = lean_unbox(v_a_2003_);
lean_dec(v_a_2003_);
if (v___x_2009_ == 0)
{
v_a_2005_ = v_b_1991_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2010_; 
lean_inc(v___x_1998_);
v___x_2010_ = lean_array_push(v_b_1991_, v___x_1998_);
v_a_2005_ = v___x_2010_;
goto v___jp_2004_;
}
v___jp_2004_:
{
size_t v___x_2006_; size_t v___x_2007_; 
v___x_2006_ = ((size_t)1ULL);
v___x_2007_ = lean_usize_add(v_i_1989_, v___x_2006_);
v_i_1989_ = v___x_2007_;
v_b_1991_ = v_a_2005_;
goto _start;
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref(v_b_1991_);
lean_dec_ref(v_f_1987_);
v_a_2011_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2002_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2002_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v___x_2019_; 
lean_dec_ref(v_f_1987_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_b_1991_);
return v___x_2019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0___boxed(lean_object* v_pu_2020_, lean_object* v_f_2021_, lean_object* v_as_2022_, lean_object* v_i_2023_, lean_object* v_stop_2024_, lean_object* v_b_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
uint8_t v_pu_boxed_2031_; size_t v_i_boxed_2032_; size_t v_stop_boxed_2033_; lean_object* v_res_2034_; 
v_pu_boxed_2031_ = lean_unbox(v_pu_2020_);
v_i_boxed_2032_ = lean_unbox_usize(v_i_2023_);
lean_dec(v_i_2023_);
v_stop_boxed_2033_ = lean_unbox_usize(v_stop_2024_);
lean_dec(v_stop_2024_);
v_res_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_boxed_2031_, v_f_2021_, v_as_2022_, v_i_boxed_2032_, v_stop_boxed_2033_, v_b_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec_ref(v_as_2022_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp(uint8_t v_pu_2035_, lean_object* v_f_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2043_ = lean_unsigned_to_nat(0u);
v___x_2044_ = lean_array_get_size(v_a_2037_);
v___x_2045_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2046_ = lean_nat_dec_lt(v___x_2043_, v___x_2044_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
lean_dec_ref(v_f_2036_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
return v___x_2047_;
}
else
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_nat_dec_le(v___x_2044_, v___x_2044_);
if (v___x_2048_ == 0)
{
if (v___x_2046_ == 0)
{
lean_object* v___x_2049_; 
lean_dec_ref(v_f_2036_);
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2045_);
return v___x_2049_;
}
else
{
size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = lean_usize_of_nat(v___x_2044_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_2035_, v_f_2036_, v_a_2037_, v___x_2050_, v___x_2051_, v___x_2045_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
return v___x_2052_;
}
}
else
{
size_t v___x_2053_; size_t v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = ((size_t)0ULL);
v___x_2054_ = lean_usize_of_nat(v___x_2044_);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_2035_, v_f_2036_, v_a_2037_, v___x_2053_, v___x_2054_, v___x_2045_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
return v___x_2055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp___boxed(lean_object* v_pu_2056_, lean_object* v_f_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
uint8_t v_pu_boxed_2064_; lean_object* v_res_2065_; 
v_pu_boxed_2064_ = lean_unbox(v_pu_2056_);
v_res_2065_ = l_Lean_Compiler_LCNF_Probe_filterByJp(v_pu_boxed_2064_, v_f_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
lean_dec_ref(v_a_2058_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(uint8_t v_pu_2066_, lean_object* v_f_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
switch(lean_obj_tag(v_a_2068_))
{
case 0:
{
lean_object* v_k_2074_; 
v_k_2074_ = lean_ctor_get(v_a_2068_, 1);
lean_inc_ref(v_k_2074_);
lean_dec_ref(v_a_2068_);
v_a_2068_ = v_k_2074_;
goto _start;
}
case 1:
{
lean_object* v_decl_2076_; lean_object* v_k_2077_; lean_object* v___x_2078_; 
v_decl_2076_ = lean_ctor_get(v_a_2068_, 0);
lean_inc_ref(v_decl_2076_);
v_k_2077_ = lean_ctor_get(v_a_2068_, 1);
lean_inc_ref(v_k_2077_);
lean_dec_ref(v_a_2068_);
lean_inc_ref(v_f_2067_);
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
lean_inc_ref(v_decl_2076_);
v___x_2078_ = lean_apply_6(v_f_2067_, v_decl_2076_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, lean_box(0));
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; uint8_t v___x_2080_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
v___x_2080_ = lean_unbox(v_a_2079_);
lean_dec(v_a_2079_);
if (v___x_2080_ == 0)
{
lean_object* v_value_2081_; lean_object* v___x_2082_; 
lean_dec_ref(v___x_2078_);
v_value_2081_ = lean_ctor_get(v_decl_2076_, 4);
lean_inc_ref(v_value_2081_);
lean_dec_ref(v_decl_2076_);
lean_inc_ref(v_f_2067_);
v___x_2082_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2066_, v_f_2067_, v_value_2081_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; uint8_t v___x_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
v___x_2084_ = lean_unbox(v_a_2083_);
lean_dec(v_a_2083_);
if (v___x_2084_ == 0)
{
lean_dec_ref(v___x_2082_);
v_a_2068_ = v_k_2077_;
goto _start;
}
else
{
lean_dec_ref(v_k_2077_);
lean_dec_ref(v_f_2067_);
return v___x_2082_;
}
}
else
{
lean_dec_ref(v_k_2077_);
lean_dec_ref(v_f_2067_);
return v___x_2082_;
}
}
else
{
lean_dec_ref(v_k_2077_);
lean_dec_ref(v_decl_2076_);
lean_dec_ref(v_f_2067_);
return v___x_2078_;
}
}
else
{
lean_dec_ref(v_k_2077_);
lean_dec_ref(v_decl_2076_);
lean_dec_ref(v_f_2067_);
return v___x_2078_;
}
}
case 2:
{
lean_object* v_decl_2086_; lean_object* v_k_2087_; lean_object* v___x_2088_; 
v_decl_2086_ = lean_ctor_get(v_a_2068_, 0);
lean_inc_ref(v_decl_2086_);
v_k_2087_ = lean_ctor_get(v_a_2068_, 1);
lean_inc_ref(v_k_2087_);
lean_dec_ref(v_a_2068_);
lean_inc_ref(v_f_2067_);
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
lean_inc_ref(v_decl_2086_);
v___x_2088_ = lean_apply_6(v_f_2067_, v_decl_2086_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, lean_box(0));
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; uint8_t v___x_2090_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
v___x_2090_ = lean_unbox(v_a_2089_);
lean_dec(v_a_2089_);
if (v___x_2090_ == 0)
{
lean_object* v_value_2091_; lean_object* v___x_2092_; 
lean_dec_ref(v___x_2088_);
v_value_2091_ = lean_ctor_get(v_decl_2086_, 4);
lean_inc_ref(v_value_2091_);
lean_dec_ref(v_decl_2086_);
lean_inc_ref(v_f_2067_);
v___x_2092_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2066_, v_f_2067_, v_value_2091_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; uint8_t v___x_2094_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
v___x_2094_ = lean_unbox(v_a_2093_);
lean_dec(v_a_2093_);
if (v___x_2094_ == 0)
{
lean_dec_ref(v___x_2092_);
v_a_2068_ = v_k_2087_;
goto _start;
}
else
{
lean_dec_ref(v_k_2087_);
lean_dec_ref(v_f_2067_);
return v___x_2092_;
}
}
else
{
lean_dec_ref(v_k_2087_);
lean_dec_ref(v_f_2067_);
return v___x_2092_;
}
}
else
{
lean_dec_ref(v_k_2087_);
lean_dec_ref(v_decl_2086_);
lean_dec_ref(v_f_2067_);
return v___x_2088_;
}
}
else
{
lean_dec_ref(v_k_2087_);
lean_dec_ref(v_decl_2086_);
lean_dec_ref(v_f_2067_);
return v___x_2088_;
}
}
case 4:
{
lean_object* v_cases_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2115_; 
v_cases_2096_ = lean_ctor_get(v_a_2068_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_a_2068_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2098_ = v_a_2068_;
v_isShared_2099_ = v_isSharedCheck_2115_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_cases_2096_);
lean_dec(v_a_2068_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2115_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_alts_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v_alts_2100_ = lean_ctor_get(v_cases_2096_, 3);
lean_inc_ref(v_alts_2100_);
lean_dec_ref(v_cases_2096_);
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = lean_array_get_size(v_alts_2100_);
v___x_2103_ = lean_nat_dec_lt(v___x_2101_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
lean_dec_ref(v_alts_2100_);
lean_dec_ref(v_f_2067_);
v___x_2104_ = lean_box(v___x_2103_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set_tag(v___x_2098_, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2104_);
v___x_2106_ = v___x_2098_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
else
{
if (v___x_2103_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2110_; 
lean_dec_ref(v_alts_2100_);
lean_dec_ref(v_f_2067_);
v___x_2108_ = lean_box(v___x_2103_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set_tag(v___x_2098_, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2108_);
v___x_2110_ = v___x_2098_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
else
{
size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; 
lean_del_object(v___x_2098_);
v___x_2112_ = ((size_t)0ULL);
v___x_2113_ = lean_usize_of_nat(v___x_2102_);
v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_2066_, v_f_2067_, v_alts_2100_, v___x_2112_, v___x_2113_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec_ref(v_alts_2100_);
return v___x_2114_;
}
}
}
}
case 7:
{
lean_object* v_k_2116_; 
v_k_2116_ = lean_ctor_get(v_a_2068_, 3);
lean_inc_ref(v_k_2116_);
lean_dec_ref(v_a_2068_);
v_a_2068_ = v_k_2116_;
goto _start;
}
case 8:
{
lean_object* v_k_2118_; 
v_k_2118_ = lean_ctor_get(v_a_2068_, 3);
lean_inc_ref(v_k_2118_);
lean_dec_ref(v_a_2068_);
v_a_2068_ = v_k_2118_;
goto _start;
}
case 9:
{
lean_object* v_k_2120_; 
v_k_2120_ = lean_ctor_get(v_a_2068_, 5);
lean_inc_ref(v_k_2120_);
lean_dec_ref(v_a_2068_);
v_a_2068_ = v_k_2120_;
goto _start;
}
case 10:
{
lean_object* v_k_2122_; 
v_k_2122_ = lean_ctor_get(v_a_2068_, 2);
lean_inc_ref(v_k_2122_);
lean_dec_ref(v_a_2068_);
v_a_2068_ = v_k_2122_;
goto _start;
}
case 11:
{
lean_object* v_k_2124_; 
v_k_2124_ = lean_ctor_get(v_a_2068_, 2);
lean_inc_ref(v_k_2124_);
lean_dec_ref(v_a_2068_);
v_a_2068_ = v_k_2124_;
goto _start;
}
case 12:
{
lean_object* v_k_2126_; 
v_k_2126_ = lean_ctor_get(v_a_2068_, 2);
lean_inc_ref(v_k_2126_);
lean_dec_ref(v_a_2068_);
v_a_2068_ = v_k_2126_;
goto _start;
}
case 13:
{
lean_object* v_k_2128_; 
v_k_2128_ = lean_ctor_get(v_a_2068_, 1);
lean_inc_ref(v_k_2128_);
lean_dec_ref(v_a_2068_);
v_a_2068_ = v_k_2128_;
goto _start;
}
default: 
{
uint8_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec_ref(v_a_2068_);
lean_dec_ref(v_f_2067_);
v___x_2130_ = 0;
v___x_2131_ = lean_box(v___x_2130_);
v___x_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
return v___x_2132_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(uint8_t v_pu_2133_, lean_object* v_f_2134_, lean_object* v_as_2135_, size_t v_i_2136_, size_t v_stop_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_usize_dec_eq(v_i_2136_, v_stop_2137_);
if (v___x_2143_ == 0)
{
uint8_t v___x_2144_; lean_object* v___y_2146_; lean_object* v___x_2161_; 
v___x_2144_ = 1;
v___x_2161_ = lean_array_uget_borrowed(v_as_2135_, v_i_2136_);
switch(lean_obj_tag(v___x_2161_))
{
case 0:
{
lean_object* v_code_2162_; 
v_code_2162_ = lean_ctor_get(v___x_2161_, 2);
lean_inc_ref(v_code_2162_);
v___y_2146_ = v_code_2162_;
goto v___jp_2145_;
}
case 1:
{
lean_object* v_code_2163_; 
v_code_2163_ = lean_ctor_get(v___x_2161_, 1);
lean_inc_ref(v_code_2163_);
v___y_2146_ = v_code_2163_;
goto v___jp_2145_;
}
default: 
{
lean_object* v_code_2164_; 
v_code_2164_ = lean_ctor_get(v___x_2161_, 0);
lean_inc_ref(v_code_2164_);
v___y_2146_ = v_code_2164_;
goto v___jp_2145_;
}
}
v___jp_2145_:
{
lean_object* v___x_2147_; 
lean_inc_ref(v_f_2134_);
v___x_2147_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2133_, v_f_2134_, v___y_2146_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2160_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2150_ = v___x_2147_;
v_isShared_2151_ = v_isSharedCheck_2160_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2147_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2160_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_unbox(v_a_2148_);
lean_dec(v_a_2148_);
if (v___x_2152_ == 0)
{
size_t v___x_2153_; size_t v___x_2154_; 
lean_del_object(v___x_2150_);
v___x_2153_ = ((size_t)1ULL);
v___x_2154_ = lean_usize_add(v_i_2136_, v___x_2153_);
v_i_2136_ = v___x_2154_;
goto _start;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
lean_dec_ref(v_f_2134_);
v___x_2156_ = lean_box(v___x_2144_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2156_);
v___x_2158_ = v___x_2150_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_dec_ref(v_f_2134_);
return v___x_2147_;
}
}
}
else
{
uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec_ref(v_f_2134_);
v___x_2165_ = 0;
v___x_2166_ = lean_box(v___x_2165_);
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
return v___x_2167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0___boxed(lean_object* v_pu_2168_, lean_object* v_f_2169_, lean_object* v_as_2170_, lean_object* v_i_2171_, lean_object* v_stop_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v_pu_boxed_2178_; size_t v_i_boxed_2179_; size_t v_stop_boxed_2180_; lean_object* v_res_2181_; 
v_pu_boxed_2178_ = lean_unbox(v_pu_2168_);
v_i_boxed_2179_ = lean_unbox_usize(v_i_2171_);
lean_dec(v_i_2171_);
v_stop_boxed_2180_ = lean_unbox_usize(v_stop_2172_);
lean_dec(v_stop_2172_);
v_res_2181_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_boxed_2178_, v_f_2169_, v_as_2170_, v_i_boxed_2179_, v_stop_boxed_2180_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec_ref(v_as_2170_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed(lean_object* v_pu_2182_, lean_object* v_f_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
uint8_t v_pu_boxed_2190_; lean_object* v_res_2191_; 
v_pu_boxed_2190_ = lean_unbox(v_pu_2182_);
v_res_2191_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_boxed_2190_, v_f_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(uint8_t v_pu_2192_, lean_object* v_f_2193_, lean_object* v_as_2194_, size_t v_i_2195_, size_t v_stop_2196_, lean_object* v_b_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
uint8_t v___x_2203_; 
v___x_2203_ = lean_usize_dec_eq(v_i_2195_, v_stop_2196_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; lean_object* v_value_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2204_ = lean_array_uget_borrowed(v_as_2194_, v_i_2195_);
v_value_2205_ = lean_ctor_get(v___x_2204_, 1);
v___x_2206_ = lean_box(v_pu_2192_);
lean_inc_ref(v_f_2193_);
v___x_2207_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed), 8, 2);
lean_closure_set(v___x_2207_, 0, v___x_2206_);
lean_closure_set(v___x_2207_, 1, v_f_2193_);
lean_inc_ref(v_value_2205_);
v___x_2208_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2205_, v___x_2207_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v_a_2211_; uint8_t v___x_2215_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref(v___x_2208_);
v___x_2215_ = lean_unbox(v_a_2209_);
lean_dec(v_a_2209_);
if (v___x_2215_ == 0)
{
v_a_2211_ = v_b_2197_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2216_; 
lean_inc(v___x_2204_);
v___x_2216_ = lean_array_push(v_b_2197_, v___x_2204_);
v_a_2211_ = v___x_2216_;
goto v___jp_2210_;
}
v___jp_2210_:
{
size_t v___x_2212_; size_t v___x_2213_; 
v___x_2212_ = ((size_t)1ULL);
v___x_2213_ = lean_usize_add(v_i_2195_, v___x_2212_);
v_i_2195_ = v___x_2213_;
v_b_2197_ = v_a_2211_;
goto _start;
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v_b_2197_);
lean_dec_ref(v_f_2193_);
v_a_2217_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2208_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2208_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v___x_2225_; 
lean_dec_ref(v_f_2193_);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v_b_2197_);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0___boxed(lean_object* v_pu_2226_, lean_object* v_f_2227_, lean_object* v_as_2228_, lean_object* v_i_2229_, lean_object* v_stop_2230_, lean_object* v_b_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
uint8_t v_pu_boxed_2237_; size_t v_i_boxed_2238_; size_t v_stop_boxed_2239_; lean_object* v_res_2240_; 
v_pu_boxed_2237_ = lean_unbox(v_pu_2226_);
v_i_boxed_2238_ = lean_unbox_usize(v_i_2229_);
lean_dec(v_i_2229_);
v_stop_boxed_2239_ = lean_unbox_usize(v_stop_2230_);
lean_dec(v_stop_2230_);
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_boxed_2237_, v_f_2227_, v_as_2228_, v_i_boxed_2238_, v_stop_boxed_2239_, v_b_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v_as_2228_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl(uint8_t v_pu_2241_, lean_object* v_f_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2249_ = lean_unsigned_to_nat(0u);
v___x_2250_ = lean_array_get_size(v_a_2243_);
v___x_2251_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2252_ = lean_nat_dec_lt(v___x_2249_, v___x_2250_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
lean_dec_ref(v_f_2242_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
return v___x_2253_;
}
else
{
uint8_t v___x_2254_; 
v___x_2254_ = lean_nat_dec_le(v___x_2250_, v___x_2250_);
if (v___x_2254_ == 0)
{
if (v___x_2252_ == 0)
{
lean_object* v___x_2255_; 
lean_dec_ref(v_f_2242_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2251_);
return v___x_2255_;
}
else
{
size_t v___x_2256_; size_t v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = ((size_t)0ULL);
v___x_2257_ = lean_usize_of_nat(v___x_2250_);
v___x_2258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2241_, v_f_2242_, v_a_2243_, v___x_2256_, v___x_2257_, v___x_2251_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
return v___x_2258_;
}
}
else
{
size_t v___x_2259_; size_t v___x_2260_; lean_object* v___x_2261_; 
v___x_2259_ = ((size_t)0ULL);
v___x_2260_ = lean_usize_of_nat(v___x_2250_);
v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2241_, v_f_2242_, v_a_2243_, v___x_2259_, v___x_2260_, v___x_2251_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
return v___x_2261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl___boxed(lean_object* v_pu_2262_, lean_object* v_f_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
uint8_t v_pu_boxed_2270_; lean_object* v_res_2271_; 
v_pu_boxed_2270_ = lean_unbox(v_pu_2262_);
v_res_2271_ = l_Lean_Compiler_LCNF_Probe_filterByFunDecl(v_pu_boxed_2270_, v_f_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec_ref(v_a_2264_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(uint8_t v_pu_2272_, lean_object* v_f_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
switch(lean_obj_tag(v_a_2274_))
{
case 0:
{
lean_object* v_k_2280_; 
v_k_2280_ = lean_ctor_get(v_a_2274_, 1);
lean_inc_ref(v_k_2280_);
lean_dec_ref(v_a_2274_);
v_a_2274_ = v_k_2280_;
goto _start;
}
case 1:
{
lean_object* v_decl_2282_; lean_object* v_k_2283_; lean_object* v_value_2284_; lean_object* v___x_2285_; 
v_decl_2282_ = lean_ctor_get(v_a_2274_, 0);
lean_inc_ref(v_decl_2282_);
v_k_2283_ = lean_ctor_get(v_a_2274_, 1);
lean_inc_ref(v_k_2283_);
lean_dec_ref(v_a_2274_);
v_value_2284_ = lean_ctor_get(v_decl_2282_, 4);
lean_inc_ref(v_value_2284_);
lean_dec_ref(v_decl_2282_);
lean_inc_ref(v_f_2273_);
v___x_2285_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2272_, v_f_2273_, v_value_2284_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; uint8_t v___x_2287_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
v___x_2287_ = lean_unbox(v_a_2286_);
lean_dec(v_a_2286_);
if (v___x_2287_ == 0)
{
lean_dec_ref(v___x_2285_);
v_a_2274_ = v_k_2283_;
goto _start;
}
else
{
lean_dec_ref(v_k_2283_);
lean_dec_ref(v_f_2273_);
return v___x_2285_;
}
}
else
{
lean_dec_ref(v_k_2283_);
lean_dec_ref(v_f_2273_);
return v___x_2285_;
}
}
case 2:
{
lean_object* v_decl_2289_; lean_object* v_k_2290_; lean_object* v_value_2291_; lean_object* v___x_2292_; 
v_decl_2289_ = lean_ctor_get(v_a_2274_, 0);
lean_inc_ref(v_decl_2289_);
v_k_2290_ = lean_ctor_get(v_a_2274_, 1);
lean_inc_ref(v_k_2290_);
lean_dec_ref(v_a_2274_);
v_value_2291_ = lean_ctor_get(v_decl_2289_, 4);
lean_inc_ref(v_value_2291_);
lean_dec_ref(v_decl_2289_);
lean_inc_ref(v_f_2273_);
v___x_2292_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2272_, v_f_2273_, v_value_2291_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; uint8_t v___x_2294_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
v___x_2294_ = lean_unbox(v_a_2293_);
lean_dec(v_a_2293_);
if (v___x_2294_ == 0)
{
lean_dec_ref(v___x_2292_);
v_a_2274_ = v_k_2290_;
goto _start;
}
else
{
lean_dec_ref(v_k_2290_);
lean_dec_ref(v_f_2273_);
return v___x_2292_;
}
}
else
{
lean_dec_ref(v_k_2290_);
lean_dec_ref(v_f_2273_);
return v___x_2292_;
}
}
case 4:
{
lean_object* v_cases_2296_; lean_object* v___x_2297_; 
v_cases_2296_ = lean_ctor_get(v_a_2274_, 0);
lean_inc_ref(v_cases_2296_);
lean_dec_ref(v_a_2274_);
lean_inc_ref(v_f_2273_);
lean_inc(v_a_2278_);
lean_inc_ref(v_a_2277_);
lean_inc(v_a_2276_);
lean_inc_ref(v_a_2275_);
lean_inc_ref(v_cases_2296_);
v___x_2297_ = lean_apply_6(v_f_2273_, v_cases_2296_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, lean_box(0));
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; uint8_t v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
v___x_2299_ = lean_unbox(v_a_2298_);
lean_dec(v_a_2298_);
if (v___x_2299_ == 0)
{
lean_object* v_alts_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v_alts_2300_ = lean_ctor_get(v_cases_2296_, 3);
lean_inc_ref(v_alts_2300_);
lean_dec_ref(v_cases_2296_);
v___x_2301_ = lean_unsigned_to_nat(0u);
v___x_2302_ = lean_array_get_size(v_alts_2300_);
v___x_2303_ = lean_nat_dec_lt(v___x_2301_, v___x_2302_);
if (v___x_2303_ == 0)
{
lean_dec_ref(v_alts_2300_);
lean_dec_ref(v_f_2273_);
return v___x_2297_;
}
else
{
if (v___x_2303_ == 0)
{
lean_dec_ref(v_alts_2300_);
lean_dec_ref(v_f_2273_);
return v___x_2297_;
}
else
{
size_t v___x_2304_; size_t v___x_2305_; lean_object* v___x_2306_; 
lean_dec_ref(v___x_2297_);
v___x_2304_ = ((size_t)0ULL);
v___x_2305_ = lean_usize_of_nat(v___x_2302_);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_2272_, v_f_2273_, v_alts_2300_, v___x_2304_, v___x_2305_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
lean_dec_ref(v_alts_2300_);
return v___x_2306_;
}
}
}
else
{
lean_dec_ref(v_cases_2296_);
lean_dec_ref(v_f_2273_);
return v___x_2297_;
}
}
else
{
lean_dec_ref(v_cases_2296_);
lean_dec_ref(v_f_2273_);
return v___x_2297_;
}
}
case 7:
{
lean_object* v_k_2307_; 
v_k_2307_ = lean_ctor_get(v_a_2274_, 3);
lean_inc_ref(v_k_2307_);
lean_dec_ref(v_a_2274_);
v_a_2274_ = v_k_2307_;
goto _start;
}
case 8:
{
lean_object* v_k_2309_; 
v_k_2309_ = lean_ctor_get(v_a_2274_, 3);
lean_inc_ref(v_k_2309_);
lean_dec_ref(v_a_2274_);
v_a_2274_ = v_k_2309_;
goto _start;
}
case 9:
{
lean_object* v_k_2311_; 
v_k_2311_ = lean_ctor_get(v_a_2274_, 5);
lean_inc_ref(v_k_2311_);
lean_dec_ref(v_a_2274_);
v_a_2274_ = v_k_2311_;
goto _start;
}
case 10:
{
lean_object* v_k_2313_; 
v_k_2313_ = lean_ctor_get(v_a_2274_, 2);
lean_inc_ref(v_k_2313_);
lean_dec_ref(v_a_2274_);
v_a_2274_ = v_k_2313_;
goto _start;
}
case 11:
{
lean_object* v_k_2315_; 
v_k_2315_ = lean_ctor_get(v_a_2274_, 2);
lean_inc_ref(v_k_2315_);
lean_dec_ref(v_a_2274_);
v_a_2274_ = v_k_2315_;
goto _start;
}
case 12:
{
lean_object* v_k_2317_; 
v_k_2317_ = lean_ctor_get(v_a_2274_, 2);
lean_inc_ref(v_k_2317_);
lean_dec_ref(v_a_2274_);
v_a_2274_ = v_k_2317_;
goto _start;
}
case 13:
{
lean_object* v_k_2319_; 
v_k_2319_ = lean_ctor_get(v_a_2274_, 1);
lean_inc_ref(v_k_2319_);
lean_dec_ref(v_a_2274_);
v_a_2274_ = v_k_2319_;
goto _start;
}
default: 
{
uint8_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v_a_2274_);
lean_dec_ref(v_f_2273_);
v___x_2321_ = 0;
v___x_2322_ = lean_box(v___x_2321_);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(uint8_t v_pu_2324_, lean_object* v_f_2325_, lean_object* v_as_2326_, size_t v_i_2327_, size_t v_stop_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_usize_dec_eq(v_i_2327_, v_stop_2328_);
if (v___x_2334_ == 0)
{
uint8_t v___x_2335_; lean_object* v___y_2337_; lean_object* v___x_2352_; 
v___x_2335_ = 1;
v___x_2352_ = lean_array_uget_borrowed(v_as_2326_, v_i_2327_);
switch(lean_obj_tag(v___x_2352_))
{
case 0:
{
lean_object* v_code_2353_; 
v_code_2353_ = lean_ctor_get(v___x_2352_, 2);
lean_inc_ref(v_code_2353_);
v___y_2337_ = v_code_2353_;
goto v___jp_2336_;
}
case 1:
{
lean_object* v_code_2354_; 
v_code_2354_ = lean_ctor_get(v___x_2352_, 1);
lean_inc_ref(v_code_2354_);
v___y_2337_ = v_code_2354_;
goto v___jp_2336_;
}
default: 
{
lean_object* v_code_2355_; 
v_code_2355_ = lean_ctor_get(v___x_2352_, 0);
lean_inc_ref(v_code_2355_);
v___y_2337_ = v_code_2355_;
goto v___jp_2336_;
}
}
v___jp_2336_:
{
lean_object* v___x_2338_; 
lean_inc_ref(v_f_2325_);
v___x_2338_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2324_, v_f_2325_, v___y_2337_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2351_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2351_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2351_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
uint8_t v___x_2343_; 
v___x_2343_ = lean_unbox(v_a_2339_);
lean_dec(v_a_2339_);
if (v___x_2343_ == 0)
{
size_t v___x_2344_; size_t v___x_2345_; 
lean_del_object(v___x_2341_);
v___x_2344_ = ((size_t)1ULL);
v___x_2345_ = lean_usize_add(v_i_2327_, v___x_2344_);
v_i_2327_ = v___x_2345_;
goto _start;
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
lean_dec_ref(v_f_2325_);
v___x_2347_ = lean_box(v___x_2335_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2347_);
v___x_2349_ = v___x_2341_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_dec_ref(v_f_2325_);
return v___x_2338_;
}
}
}
else
{
uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_dec_ref(v_f_2325_);
v___x_2356_ = 0;
v___x_2357_ = lean_box(v___x_2356_);
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
return v___x_2358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0___boxed(lean_object* v_pu_2359_, lean_object* v_f_2360_, lean_object* v_as_2361_, lean_object* v_i_2362_, lean_object* v_stop_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
uint8_t v_pu_boxed_2369_; size_t v_i_boxed_2370_; size_t v_stop_boxed_2371_; lean_object* v_res_2372_; 
v_pu_boxed_2369_ = lean_unbox(v_pu_2359_);
v_i_boxed_2370_ = lean_unbox_usize(v_i_2362_);
lean_dec(v_i_2362_);
v_stop_boxed_2371_ = lean_unbox_usize(v_stop_2363_);
lean_dec(v_stop_2363_);
v_res_2372_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_boxed_2369_, v_f_2360_, v_as_2361_, v_i_boxed_2370_, v_stop_boxed_2371_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec_ref(v_as_2361_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed(lean_object* v_pu_2373_, lean_object* v_f_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
uint8_t v_pu_boxed_2381_; lean_object* v_res_2382_; 
v_pu_boxed_2381_ = lean_unbox(v_pu_2373_);
v_res_2382_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_boxed_2381_, v_f_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(uint8_t v_pu_2383_, lean_object* v_f_2384_, lean_object* v_as_2385_, size_t v_i_2386_, size_t v_stop_2387_, lean_object* v_b_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_usize_dec_eq(v_i_2386_, v_stop_2387_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; lean_object* v_value_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2395_ = lean_array_uget_borrowed(v_as_2385_, v_i_2386_);
v_value_2396_ = lean_ctor_get(v___x_2395_, 1);
v___x_2397_ = lean_box(v_pu_2383_);
lean_inc_ref(v_f_2384_);
v___x_2398_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed), 8, 2);
lean_closure_set(v___x_2398_, 0, v___x_2397_);
lean_closure_set(v___x_2398_, 1, v_f_2384_);
lean_inc_ref(v_value_2396_);
v___x_2399_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2396_, v___x_2398_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v_a_2402_; uint8_t v___x_2406_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref(v___x_2399_);
v___x_2406_ = lean_unbox(v_a_2400_);
lean_dec(v_a_2400_);
if (v___x_2406_ == 0)
{
v_a_2402_ = v_b_2388_;
goto v___jp_2401_;
}
else
{
lean_object* v___x_2407_; 
lean_inc(v___x_2395_);
v___x_2407_ = lean_array_push(v_b_2388_, v___x_2395_);
v_a_2402_ = v___x_2407_;
goto v___jp_2401_;
}
v___jp_2401_:
{
size_t v___x_2403_; size_t v___x_2404_; 
v___x_2403_ = ((size_t)1ULL);
v___x_2404_ = lean_usize_add(v_i_2386_, v___x_2403_);
v_i_2386_ = v___x_2404_;
v_b_2388_ = v_a_2402_;
goto _start;
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec_ref(v_b_2388_);
lean_dec_ref(v_f_2384_);
v_a_2408_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2399_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2399_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
else
{
lean_object* v___x_2416_; 
lean_dec_ref(v_f_2384_);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_b_2388_);
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0___boxed(lean_object* v_pu_2417_, lean_object* v_f_2418_, lean_object* v_as_2419_, lean_object* v_i_2420_, lean_object* v_stop_2421_, lean_object* v_b_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
uint8_t v_pu_boxed_2428_; size_t v_i_boxed_2429_; size_t v_stop_boxed_2430_; lean_object* v_res_2431_; 
v_pu_boxed_2428_ = lean_unbox(v_pu_2417_);
v_i_boxed_2429_ = lean_unbox_usize(v_i_2420_);
lean_dec(v_i_2420_);
v_stop_boxed_2430_ = lean_unbox_usize(v_stop_2421_);
lean_dec(v_stop_2421_);
v_res_2431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_boxed_2428_, v_f_2418_, v_as_2419_, v_i_boxed_2429_, v_stop_boxed_2430_, v_b_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec_ref(v_as_2419_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases(uint8_t v_pu_2432_, lean_object* v_f_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; 
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = lean_array_get_size(v_a_2434_);
v___x_2442_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2443_ = lean_nat_dec_lt(v___x_2440_, v___x_2441_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; 
lean_dec_ref(v_f_2433_);
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2442_);
return v___x_2444_;
}
else
{
uint8_t v___x_2445_; 
v___x_2445_ = lean_nat_dec_le(v___x_2441_, v___x_2441_);
if (v___x_2445_ == 0)
{
if (v___x_2443_ == 0)
{
lean_object* v___x_2446_; 
lean_dec_ref(v_f_2433_);
v___x_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2442_);
return v___x_2446_;
}
else
{
size_t v___x_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = ((size_t)0ULL);
v___x_2448_ = lean_usize_of_nat(v___x_2441_);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2432_, v_f_2433_, v_a_2434_, v___x_2447_, v___x_2448_, v___x_2442_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_);
return v___x_2449_;
}
}
else
{
size_t v___x_2450_; size_t v___x_2451_; lean_object* v___x_2452_; 
v___x_2450_ = ((size_t)0ULL);
v___x_2451_ = lean_usize_of_nat(v___x_2441_);
v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2432_, v_f_2433_, v_a_2434_, v___x_2450_, v___x_2451_, v___x_2442_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_);
return v___x_2452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases___boxed(lean_object* v_pu_2453_, lean_object* v_f_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
uint8_t v_pu_boxed_2461_; lean_object* v_res_2462_; 
v_pu_boxed_2461_ = lean_unbox(v_pu_2453_);
v_res_2462_ = l_Lean_Compiler_LCNF_Probe_filterByCases(v_pu_boxed_2461_, v_f_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec_ref(v_a_2455_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(uint8_t v_pu_2463_, lean_object* v_f_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
switch(lean_obj_tag(v_a_2465_))
{
case 0:
{
lean_object* v_k_2471_; 
v_k_2471_ = lean_ctor_get(v_a_2465_, 1);
lean_inc_ref(v_k_2471_);
lean_dec_ref(v_a_2465_);
v_a_2465_ = v_k_2471_;
goto _start;
}
case 1:
{
lean_object* v_decl_2473_; lean_object* v_k_2474_; lean_object* v_value_2475_; lean_object* v___x_2476_; 
v_decl_2473_ = lean_ctor_get(v_a_2465_, 0);
lean_inc_ref(v_decl_2473_);
v_k_2474_ = lean_ctor_get(v_a_2465_, 1);
lean_inc_ref(v_k_2474_);
lean_dec_ref(v_a_2465_);
v_value_2475_ = lean_ctor_get(v_decl_2473_, 4);
lean_inc_ref(v_value_2475_);
lean_dec_ref(v_decl_2473_);
lean_inc_ref(v_f_2464_);
v___x_2476_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2463_, v_f_2464_, v_value_2475_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; uint8_t v___x_2478_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
v___x_2478_ = lean_unbox(v_a_2477_);
lean_dec(v_a_2477_);
if (v___x_2478_ == 0)
{
lean_dec_ref(v___x_2476_);
v_a_2465_ = v_k_2474_;
goto _start;
}
else
{
lean_dec_ref(v_k_2474_);
lean_dec_ref(v_f_2464_);
return v___x_2476_;
}
}
else
{
lean_dec_ref(v_k_2474_);
lean_dec_ref(v_f_2464_);
return v___x_2476_;
}
}
case 2:
{
lean_object* v_decl_2480_; lean_object* v_k_2481_; lean_object* v_value_2482_; lean_object* v___x_2483_; 
v_decl_2480_ = lean_ctor_get(v_a_2465_, 0);
lean_inc_ref(v_decl_2480_);
v_k_2481_ = lean_ctor_get(v_a_2465_, 1);
lean_inc_ref(v_k_2481_);
lean_dec_ref(v_a_2465_);
v_value_2482_ = lean_ctor_get(v_decl_2480_, 4);
lean_inc_ref(v_value_2482_);
lean_dec_ref(v_decl_2480_);
lean_inc_ref(v_f_2464_);
v___x_2483_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2463_, v_f_2464_, v_value_2482_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; uint8_t v___x_2485_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
v___x_2485_ = lean_unbox(v_a_2484_);
lean_dec(v_a_2484_);
if (v___x_2485_ == 0)
{
lean_dec_ref(v___x_2483_);
v_a_2465_ = v_k_2481_;
goto _start;
}
else
{
lean_dec_ref(v_k_2481_);
lean_dec_ref(v_f_2464_);
return v___x_2483_;
}
}
else
{
lean_dec_ref(v_k_2481_);
lean_dec_ref(v_f_2464_);
return v___x_2483_;
}
}
case 3:
{
lean_object* v_fvarId_2487_; lean_object* v_args_2488_; lean_object* v___x_2489_; 
v_fvarId_2487_ = lean_ctor_get(v_a_2465_, 0);
lean_inc(v_fvarId_2487_);
v_args_2488_ = lean_ctor_get(v_a_2465_, 1);
lean_inc_ref(v_args_2488_);
lean_dec_ref(v_a_2465_);
lean_inc(v_a_2469_);
lean_inc_ref(v_a_2468_);
lean_inc(v_a_2467_);
lean_inc_ref(v_a_2466_);
v___x_2489_ = lean_apply_7(v_f_2464_, v_fvarId_2487_, v_args_2488_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, lean_box(0));
return v___x_2489_;
}
case 4:
{
lean_object* v_cases_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2509_; 
v_cases_2490_ = lean_ctor_get(v_a_2465_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_a_2465_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2492_ = v_a_2465_;
v_isShared_2493_ = v_isSharedCheck_2509_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_cases_2490_);
lean_dec(v_a_2465_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2509_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v_alts_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v_alts_2494_ = lean_ctor_get(v_cases_2490_, 3);
lean_inc_ref(v_alts_2494_);
lean_dec_ref(v_cases_2490_);
v___x_2495_ = lean_unsigned_to_nat(0u);
v___x_2496_ = lean_array_get_size(v_alts_2494_);
v___x_2497_ = lean_nat_dec_lt(v___x_2495_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2500_; 
lean_dec_ref(v_alts_2494_);
lean_dec_ref(v_f_2464_);
v___x_2498_ = lean_box(v___x_2497_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set_tag(v___x_2492_, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2498_);
v___x_2500_ = v___x_2492_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
else
{
if (v___x_2497_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2504_; 
lean_dec_ref(v_alts_2494_);
lean_dec_ref(v_f_2464_);
v___x_2502_ = lean_box(v___x_2497_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set_tag(v___x_2492_, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2502_);
v___x_2504_ = v___x_2492_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2502_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
else
{
size_t v___x_2506_; size_t v___x_2507_; lean_object* v___x_2508_; 
lean_del_object(v___x_2492_);
v___x_2506_ = ((size_t)0ULL);
v___x_2507_ = lean_usize_of_nat(v___x_2496_);
v___x_2508_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_2463_, v_f_2464_, v_alts_2494_, v___x_2506_, v___x_2507_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
lean_dec_ref(v_alts_2494_);
return v___x_2508_;
}
}
}
}
case 7:
{
lean_object* v_k_2510_; 
v_k_2510_ = lean_ctor_get(v_a_2465_, 3);
lean_inc_ref(v_k_2510_);
lean_dec_ref(v_a_2465_);
v_a_2465_ = v_k_2510_;
goto _start;
}
case 8:
{
lean_object* v_k_2512_; 
v_k_2512_ = lean_ctor_get(v_a_2465_, 3);
lean_inc_ref(v_k_2512_);
lean_dec_ref(v_a_2465_);
v_a_2465_ = v_k_2512_;
goto _start;
}
case 9:
{
lean_object* v_k_2514_; 
v_k_2514_ = lean_ctor_get(v_a_2465_, 5);
lean_inc_ref(v_k_2514_);
lean_dec_ref(v_a_2465_);
v_a_2465_ = v_k_2514_;
goto _start;
}
case 10:
{
lean_object* v_k_2516_; 
v_k_2516_ = lean_ctor_get(v_a_2465_, 2);
lean_inc_ref(v_k_2516_);
lean_dec_ref(v_a_2465_);
v_a_2465_ = v_k_2516_;
goto _start;
}
case 11:
{
lean_object* v_k_2518_; 
v_k_2518_ = lean_ctor_get(v_a_2465_, 2);
lean_inc_ref(v_k_2518_);
lean_dec_ref(v_a_2465_);
v_a_2465_ = v_k_2518_;
goto _start;
}
case 12:
{
lean_object* v_k_2520_; 
v_k_2520_ = lean_ctor_get(v_a_2465_, 2);
lean_inc_ref(v_k_2520_);
lean_dec_ref(v_a_2465_);
v_a_2465_ = v_k_2520_;
goto _start;
}
case 13:
{
lean_object* v_k_2522_; 
v_k_2522_ = lean_ctor_get(v_a_2465_, 1);
lean_inc_ref(v_k_2522_);
lean_dec_ref(v_a_2465_);
v_a_2465_ = v_k_2522_;
goto _start;
}
default: 
{
uint8_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec_ref(v_a_2465_);
lean_dec_ref(v_f_2464_);
v___x_2524_ = 0;
v___x_2525_ = lean_box(v___x_2524_);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(uint8_t v_pu_2527_, lean_object* v_f_2528_, lean_object* v_as_2529_, size_t v_i_2530_, size_t v_stop_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_usize_dec_eq(v_i_2530_, v_stop_2531_);
if (v___x_2537_ == 0)
{
uint8_t v___x_2538_; lean_object* v___y_2540_; lean_object* v___x_2555_; 
v___x_2538_ = 1;
v___x_2555_ = lean_array_uget_borrowed(v_as_2529_, v_i_2530_);
switch(lean_obj_tag(v___x_2555_))
{
case 0:
{
lean_object* v_code_2556_; 
v_code_2556_ = lean_ctor_get(v___x_2555_, 2);
lean_inc_ref(v_code_2556_);
v___y_2540_ = v_code_2556_;
goto v___jp_2539_;
}
case 1:
{
lean_object* v_code_2557_; 
v_code_2557_ = lean_ctor_get(v___x_2555_, 1);
lean_inc_ref(v_code_2557_);
v___y_2540_ = v_code_2557_;
goto v___jp_2539_;
}
default: 
{
lean_object* v_code_2558_; 
v_code_2558_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_ref(v_code_2558_);
v___y_2540_ = v_code_2558_;
goto v___jp_2539_;
}
}
v___jp_2539_:
{
lean_object* v___x_2541_; 
lean_inc_ref(v_f_2528_);
v___x_2541_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2527_, v_f_2528_, v___y_2540_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2554_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2554_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2554_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
uint8_t v___x_2546_; 
v___x_2546_ = lean_unbox(v_a_2542_);
lean_dec(v_a_2542_);
if (v___x_2546_ == 0)
{
size_t v___x_2547_; size_t v___x_2548_; 
lean_del_object(v___x_2544_);
v___x_2547_ = ((size_t)1ULL);
v___x_2548_ = lean_usize_add(v_i_2530_, v___x_2547_);
v_i_2530_ = v___x_2548_;
goto _start;
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2552_; 
lean_dec_ref(v_f_2528_);
v___x_2550_ = lean_box(v___x_2538_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2550_);
v___x_2552_ = v___x_2544_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
else
{
lean_dec_ref(v_f_2528_);
return v___x_2541_;
}
}
}
else
{
uint8_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
lean_dec_ref(v_f_2528_);
v___x_2559_ = 0;
v___x_2560_ = lean_box(v___x_2559_);
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0___boxed(lean_object* v_pu_2562_, lean_object* v_f_2563_, lean_object* v_as_2564_, lean_object* v_i_2565_, lean_object* v_stop_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
uint8_t v_pu_boxed_2572_; size_t v_i_boxed_2573_; size_t v_stop_boxed_2574_; lean_object* v_res_2575_; 
v_pu_boxed_2572_ = lean_unbox(v_pu_2562_);
v_i_boxed_2573_ = lean_unbox_usize(v_i_2565_);
lean_dec(v_i_2565_);
v_stop_boxed_2574_ = lean_unbox_usize(v_stop_2566_);
lean_dec(v_stop_2566_);
v_res_2575_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_boxed_2572_, v_f_2563_, v_as_2564_, v_i_boxed_2573_, v_stop_boxed_2574_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec_ref(v_as_2564_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed(lean_object* v_pu_2576_, lean_object* v_f_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
uint8_t v_pu_boxed_2584_; lean_object* v_res_2585_; 
v_pu_boxed_2584_ = lean_unbox(v_pu_2576_);
v_res_2585_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_boxed_2584_, v_f_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(uint8_t v_pu_2586_, lean_object* v_f_2587_, lean_object* v_as_2588_, size_t v_i_2589_, size_t v_stop_2590_, lean_object* v_b_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
uint8_t v___x_2597_; 
v___x_2597_ = lean_usize_dec_eq(v_i_2589_, v_stop_2590_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v_value_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2598_ = lean_array_uget_borrowed(v_as_2588_, v_i_2589_);
v_value_2599_ = lean_ctor_get(v___x_2598_, 1);
v___x_2600_ = lean_box(v_pu_2586_);
lean_inc_ref(v_f_2587_);
v___x_2601_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed), 8, 2);
lean_closure_set(v___x_2601_, 0, v___x_2600_);
lean_closure_set(v___x_2601_, 1, v_f_2587_);
lean_inc_ref(v_value_2599_);
v___x_2602_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2599_, v___x_2601_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v_a_2605_; uint8_t v___x_2609_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref(v___x_2602_);
v___x_2609_ = lean_unbox(v_a_2603_);
lean_dec(v_a_2603_);
if (v___x_2609_ == 0)
{
v_a_2605_ = v_b_2591_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2610_; 
lean_inc(v___x_2598_);
v___x_2610_ = lean_array_push(v_b_2591_, v___x_2598_);
v_a_2605_ = v___x_2610_;
goto v___jp_2604_;
}
v___jp_2604_:
{
size_t v___x_2606_; size_t v___x_2607_; 
v___x_2606_ = ((size_t)1ULL);
v___x_2607_ = lean_usize_add(v_i_2589_, v___x_2606_);
v_i_2589_ = v___x_2607_;
v_b_2591_ = v_a_2605_;
goto _start;
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec_ref(v_b_2591_);
lean_dec_ref(v_f_2587_);
v_a_2611_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2602_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2602_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_object* v___x_2619_; 
lean_dec_ref(v_f_2587_);
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_b_2591_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0___boxed(lean_object* v_pu_2620_, lean_object* v_f_2621_, lean_object* v_as_2622_, lean_object* v_i_2623_, lean_object* v_stop_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
uint8_t v_pu_boxed_2631_; size_t v_i_boxed_2632_; size_t v_stop_boxed_2633_; lean_object* v_res_2634_; 
v_pu_boxed_2631_ = lean_unbox(v_pu_2620_);
v_i_boxed_2632_ = lean_unbox_usize(v_i_2623_);
lean_dec(v_i_2623_);
v_stop_boxed_2633_ = lean_unbox_usize(v_stop_2624_);
lean_dec(v_stop_2624_);
v_res_2634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_boxed_2631_, v_f_2621_, v_as_2622_, v_i_boxed_2632_, v_stop_boxed_2633_, v_b_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v_as_2622_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp(uint8_t v_pu_2635_, lean_object* v_f_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_array_get_size(v_a_2637_);
v___x_2645_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2646_ = lean_nat_dec_lt(v___x_2643_, v___x_2644_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; 
lean_dec_ref(v_f_2636_);
v___x_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2645_);
return v___x_2647_;
}
else
{
uint8_t v___x_2648_; 
v___x_2648_ = lean_nat_dec_le(v___x_2644_, v___x_2644_);
if (v___x_2648_ == 0)
{
if (v___x_2646_ == 0)
{
lean_object* v___x_2649_; 
lean_dec_ref(v_f_2636_);
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2645_);
return v___x_2649_;
}
else
{
size_t v___x_2650_; size_t v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = ((size_t)0ULL);
v___x_2651_ = lean_usize_of_nat(v___x_2644_);
v___x_2652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2635_, v_f_2636_, v_a_2637_, v___x_2650_, v___x_2651_, v___x_2645_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
return v___x_2652_;
}
}
else
{
size_t v___x_2653_; size_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = ((size_t)0ULL);
v___x_2654_ = lean_usize_of_nat(v___x_2644_);
v___x_2655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2635_, v_f_2636_, v_a_2637_, v___x_2653_, v___x_2654_, v___x_2645_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
return v___x_2655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp___boxed(lean_object* v_pu_2656_, lean_object* v_f_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
uint8_t v_pu_boxed_2664_; lean_object* v_res_2665_; 
v_pu_boxed_2664_ = lean_unbox(v_pu_2656_);
v_res_2665_ = l_Lean_Compiler_LCNF_Probe_filterByJmp(v_pu_boxed_2664_, v_f_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec_ref(v_a_2658_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(uint8_t v_pu_2666_, lean_object* v_f_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
switch(lean_obj_tag(v_a_2668_))
{
case 0:
{
lean_object* v_k_2674_; 
v_k_2674_ = lean_ctor_get(v_a_2668_, 1);
lean_inc_ref(v_k_2674_);
lean_dec_ref(v_a_2668_);
v_a_2668_ = v_k_2674_;
goto _start;
}
case 1:
{
lean_object* v_decl_2676_; lean_object* v_k_2677_; lean_object* v_value_2678_; lean_object* v___x_2679_; 
v_decl_2676_ = lean_ctor_get(v_a_2668_, 0);
lean_inc_ref(v_decl_2676_);
v_k_2677_ = lean_ctor_get(v_a_2668_, 1);
lean_inc_ref(v_k_2677_);
lean_dec_ref(v_a_2668_);
v_value_2678_ = lean_ctor_get(v_decl_2676_, 4);
lean_inc_ref(v_value_2678_);
lean_dec_ref(v_decl_2676_);
lean_inc_ref(v_f_2667_);
v___x_2679_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2666_, v_f_2667_, v_value_2678_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; uint8_t v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
v___x_2681_ = lean_unbox(v_a_2680_);
lean_dec(v_a_2680_);
if (v___x_2681_ == 0)
{
lean_dec_ref(v___x_2679_);
v_a_2668_ = v_k_2677_;
goto _start;
}
else
{
lean_dec_ref(v_k_2677_);
lean_dec_ref(v_f_2667_);
return v___x_2679_;
}
}
else
{
lean_dec_ref(v_k_2677_);
lean_dec_ref(v_f_2667_);
return v___x_2679_;
}
}
case 2:
{
lean_object* v_decl_2683_; lean_object* v_k_2684_; lean_object* v_value_2685_; lean_object* v___x_2686_; 
v_decl_2683_ = lean_ctor_get(v_a_2668_, 0);
lean_inc_ref(v_decl_2683_);
v_k_2684_ = lean_ctor_get(v_a_2668_, 1);
lean_inc_ref(v_k_2684_);
lean_dec_ref(v_a_2668_);
v_value_2685_ = lean_ctor_get(v_decl_2683_, 4);
lean_inc_ref(v_value_2685_);
lean_dec_ref(v_decl_2683_);
lean_inc_ref(v_f_2667_);
v___x_2686_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2666_, v_f_2667_, v_value_2685_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; uint8_t v___x_2688_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
v___x_2688_ = lean_unbox(v_a_2687_);
lean_dec(v_a_2687_);
if (v___x_2688_ == 0)
{
lean_dec_ref(v___x_2686_);
v_a_2668_ = v_k_2684_;
goto _start;
}
else
{
lean_dec_ref(v_k_2684_);
lean_dec_ref(v_f_2667_);
return v___x_2686_;
}
}
else
{
lean_dec_ref(v_k_2684_);
lean_dec_ref(v_f_2667_);
return v___x_2686_;
}
}
case 4:
{
lean_object* v_cases_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2709_; 
v_cases_2690_ = lean_ctor_get(v_a_2668_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_a_2668_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2692_ = v_a_2668_;
v_isShared_2693_ = v_isSharedCheck_2709_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_cases_2690_);
lean_dec(v_a_2668_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2709_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_alts_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_alts_2694_ = lean_ctor_get(v_cases_2690_, 3);
lean_inc_ref(v_alts_2694_);
lean_dec_ref(v_cases_2690_);
v___x_2695_ = lean_unsigned_to_nat(0u);
v___x_2696_ = lean_array_get_size(v_alts_2694_);
v___x_2697_ = lean_nat_dec_lt(v___x_2695_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; lean_object* v___x_2700_; 
lean_dec_ref(v_alts_2694_);
lean_dec_ref(v_f_2667_);
v___x_2698_ = lean_box(v___x_2697_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2698_);
v___x_2700_ = v___x_2692_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
else
{
if (v___x_2697_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
lean_dec_ref(v_alts_2694_);
lean_dec_ref(v_f_2667_);
v___x_2702_ = lean_box(v___x_2697_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2702_);
v___x_2704_ = v___x_2692_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
else
{
size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
lean_del_object(v___x_2692_);
v___x_2706_ = ((size_t)0ULL);
v___x_2707_ = lean_usize_of_nat(v___x_2696_);
v___x_2708_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_2666_, v_f_2667_, v_alts_2694_, v___x_2706_, v___x_2707_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
lean_dec_ref(v_alts_2694_);
return v___x_2708_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2710_; lean_object* v___x_2711_; 
v_fvarId_2710_ = lean_ctor_get(v_a_2668_, 0);
lean_inc(v_fvarId_2710_);
lean_dec_ref(v_a_2668_);
lean_inc(v_a_2672_);
lean_inc_ref(v_a_2671_);
lean_inc(v_a_2670_);
lean_inc_ref(v_a_2669_);
v___x_2711_ = lean_apply_6(v_f_2667_, v_fvarId_2710_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, lean_box(0));
return v___x_2711_;
}
case 7:
{
lean_object* v_k_2712_; 
v_k_2712_ = lean_ctor_get(v_a_2668_, 3);
lean_inc_ref(v_k_2712_);
lean_dec_ref(v_a_2668_);
v_a_2668_ = v_k_2712_;
goto _start;
}
case 8:
{
lean_object* v_k_2714_; 
v_k_2714_ = lean_ctor_get(v_a_2668_, 3);
lean_inc_ref(v_k_2714_);
lean_dec_ref(v_a_2668_);
v_a_2668_ = v_k_2714_;
goto _start;
}
case 9:
{
lean_object* v_k_2716_; 
v_k_2716_ = lean_ctor_get(v_a_2668_, 5);
lean_inc_ref(v_k_2716_);
lean_dec_ref(v_a_2668_);
v_a_2668_ = v_k_2716_;
goto _start;
}
case 10:
{
lean_object* v_k_2718_; 
v_k_2718_ = lean_ctor_get(v_a_2668_, 2);
lean_inc_ref(v_k_2718_);
lean_dec_ref(v_a_2668_);
v_a_2668_ = v_k_2718_;
goto _start;
}
case 11:
{
lean_object* v_k_2720_; 
v_k_2720_ = lean_ctor_get(v_a_2668_, 2);
lean_inc_ref(v_k_2720_);
lean_dec_ref(v_a_2668_);
v_a_2668_ = v_k_2720_;
goto _start;
}
case 12:
{
lean_object* v_k_2722_; 
v_k_2722_ = lean_ctor_get(v_a_2668_, 2);
lean_inc_ref(v_k_2722_);
lean_dec_ref(v_a_2668_);
v_a_2668_ = v_k_2722_;
goto _start;
}
case 13:
{
lean_object* v_k_2724_; 
v_k_2724_ = lean_ctor_get(v_a_2668_, 1);
lean_inc_ref(v_k_2724_);
lean_dec_ref(v_a_2668_);
v_a_2668_ = v_k_2724_;
goto _start;
}
default: 
{
uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_dec_ref(v_a_2668_);
lean_dec_ref(v_f_2667_);
v___x_2726_ = 0;
v___x_2727_ = lean_box(v___x_2726_);
v___x_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
return v___x_2728_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(uint8_t v_pu_2729_, lean_object* v_f_2730_, lean_object* v_as_2731_, size_t v_i_2732_, size_t v_stop_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
uint8_t v___x_2739_; 
v___x_2739_ = lean_usize_dec_eq(v_i_2732_, v_stop_2733_);
if (v___x_2739_ == 0)
{
uint8_t v___x_2740_; lean_object* v___y_2742_; lean_object* v___x_2757_; 
v___x_2740_ = 1;
v___x_2757_ = lean_array_uget_borrowed(v_as_2731_, v_i_2732_);
switch(lean_obj_tag(v___x_2757_))
{
case 0:
{
lean_object* v_code_2758_; 
v_code_2758_ = lean_ctor_get(v___x_2757_, 2);
lean_inc_ref(v_code_2758_);
v___y_2742_ = v_code_2758_;
goto v___jp_2741_;
}
case 1:
{
lean_object* v_code_2759_; 
v_code_2759_ = lean_ctor_get(v___x_2757_, 1);
lean_inc_ref(v_code_2759_);
v___y_2742_ = v_code_2759_;
goto v___jp_2741_;
}
default: 
{
lean_object* v_code_2760_; 
v_code_2760_ = lean_ctor_get(v___x_2757_, 0);
lean_inc_ref(v_code_2760_);
v___y_2742_ = v_code_2760_;
goto v___jp_2741_;
}
}
v___jp_2741_:
{
lean_object* v___x_2743_; 
lean_inc_ref(v_f_2730_);
v___x_2743_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2729_, v_f_2730_, v___y_2742_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2756_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2756_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2756_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
uint8_t v___x_2748_; 
v___x_2748_ = lean_unbox(v_a_2744_);
lean_dec(v_a_2744_);
if (v___x_2748_ == 0)
{
size_t v___x_2749_; size_t v___x_2750_; 
lean_del_object(v___x_2746_);
v___x_2749_ = ((size_t)1ULL);
v___x_2750_ = lean_usize_add(v_i_2732_, v___x_2749_);
v_i_2732_ = v___x_2750_;
goto _start;
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
lean_dec_ref(v_f_2730_);
v___x_2752_ = lean_box(v___x_2740_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2752_);
v___x_2754_ = v___x_2746_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_dec_ref(v_f_2730_);
return v___x_2743_;
}
}
}
else
{
uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec_ref(v_f_2730_);
v___x_2761_ = 0;
v___x_2762_ = lean_box(v___x_2761_);
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0___boxed(lean_object* v_pu_2764_, lean_object* v_f_2765_, lean_object* v_as_2766_, lean_object* v_i_2767_, lean_object* v_stop_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
uint8_t v_pu_boxed_2774_; size_t v_i_boxed_2775_; size_t v_stop_boxed_2776_; lean_object* v_res_2777_; 
v_pu_boxed_2774_ = lean_unbox(v_pu_2764_);
v_i_boxed_2775_ = lean_unbox_usize(v_i_2767_);
lean_dec(v_i_2767_);
v_stop_boxed_2776_ = lean_unbox_usize(v_stop_2768_);
lean_dec(v_stop_2768_);
v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_boxed_2774_, v_f_2765_, v_as_2766_, v_i_boxed_2775_, v_stop_boxed_2776_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec_ref(v_as_2766_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed(lean_object* v_pu_2778_, lean_object* v_f_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
uint8_t v_pu_boxed_2786_; lean_object* v_res_2787_; 
v_pu_boxed_2786_ = lean_unbox(v_pu_2778_);
v_res_2787_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_boxed_2786_, v_f_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(uint8_t v_pu_2788_, lean_object* v_f_2789_, lean_object* v_as_2790_, size_t v_i_2791_, size_t v_stop_2792_, lean_object* v_b_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_usize_dec_eq(v_i_2791_, v_stop_2792_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; lean_object* v_value_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2800_ = lean_array_uget_borrowed(v_as_2790_, v_i_2791_);
v_value_2801_ = lean_ctor_get(v___x_2800_, 1);
v___x_2802_ = lean_box(v_pu_2788_);
lean_inc_ref(v_f_2789_);
v___x_2803_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed), 8, 2);
lean_closure_set(v___x_2803_, 0, v___x_2802_);
lean_closure_set(v___x_2803_, 1, v_f_2789_);
lean_inc_ref(v_value_2801_);
v___x_2804_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2801_, v___x_2803_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v_a_2807_; uint8_t v___x_2811_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref(v___x_2804_);
v___x_2811_ = lean_unbox(v_a_2805_);
lean_dec(v_a_2805_);
if (v___x_2811_ == 0)
{
v_a_2807_ = v_b_2793_;
goto v___jp_2806_;
}
else
{
lean_object* v___x_2812_; 
lean_inc(v___x_2800_);
v___x_2812_ = lean_array_push(v_b_2793_, v___x_2800_);
v_a_2807_ = v___x_2812_;
goto v___jp_2806_;
}
v___jp_2806_:
{
size_t v___x_2808_; size_t v___x_2809_; 
v___x_2808_ = ((size_t)1ULL);
v___x_2809_ = lean_usize_add(v_i_2791_, v___x_2808_);
v_i_2791_ = v___x_2809_;
v_b_2793_ = v_a_2807_;
goto _start;
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec_ref(v_b_2793_);
lean_dec_ref(v_f_2789_);
v_a_2813_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2804_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2804_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_object* v___x_2821_; 
lean_dec_ref(v_f_2789_);
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_b_2793_);
return v___x_2821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0___boxed(lean_object* v_pu_2822_, lean_object* v_f_2823_, lean_object* v_as_2824_, lean_object* v_i_2825_, lean_object* v_stop_2826_, lean_object* v_b_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
uint8_t v_pu_boxed_2833_; size_t v_i_boxed_2834_; size_t v_stop_boxed_2835_; lean_object* v_res_2836_; 
v_pu_boxed_2833_ = lean_unbox(v_pu_2822_);
v_i_boxed_2834_ = lean_unbox_usize(v_i_2825_);
lean_dec(v_i_2825_);
v_stop_boxed_2835_ = lean_unbox_usize(v_stop_2826_);
lean_dec(v_stop_2826_);
v_res_2836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_boxed_2833_, v_f_2823_, v_as_2824_, v_i_boxed_2834_, v_stop_boxed_2835_, v_b_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec_ref(v_as_2824_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn(uint8_t v_pu_2837_, lean_object* v_f_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2845_ = lean_unsigned_to_nat(0u);
v___x_2846_ = lean_array_get_size(v_a_2839_);
v___x_2847_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2848_ = lean_nat_dec_lt(v___x_2845_, v___x_2846_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
lean_dec_ref(v_f_2838_);
v___x_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
return v___x_2849_;
}
else
{
uint8_t v___x_2850_; 
v___x_2850_ = lean_nat_dec_le(v___x_2846_, v___x_2846_);
if (v___x_2850_ == 0)
{
if (v___x_2848_ == 0)
{
lean_object* v___x_2851_; 
lean_dec_ref(v_f_2838_);
v___x_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2847_);
return v___x_2851_;
}
else
{
size_t v___x_2852_; size_t v___x_2853_; lean_object* v___x_2854_; 
v___x_2852_ = ((size_t)0ULL);
v___x_2853_ = lean_usize_of_nat(v___x_2846_);
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2837_, v_f_2838_, v_a_2839_, v___x_2852_, v___x_2853_, v___x_2847_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
return v___x_2854_;
}
}
else
{
size_t v___x_2855_; size_t v___x_2856_; lean_object* v___x_2857_; 
v___x_2855_ = ((size_t)0ULL);
v___x_2856_ = lean_usize_of_nat(v___x_2846_);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2837_, v_f_2838_, v_a_2839_, v___x_2855_, v___x_2856_, v___x_2847_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_);
return v___x_2857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn___boxed(lean_object* v_pu_2858_, lean_object* v_f_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
uint8_t v_pu_boxed_2866_; lean_object* v_res_2867_; 
v_pu_boxed_2866_ = lean_unbox(v_pu_2858_);
v_res_2867_ = l_Lean_Compiler_LCNF_Probe_filterByReturn(v_pu_boxed_2866_, v_f_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec_ref(v_a_2860_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(uint8_t v_pu_2868_, lean_object* v_f_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
switch(lean_obj_tag(v_a_2870_))
{
case 0:
{
lean_object* v_k_2876_; 
v_k_2876_ = lean_ctor_get(v_a_2870_, 1);
lean_inc_ref(v_k_2876_);
lean_dec_ref(v_a_2870_);
v_a_2870_ = v_k_2876_;
goto _start;
}
case 1:
{
lean_object* v_decl_2878_; lean_object* v_k_2879_; lean_object* v_value_2880_; lean_object* v___x_2881_; 
v_decl_2878_ = lean_ctor_get(v_a_2870_, 0);
lean_inc_ref(v_decl_2878_);
v_k_2879_ = lean_ctor_get(v_a_2870_, 1);
lean_inc_ref(v_k_2879_);
lean_dec_ref(v_a_2870_);
v_value_2880_ = lean_ctor_get(v_decl_2878_, 4);
lean_inc_ref(v_value_2880_);
lean_dec_ref(v_decl_2878_);
lean_inc_ref(v_f_2869_);
v___x_2881_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2868_, v_f_2869_, v_value_2880_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; uint8_t v___x_2883_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
v___x_2883_ = lean_unbox(v_a_2882_);
lean_dec(v_a_2882_);
if (v___x_2883_ == 0)
{
lean_dec_ref(v___x_2881_);
v_a_2870_ = v_k_2879_;
goto _start;
}
else
{
lean_dec_ref(v_k_2879_);
lean_dec_ref(v_f_2869_);
return v___x_2881_;
}
}
else
{
lean_dec_ref(v_k_2879_);
lean_dec_ref(v_f_2869_);
return v___x_2881_;
}
}
case 2:
{
lean_object* v_decl_2885_; lean_object* v_k_2886_; lean_object* v_value_2887_; lean_object* v___x_2888_; 
v_decl_2885_ = lean_ctor_get(v_a_2870_, 0);
lean_inc_ref(v_decl_2885_);
v_k_2886_ = lean_ctor_get(v_a_2870_, 1);
lean_inc_ref(v_k_2886_);
lean_dec_ref(v_a_2870_);
v_value_2887_ = lean_ctor_get(v_decl_2885_, 4);
lean_inc_ref(v_value_2887_);
lean_dec_ref(v_decl_2885_);
lean_inc_ref(v_f_2869_);
v___x_2888_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2868_, v_f_2869_, v_value_2887_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; uint8_t v___x_2890_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
v___x_2890_ = lean_unbox(v_a_2889_);
lean_dec(v_a_2889_);
if (v___x_2890_ == 0)
{
lean_dec_ref(v___x_2888_);
v_a_2870_ = v_k_2886_;
goto _start;
}
else
{
lean_dec_ref(v_k_2886_);
lean_dec_ref(v_f_2869_);
return v___x_2888_;
}
}
else
{
lean_dec_ref(v_k_2886_);
lean_dec_ref(v_f_2869_);
return v___x_2888_;
}
}
case 4:
{
lean_object* v_cases_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2911_; 
v_cases_2892_ = lean_ctor_get(v_a_2870_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_a_2870_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2894_ = v_a_2870_;
v_isShared_2895_ = v_isSharedCheck_2911_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_cases_2892_);
lean_dec(v_a_2870_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2911_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v_alts_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v_alts_2896_ = lean_ctor_get(v_cases_2892_, 3);
lean_inc_ref(v_alts_2896_);
lean_dec_ref(v_cases_2892_);
v___x_2897_ = lean_unsigned_to_nat(0u);
v___x_2898_ = lean_array_get_size(v_alts_2896_);
v___x_2899_ = lean_nat_dec_lt(v___x_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
lean_dec_ref(v_alts_2896_);
lean_dec_ref(v_f_2869_);
v___x_2900_ = lean_box(v___x_2899_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set_tag(v___x_2894_, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2900_);
v___x_2902_ = v___x_2894_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
else
{
if (v___x_2899_ == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
lean_dec_ref(v_alts_2896_);
lean_dec_ref(v_f_2869_);
v___x_2904_ = lean_box(v___x_2899_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set_tag(v___x_2894_, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2904_);
v___x_2906_ = v___x_2894_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
else
{
size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
lean_del_object(v___x_2894_);
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = lean_usize_of_nat(v___x_2898_);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_2868_, v_f_2869_, v_alts_2896_, v___x_2908_, v___x_2909_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
lean_dec_ref(v_alts_2896_);
return v___x_2910_;
}
}
}
}
case 6:
{
lean_object* v_type_2912_; lean_object* v___x_2913_; 
v_type_2912_ = lean_ctor_get(v_a_2870_, 0);
lean_inc_ref(v_type_2912_);
lean_dec_ref(v_a_2870_);
lean_inc(v_a_2874_);
lean_inc_ref(v_a_2873_);
lean_inc(v_a_2872_);
lean_inc_ref(v_a_2871_);
v___x_2913_ = lean_apply_6(v_f_2869_, v_type_2912_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, lean_box(0));
return v___x_2913_;
}
case 7:
{
lean_object* v_k_2914_; 
v_k_2914_ = lean_ctor_get(v_a_2870_, 3);
lean_inc_ref(v_k_2914_);
lean_dec_ref(v_a_2870_);
v_a_2870_ = v_k_2914_;
goto _start;
}
case 8:
{
lean_object* v_k_2916_; 
v_k_2916_ = lean_ctor_get(v_a_2870_, 3);
lean_inc_ref(v_k_2916_);
lean_dec_ref(v_a_2870_);
v_a_2870_ = v_k_2916_;
goto _start;
}
case 9:
{
lean_object* v_k_2918_; 
v_k_2918_ = lean_ctor_get(v_a_2870_, 5);
lean_inc_ref(v_k_2918_);
lean_dec_ref(v_a_2870_);
v_a_2870_ = v_k_2918_;
goto _start;
}
case 10:
{
lean_object* v_k_2920_; 
v_k_2920_ = lean_ctor_get(v_a_2870_, 2);
lean_inc_ref(v_k_2920_);
lean_dec_ref(v_a_2870_);
v_a_2870_ = v_k_2920_;
goto _start;
}
case 11:
{
lean_object* v_k_2922_; 
v_k_2922_ = lean_ctor_get(v_a_2870_, 2);
lean_inc_ref(v_k_2922_);
lean_dec_ref(v_a_2870_);
v_a_2870_ = v_k_2922_;
goto _start;
}
case 12:
{
lean_object* v_k_2924_; 
v_k_2924_ = lean_ctor_get(v_a_2870_, 2);
lean_inc_ref(v_k_2924_);
lean_dec_ref(v_a_2870_);
v_a_2870_ = v_k_2924_;
goto _start;
}
case 13:
{
lean_object* v_k_2926_; 
v_k_2926_ = lean_ctor_get(v_a_2870_, 1);
lean_inc_ref(v_k_2926_);
lean_dec_ref(v_a_2870_);
v_a_2870_ = v_k_2926_;
goto _start;
}
default: 
{
uint8_t v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
lean_dec_ref(v_a_2870_);
lean_dec_ref(v_f_2869_);
v___x_2928_ = 0;
v___x_2929_ = lean_box(v___x_2928_);
v___x_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2929_);
return v___x_2930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(uint8_t v_pu_2931_, lean_object* v_f_2932_, lean_object* v_as_2933_, size_t v_i_2934_, size_t v_stop_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v___x_2941_; 
v___x_2941_ = lean_usize_dec_eq(v_i_2934_, v_stop_2935_);
if (v___x_2941_ == 0)
{
uint8_t v___x_2942_; lean_object* v___y_2944_; lean_object* v___x_2959_; 
v___x_2942_ = 1;
v___x_2959_ = lean_array_uget_borrowed(v_as_2933_, v_i_2934_);
switch(lean_obj_tag(v___x_2959_))
{
case 0:
{
lean_object* v_code_2960_; 
v_code_2960_ = lean_ctor_get(v___x_2959_, 2);
lean_inc_ref(v_code_2960_);
v___y_2944_ = v_code_2960_;
goto v___jp_2943_;
}
case 1:
{
lean_object* v_code_2961_; 
v_code_2961_ = lean_ctor_get(v___x_2959_, 1);
lean_inc_ref(v_code_2961_);
v___y_2944_ = v_code_2961_;
goto v___jp_2943_;
}
default: 
{
lean_object* v_code_2962_; 
v_code_2962_ = lean_ctor_get(v___x_2959_, 0);
lean_inc_ref(v_code_2962_);
v___y_2944_ = v_code_2962_;
goto v___jp_2943_;
}
}
v___jp_2943_:
{
lean_object* v___x_2945_; 
lean_inc_ref(v_f_2932_);
v___x_2945_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2931_, v_f_2932_, v___y_2944_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2958_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2958_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2958_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
uint8_t v___x_2950_; 
v___x_2950_ = lean_unbox(v_a_2946_);
lean_dec(v_a_2946_);
if (v___x_2950_ == 0)
{
size_t v___x_2951_; size_t v___x_2952_; 
lean_del_object(v___x_2948_);
v___x_2951_ = ((size_t)1ULL);
v___x_2952_ = lean_usize_add(v_i_2934_, v___x_2951_);
v_i_2934_ = v___x_2952_;
goto _start;
}
else
{
lean_object* v___x_2954_; lean_object* v___x_2956_; 
lean_dec_ref(v_f_2932_);
v___x_2954_ = lean_box(v___x_2942_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2954_);
v___x_2956_ = v___x_2948_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_dec_ref(v_f_2932_);
return v___x_2945_;
}
}
}
else
{
uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec_ref(v_f_2932_);
v___x_2963_ = 0;
v___x_2964_ = lean_box(v___x_2963_);
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0___boxed(lean_object* v_pu_2966_, lean_object* v_f_2967_, lean_object* v_as_2968_, lean_object* v_i_2969_, lean_object* v_stop_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
uint8_t v_pu_boxed_2976_; size_t v_i_boxed_2977_; size_t v_stop_boxed_2978_; lean_object* v_res_2979_; 
v_pu_boxed_2976_ = lean_unbox(v_pu_2966_);
v_i_boxed_2977_ = lean_unbox_usize(v_i_2969_);
lean_dec(v_i_2969_);
v_stop_boxed_2978_ = lean_unbox_usize(v_stop_2970_);
lean_dec(v_stop_2970_);
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_boxed_2976_, v_f_2967_, v_as_2968_, v_i_boxed_2977_, v_stop_boxed_2978_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec_ref(v_as_2968_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed(lean_object* v_pu_2980_, lean_object* v_f_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
uint8_t v_pu_boxed_2988_; lean_object* v_res_2989_; 
v_pu_boxed_2988_ = lean_unbox(v_pu_2980_);
v_res_2989_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_boxed_2988_, v_f_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(uint8_t v_pu_2990_, lean_object* v_f_2991_, lean_object* v_as_2992_, size_t v_i_2993_, size_t v_stop_2994_, lean_object* v_b_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
uint8_t v___x_3001_; 
v___x_3001_ = lean_usize_dec_eq(v_i_2993_, v_stop_2994_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v_value_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3002_ = lean_array_uget_borrowed(v_as_2992_, v_i_2993_);
v_value_3003_ = lean_ctor_get(v___x_3002_, 1);
v___x_3004_ = lean_box(v_pu_2990_);
lean_inc_ref(v_f_2991_);
v___x_3005_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed), 8, 2);
lean_closure_set(v___x_3005_, 0, v___x_3004_);
lean_closure_set(v___x_3005_, 1, v_f_2991_);
lean_inc_ref(v_value_3003_);
v___x_3006_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_3003_, v___x_3005_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v_a_3009_; uint8_t v___x_3013_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref(v___x_3006_);
v___x_3013_ = lean_unbox(v_a_3007_);
lean_dec(v_a_3007_);
if (v___x_3013_ == 0)
{
v_a_3009_ = v_b_2995_;
goto v___jp_3008_;
}
else
{
lean_object* v___x_3014_; 
lean_inc(v___x_3002_);
v___x_3014_ = lean_array_push(v_b_2995_, v___x_3002_);
v_a_3009_ = v___x_3014_;
goto v___jp_3008_;
}
v___jp_3008_:
{
size_t v___x_3010_; size_t v___x_3011_; 
v___x_3010_ = ((size_t)1ULL);
v___x_3011_ = lean_usize_add(v_i_2993_, v___x_3010_);
v_i_2993_ = v___x_3011_;
v_b_2995_ = v_a_3009_;
goto _start;
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v_b_2995_);
lean_dec_ref(v_f_2991_);
v_a_3015_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3006_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3006_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_object* v___x_3023_; 
lean_dec_ref(v_f_2991_);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_b_2995_);
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0___boxed(lean_object* v_pu_3024_, lean_object* v_f_3025_, lean_object* v_as_3026_, lean_object* v_i_3027_, lean_object* v_stop_3028_, lean_object* v_b_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
uint8_t v_pu_boxed_3035_; size_t v_i_boxed_3036_; size_t v_stop_boxed_3037_; lean_object* v_res_3038_; 
v_pu_boxed_3035_ = lean_unbox(v_pu_3024_);
v_i_boxed_3036_ = lean_unbox_usize(v_i_3027_);
lean_dec(v_i_3027_);
v_stop_boxed_3037_ = lean_unbox_usize(v_stop_3028_);
lean_dec(v_stop_3028_);
v_res_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_boxed_3035_, v_f_3025_, v_as_3026_, v_i_boxed_3036_, v_stop_boxed_3037_, v_b_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec_ref(v_as_3026_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach(uint8_t v_pu_3039_, lean_object* v_f_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3047_ = lean_unsigned_to_nat(0u);
v___x_3048_ = lean_array_get_size(v_a_3041_);
v___x_3049_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_3050_ = lean_nat_dec_lt(v___x_3047_, v___x_3048_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
lean_dec_ref(v_f_3040_);
v___x_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
return v___x_3051_;
}
else
{
uint8_t v___x_3052_; 
v___x_3052_ = lean_nat_dec_le(v___x_3048_, v___x_3048_);
if (v___x_3052_ == 0)
{
if (v___x_3050_ == 0)
{
lean_object* v___x_3053_; 
lean_dec_ref(v_f_3040_);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3049_);
return v___x_3053_;
}
else
{
size_t v___x_3054_; size_t v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = ((size_t)0ULL);
v___x_3055_ = lean_usize_of_nat(v___x_3048_);
v___x_3056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_3039_, v_f_3040_, v_a_3041_, v___x_3054_, v___x_3055_, v___x_3049_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
return v___x_3056_;
}
}
else
{
size_t v___x_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = ((size_t)0ULL);
v___x_3058_ = lean_usize_of_nat(v___x_3048_);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_3039_, v_f_3040_, v_a_3041_, v___x_3057_, v___x_3058_, v___x_3049_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
return v___x_3059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach___boxed(lean_object* v_pu_3060_, lean_object* v_f_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
uint8_t v_pu_boxed_3068_; lean_object* v_res_3069_; 
v_pu_boxed_3068_ = lean_unbox(v_pu_3060_);
v_res_3069_ = l_Lean_Compiler_LCNF_Probe_filterByUnreach(v_pu_boxed_3068_, v_f_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec_ref(v_a_3062_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(lean_object* v_decl_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v_toSignature_3076_; lean_object* v_name_3077_; lean_object* v___x_3078_; 
v_toSignature_3076_ = lean_ctor_get(v_decl_3070_, 0);
v_name_3077_ = lean_ctor_get(v_toSignature_3076_, 0);
lean_inc(v_name_3077_);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v_name_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed(lean_object* v_decl_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(v_decl_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec_ref(v_decl_3079_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg(lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v___x_3093_; lean_object* v_toApplicative_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3156_; 
v___x_3093_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; 
v_unused_3157_ = lean_ctor_get(v___x_3093_, 1);
lean_dec(v_unused_3157_);
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3156_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_toApplicative_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3156_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_toFunctor_3098_; lean_object* v_toSeq_3099_; lean_object* v_toSeqLeft_3100_; lean_object* v_toSeqRight_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3154_; 
v_toFunctor_3098_ = lean_ctor_get(v_toApplicative_3094_, 0);
v_toSeq_3099_ = lean_ctor_get(v_toApplicative_3094_, 2);
v_toSeqLeft_3100_ = lean_ctor_get(v_toApplicative_3094_, 3);
v_toSeqRight_3101_ = lean_ctor_get(v_toApplicative_3094_, 4);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_toApplicative_3094_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v_toApplicative_3094_, 1);
lean_dec(v_unused_3155_);
v___x_3103_ = v_toApplicative_3094_;
v_isShared_3104_ = v_isSharedCheck_3154_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_toSeqRight_3101_);
lean_inc(v_toSeqLeft_3100_);
lean_inc(v_toSeq_3099_);
lean_inc(v_toFunctor_3098_);
lean_dec(v_toApplicative_3094_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3154_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___f_3105_; lean_object* v___f_3106_; lean_object* v___f_3107_; lean_object* v___f_3108_; lean_object* v___x_3109_; lean_object* v___f_3110_; lean_object* v___f_3111_; lean_object* v___f_3112_; lean_object* v___x_3114_; 
v___f_3105_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3106_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref(v_toFunctor_3098_);
v___f_3107_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3107_, 0, v_toFunctor_3098_);
v___f_3108_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3108_, 0, v_toFunctor_3098_);
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___f_3107_);
lean_ctor_set(v___x_3109_, 1, v___f_3108_);
v___f_3110_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3110_, 0, v_toSeqRight_3101_);
v___f_3111_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3111_, 0, v_toSeqLeft_3100_);
v___f_3112_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3112_, 0, v_toSeq_3099_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 4, v___f_3110_);
lean_ctor_set(v___x_3103_, 3, v___f_3111_);
lean_ctor_set(v___x_3103_, 2, v___f_3112_);
lean_ctor_set(v___x_3103_, 1, v___f_3105_);
lean_ctor_set(v___x_3103_, 0, v___x_3109_);
v___x_3114_ = v___x_3103_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v___f_3105_);
lean_ctor_set(v_reuseFailAlloc_3153_, 2, v___f_3112_);
lean_ctor_set(v_reuseFailAlloc_3153_, 3, v___f_3111_);
lean_ctor_set(v_reuseFailAlloc_3153_, 4, v___f_3110_);
v___x_3114_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3116_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 1, v___f_3106_);
lean_ctor_set(v___x_3096_, 0, v___x_3114_);
v___x_3116_ = v___x_3096_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v___f_3106_);
v___x_3116_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; lean_object* v_toApplicative_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3150_; 
v___x_3117_ = l_StateRefT_x27_instMonad___redArg(v___x_3116_);
v_toApplicative_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v___x_3117_, 1);
lean_dec(v_unused_3151_);
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3150_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_toApplicative_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3150_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v_toFunctor_3122_; lean_object* v_toSeq_3123_; lean_object* v_toSeqLeft_3124_; lean_object* v_toSeqRight_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3148_; 
v_toFunctor_3122_ = lean_ctor_get(v_toApplicative_3118_, 0);
v_toSeq_3123_ = lean_ctor_get(v_toApplicative_3118_, 2);
v_toSeqLeft_3124_ = lean_ctor_get(v_toApplicative_3118_, 3);
v_toSeqRight_3125_ = lean_ctor_get(v_toApplicative_3118_, 4);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_toApplicative_3118_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; 
v_unused_3149_ = lean_ctor_get(v_toApplicative_3118_, 1);
lean_dec(v_unused_3149_);
v___x_3127_ = v_toApplicative_3118_;
v_isShared_3128_ = v_isSharedCheck_3148_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_toSeqRight_3125_);
lean_inc(v_toSeqLeft_3124_);
lean_inc(v_toSeq_3123_);
lean_inc(v_toFunctor_3122_);
lean_dec(v_toApplicative_3118_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3148_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___f_3129_; lean_object* v___f_3130_; lean_object* v___f_3131_; lean_object* v___f_3132_; lean_object* v___f_3133_; lean_object* v___x_3134_; lean_object* v___f_3135_; lean_object* v___f_3136_; lean_object* v___f_3137_; lean_object* v___x_3139_; 
v___f_3129_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3130_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3131_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3122_);
v___f_3132_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3132_, 0, v_toFunctor_3122_);
v___f_3133_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3133_, 0, v_toFunctor_3122_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___f_3132_);
lean_ctor_set(v___x_3134_, 1, v___f_3133_);
v___f_3135_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3135_, 0, v_toSeqRight_3125_);
v___f_3136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3136_, 0, v_toSeqLeft_3124_);
v___f_3137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3137_, 0, v_toSeq_3123_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 4, v___f_3135_);
lean_ctor_set(v___x_3127_, 3, v___f_3136_);
lean_ctor_set(v___x_3127_, 2, v___f_3137_);
lean_ctor_set(v___x_3127_, 1, v___f_3130_);
lean_ctor_set(v___x_3127_, 0, v___x_3134_);
v___x_3139_ = v___x_3127_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v___f_3130_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v___f_3137_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v___f_3136_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v___f_3135_);
v___x_3139_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3141_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v___f_3131_);
lean_ctor_set(v___x_3120_, 0, v___x_3139_);
v___x_3141_ = v___x_3120_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___f_3131_);
v___x_3141_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
size_t v_sz_3142_; size_t v___x_3143_; lean_object* v___x_127__overap_3144_; lean_object* v___x_3145_; 
v_sz_3142_ = lean_array_size(v_a_3087_);
v___x_3143_ = ((size_t)0ULL);
v___x_127__overap_3144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3141_, v___f_3129_, v_sz_3142_, v___x_3143_, v_a_3087_);
lean_inc(v_a_3091_);
lean_inc_ref(v_a_3090_);
lean_inc(v_a_3089_);
lean_inc_ref(v_a_3088_);
v___x_3145_ = lean_apply_5(v___x_127__overap_3144_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, lean_box(0));
return v___x_3145_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___boxed(lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg(v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
lean_dec(v_a_3162_);
lean_dec_ref(v_a_3161_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames(uint8_t v_pu_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v___x_3172_; lean_object* v_toApplicative_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3235_; 
v___x_3172_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3173_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3235_ == 0)
{
lean_object* v_unused_3236_; 
v_unused_3236_ = lean_ctor_get(v___x_3172_, 1);
lean_dec(v_unused_3236_);
v___x_3175_ = v___x_3172_;
v_isShared_3176_ = v_isSharedCheck_3235_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_toApplicative_3173_);
lean_dec(v___x_3172_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3235_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v_toFunctor_3177_; lean_object* v_toSeq_3178_; lean_object* v_toSeqLeft_3179_; lean_object* v_toSeqRight_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3233_; 
v_toFunctor_3177_ = lean_ctor_get(v_toApplicative_3173_, 0);
v_toSeq_3178_ = lean_ctor_get(v_toApplicative_3173_, 2);
v_toSeqLeft_3179_ = lean_ctor_get(v_toApplicative_3173_, 3);
v_toSeqRight_3180_ = lean_ctor_get(v_toApplicative_3173_, 4);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_toApplicative_3173_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; 
v_unused_3234_ = lean_ctor_get(v_toApplicative_3173_, 1);
lean_dec(v_unused_3234_);
v___x_3182_ = v_toApplicative_3173_;
v_isShared_3183_ = v_isSharedCheck_3233_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_toSeqRight_3180_);
lean_inc(v_toSeqLeft_3179_);
lean_inc(v_toSeq_3178_);
lean_inc(v_toFunctor_3177_);
lean_dec(v_toApplicative_3173_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3233_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___f_3184_; lean_object* v___f_3185_; lean_object* v___f_3186_; lean_object* v___f_3187_; lean_object* v___x_3188_; lean_object* v___f_3189_; lean_object* v___f_3190_; lean_object* v___f_3191_; lean_object* v___x_3193_; 
v___f_3184_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3185_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref(v_toFunctor_3177_);
v___f_3186_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3186_, 0, v_toFunctor_3177_);
v___f_3187_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3187_, 0, v_toFunctor_3177_);
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___f_3186_);
lean_ctor_set(v___x_3188_, 1, v___f_3187_);
v___f_3189_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3189_, 0, v_toSeqRight_3180_);
v___f_3190_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3190_, 0, v_toSeqLeft_3179_);
v___f_3191_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3191_, 0, v_toSeq_3178_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 4, v___f_3189_);
lean_ctor_set(v___x_3182_, 3, v___f_3190_);
lean_ctor_set(v___x_3182_, 2, v___f_3191_);
lean_ctor_set(v___x_3182_, 1, v___f_3184_);
lean_ctor_set(v___x_3182_, 0, v___x_3188_);
v___x_3193_ = v___x_3182_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v___f_3184_);
lean_ctor_set(v_reuseFailAlloc_3232_, 2, v___f_3191_);
lean_ctor_set(v_reuseFailAlloc_3232_, 3, v___f_3190_);
lean_ctor_set(v_reuseFailAlloc_3232_, 4, v___f_3189_);
v___x_3193_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3195_; 
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 1, v___f_3185_);
lean_ctor_set(v___x_3175_, 0, v___x_3193_);
v___x_3195_ = v___x_3175_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___f_3185_);
v___x_3195_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3196_; lean_object* v_toApplicative_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3229_; 
v___x_3196_ = l_StateRefT_x27_instMonad___redArg(v___x_3195_);
v_toApplicative_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v___x_3196_, 1);
lean_dec(v_unused_3230_);
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3229_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_toApplicative_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3229_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v_toFunctor_3201_; lean_object* v_toSeq_3202_; lean_object* v_toSeqLeft_3203_; lean_object* v_toSeqRight_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3227_; 
v_toFunctor_3201_ = lean_ctor_get(v_toApplicative_3197_, 0);
v_toSeq_3202_ = lean_ctor_get(v_toApplicative_3197_, 2);
v_toSeqLeft_3203_ = lean_ctor_get(v_toApplicative_3197_, 3);
v_toSeqRight_3204_ = lean_ctor_get(v_toApplicative_3197_, 4);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_toApplicative_3197_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v_toApplicative_3197_, 1);
lean_dec(v_unused_3228_);
v___x_3206_ = v_toApplicative_3197_;
v_isShared_3207_ = v_isSharedCheck_3227_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_toSeqRight_3204_);
lean_inc(v_toSeqLeft_3203_);
lean_inc(v_toSeq_3202_);
lean_inc(v_toFunctor_3201_);
lean_dec(v_toApplicative_3197_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3227_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___f_3208_; lean_object* v___f_3209_; lean_object* v___f_3210_; lean_object* v___f_3211_; lean_object* v___f_3212_; lean_object* v___x_3213_; lean_object* v___f_3214_; lean_object* v___f_3215_; lean_object* v___f_3216_; lean_object* v___x_3218_; 
v___f_3208_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3209_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3210_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3201_);
v___f_3211_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3211_, 0, v_toFunctor_3201_);
v___f_3212_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3212_, 0, v_toFunctor_3201_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___f_3211_);
lean_ctor_set(v___x_3213_, 1, v___f_3212_);
v___f_3214_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3214_, 0, v_toSeqRight_3204_);
v___f_3215_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3215_, 0, v_toSeqLeft_3203_);
v___f_3216_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3216_, 0, v_toSeq_3202_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 4, v___f_3214_);
lean_ctor_set(v___x_3206_, 3, v___f_3215_);
lean_ctor_set(v___x_3206_, 2, v___f_3216_);
lean_ctor_set(v___x_3206_, 1, v___f_3209_);
lean_ctor_set(v___x_3206_, 0, v___x_3213_);
v___x_3218_ = v___x_3206_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___f_3209_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v___f_3216_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v___f_3215_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v___f_3214_);
v___x_3218_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3220_; 
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 1, v___f_3210_);
lean_ctor_set(v___x_3199_, 0, v___x_3218_);
v___x_3220_ = v___x_3199_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3218_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v___f_3210_);
v___x_3220_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
size_t v_sz_3221_; size_t v___x_3222_; lean_object* v___x_185__overap_3223_; lean_object* v___x_3224_; 
v_sz_3221_ = lean_array_size(v_a_3166_);
v___x_3222_ = ((size_t)0ULL);
v___x_185__overap_3223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3220_, v___f_3208_, v_sz_3221_, v___x_3222_, v_a_3166_);
lean_inc(v_a_3170_);
lean_inc_ref(v_a_3169_);
lean_inc(v_a_3168_);
lean_inc_ref(v_a_3167_);
v___x_3224_ = lean_apply_5(v___x_185__overap_3223_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, lean_box(0));
return v___x_3224_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___boxed(lean_object* v_pu_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
uint8_t v_pu_boxed_3244_; lean_object* v_res_3245_; 
v_pu_boxed_3244_ = lean_unbox(v_pu_3237_);
v_res_3245_ = l_Lean_Compiler_LCNF_Probe_declNames(v_pu_boxed_3244_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
lean_dec(v_a_3242_);
lean_dec_ref(v_a_3241_);
lean_dec(v_a_3240_);
lean_dec_ref(v_a_3239_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(lean_object* v_inst_3246_, lean_object* v_x_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = lean_apply_1(v_inst_3246_, v_x_3247_);
v___x_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed(lean_object* v_inst_3255_, lean_object* v_x_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(v_inst_3255_, v_x_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg(lean_object* v_inst_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_){
_start:
{
lean_object* v___x_3270_; lean_object* v_toApplicative_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3333_; 
v___x_3270_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3333_ == 0)
{
lean_object* v_unused_3334_; 
v_unused_3334_ = lean_ctor_get(v___x_3270_, 1);
lean_dec(v_unused_3334_);
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3333_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_toApplicative_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3333_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v_toFunctor_3275_; lean_object* v_toSeq_3276_; lean_object* v_toSeqLeft_3277_; lean_object* v_toSeqRight_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3331_; 
v_toFunctor_3275_ = lean_ctor_get(v_toApplicative_3271_, 0);
v_toSeq_3276_ = lean_ctor_get(v_toApplicative_3271_, 2);
v_toSeqLeft_3277_ = lean_ctor_get(v_toApplicative_3271_, 3);
v_toSeqRight_3278_ = lean_ctor_get(v_toApplicative_3271_, 4);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_toApplicative_3271_);
if (v_isSharedCheck_3331_ == 0)
{
lean_object* v_unused_3332_; 
v_unused_3332_ = lean_ctor_get(v_toApplicative_3271_, 1);
lean_dec(v_unused_3332_);
v___x_3280_ = v_toApplicative_3271_;
v_isShared_3281_ = v_isSharedCheck_3331_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_toSeqRight_3278_);
lean_inc(v_toSeqLeft_3277_);
lean_inc(v_toSeq_3276_);
lean_inc(v_toFunctor_3275_);
lean_dec(v_toApplicative_3271_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3331_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___f_3282_; lean_object* v___f_3283_; lean_object* v___f_3284_; lean_object* v___f_3285_; lean_object* v___x_3286_; lean_object* v___f_3287_; lean_object* v___f_3288_; lean_object* v___f_3289_; lean_object* v___x_3291_; 
v___f_3282_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3283_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref(v_toFunctor_3275_);
v___f_3284_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3284_, 0, v_toFunctor_3275_);
v___f_3285_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3285_, 0, v_toFunctor_3275_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___f_3284_);
lean_ctor_set(v___x_3286_, 1, v___f_3285_);
v___f_3287_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3287_, 0, v_toSeqRight_3278_);
v___f_3288_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3288_, 0, v_toSeqLeft_3277_);
v___f_3289_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3289_, 0, v_toSeq_3276_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 4, v___f_3287_);
lean_ctor_set(v___x_3280_, 3, v___f_3288_);
lean_ctor_set(v___x_3280_, 2, v___f_3289_);
lean_ctor_set(v___x_3280_, 1, v___f_3282_);
lean_ctor_set(v___x_3280_, 0, v___x_3286_);
v___x_3291_ = v___x_3280_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3286_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v___f_3282_);
lean_ctor_set(v_reuseFailAlloc_3330_, 2, v___f_3289_);
lean_ctor_set(v_reuseFailAlloc_3330_, 3, v___f_3288_);
lean_ctor_set(v_reuseFailAlloc_3330_, 4, v___f_3287_);
v___x_3291_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3293_; 
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 1, v___f_3283_);
lean_ctor_set(v___x_3273_, 0, v___x_3291_);
v___x_3293_ = v___x_3273_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v___f_3283_);
v___x_3293_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
lean_object* v___x_3294_; lean_object* v_toApplicative_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3327_; 
v___x_3294_ = l_StateRefT_x27_instMonad___redArg(v___x_3293_);
v_toApplicative_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3327_ == 0)
{
lean_object* v_unused_3328_; 
v_unused_3328_ = lean_ctor_get(v___x_3294_, 1);
lean_dec(v_unused_3328_);
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3327_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_toApplicative_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3327_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_toFunctor_3299_; lean_object* v_toSeq_3300_; lean_object* v_toSeqLeft_3301_; lean_object* v_toSeqRight_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3325_; 
v_toFunctor_3299_ = lean_ctor_get(v_toApplicative_3295_, 0);
v_toSeq_3300_ = lean_ctor_get(v_toApplicative_3295_, 2);
v_toSeqLeft_3301_ = lean_ctor_get(v_toApplicative_3295_, 3);
v_toSeqRight_3302_ = lean_ctor_get(v_toApplicative_3295_, 4);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_toApplicative_3295_);
if (v_isSharedCheck_3325_ == 0)
{
lean_object* v_unused_3326_; 
v_unused_3326_ = lean_ctor_get(v_toApplicative_3295_, 1);
lean_dec(v_unused_3326_);
v___x_3304_ = v_toApplicative_3295_;
v_isShared_3305_ = v_isSharedCheck_3325_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_toSeqRight_3302_);
lean_inc(v_toSeqLeft_3301_);
lean_inc(v_toSeq_3300_);
lean_inc(v_toFunctor_3299_);
lean_dec(v_toApplicative_3295_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3325_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___f_3306_; lean_object* v___f_3307_; lean_object* v___f_3308_; lean_object* v___f_3309_; lean_object* v___f_3310_; lean_object* v___x_3311_; lean_object* v___f_3312_; lean_object* v___f_3313_; lean_object* v___f_3314_; lean_object* v___x_3316_; 
v___f_3306_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3306_, 0, v_inst_3263_);
v___f_3307_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3308_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3299_);
v___f_3309_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3309_, 0, v_toFunctor_3299_);
v___f_3310_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3310_, 0, v_toFunctor_3299_);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___f_3309_);
lean_ctor_set(v___x_3311_, 1, v___f_3310_);
v___f_3312_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3312_, 0, v_toSeqRight_3302_);
v___f_3313_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3313_, 0, v_toSeqLeft_3301_);
v___f_3314_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3314_, 0, v_toSeq_3300_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 4, v___f_3312_);
lean_ctor_set(v___x_3304_, 3, v___f_3313_);
lean_ctor_set(v___x_3304_, 2, v___f_3314_);
lean_ctor_set(v___x_3304_, 1, v___f_3307_);
lean_ctor_set(v___x_3304_, 0, v___x_3311_);
v___x_3316_ = v___x_3304_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___f_3307_);
lean_ctor_set(v_reuseFailAlloc_3324_, 2, v___f_3314_);
lean_ctor_set(v_reuseFailAlloc_3324_, 3, v___f_3313_);
lean_ctor_set(v_reuseFailAlloc_3324_, 4, v___f_3312_);
v___x_3316_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3318_; 
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 1, v___f_3308_);
lean_ctor_set(v___x_3297_, 0, v___x_3316_);
v___x_3318_ = v___x_3297_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v___f_3308_);
v___x_3318_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
size_t v_sz_3319_; size_t v___x_3320_; lean_object* v___x_129__overap_3321_; lean_object* v___x_3322_; 
v_sz_3319_ = lean_array_size(v_a_3264_);
v___x_3320_ = ((size_t)0ULL);
v___x_129__overap_3321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3318_, v___f_3306_, v_sz_3319_, v___x_3320_, v_a_3264_);
lean_inc(v_a_3268_);
lean_inc_ref(v_a_3267_);
lean_inc(v_a_3266_);
lean_inc_ref(v_a_3265_);
v___x_3322_ = lean_apply_5(v___x_129__overap_3321_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, lean_box(0));
return v___x_3322_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___boxed(lean_object* v_inst_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Compiler_LCNF_Probe_toString___redArg(v_inst_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString(lean_object* v_00_u03b1_3343_, lean_object* v_inst_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v___x_3351_; lean_object* v_toApplicative_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3414_; 
v___x_3351_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; 
v_unused_3415_ = lean_ctor_get(v___x_3351_, 1);
lean_dec(v_unused_3415_);
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3414_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_toApplicative_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3414_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v_toFunctor_3356_; lean_object* v_toSeq_3357_; lean_object* v_toSeqLeft_3358_; lean_object* v_toSeqRight_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3412_; 
v_toFunctor_3356_ = lean_ctor_get(v_toApplicative_3352_, 0);
v_toSeq_3357_ = lean_ctor_get(v_toApplicative_3352_, 2);
v_toSeqLeft_3358_ = lean_ctor_get(v_toApplicative_3352_, 3);
v_toSeqRight_3359_ = lean_ctor_get(v_toApplicative_3352_, 4);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_toApplicative_3352_);
if (v_isSharedCheck_3412_ == 0)
{
lean_object* v_unused_3413_; 
v_unused_3413_ = lean_ctor_get(v_toApplicative_3352_, 1);
lean_dec(v_unused_3413_);
v___x_3361_ = v_toApplicative_3352_;
v_isShared_3362_ = v_isSharedCheck_3412_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_toSeqRight_3359_);
lean_inc(v_toSeqLeft_3358_);
lean_inc(v_toSeq_3357_);
lean_inc(v_toFunctor_3356_);
lean_dec(v_toApplicative_3352_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3412_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___f_3363_; lean_object* v___f_3364_; lean_object* v___f_3365_; lean_object* v___f_3366_; lean_object* v___x_3367_; lean_object* v___f_3368_; lean_object* v___f_3369_; lean_object* v___f_3370_; lean_object* v___x_3372_; 
v___f_3363_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3364_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref(v_toFunctor_3356_);
v___f_3365_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3365_, 0, v_toFunctor_3356_);
v___f_3366_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3366_, 0, v_toFunctor_3356_);
v___x_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___f_3365_);
lean_ctor_set(v___x_3367_, 1, v___f_3366_);
v___f_3368_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3368_, 0, v_toSeqRight_3359_);
v___f_3369_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3369_, 0, v_toSeqLeft_3358_);
v___f_3370_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3370_, 0, v_toSeq_3357_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 4, v___f_3368_);
lean_ctor_set(v___x_3361_, 3, v___f_3369_);
lean_ctor_set(v___x_3361_, 2, v___f_3370_);
lean_ctor_set(v___x_3361_, 1, v___f_3363_);
lean_ctor_set(v___x_3361_, 0, v___x_3367_);
v___x_3372_ = v___x_3361_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v___f_3363_);
lean_ctor_set(v_reuseFailAlloc_3411_, 2, v___f_3370_);
lean_ctor_set(v_reuseFailAlloc_3411_, 3, v___f_3369_);
lean_ctor_set(v_reuseFailAlloc_3411_, 4, v___f_3368_);
v___x_3372_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3374_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 1, v___f_3364_);
lean_ctor_set(v___x_3354_, 0, v___x_3372_);
v___x_3374_ = v___x_3354_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v___f_3364_);
v___x_3374_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; lean_object* v_toApplicative_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3408_; 
v___x_3375_ = l_StateRefT_x27_instMonad___redArg(v___x_3374_);
v_toApplicative_3376_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; 
v_unused_3409_ = lean_ctor_get(v___x_3375_, 1);
lean_dec(v_unused_3409_);
v___x_3378_ = v___x_3375_;
v_isShared_3379_ = v_isSharedCheck_3408_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_toApplicative_3376_);
lean_dec(v___x_3375_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3408_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v_toFunctor_3380_; lean_object* v_toSeq_3381_; lean_object* v_toSeqLeft_3382_; lean_object* v_toSeqRight_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3406_; 
v_toFunctor_3380_ = lean_ctor_get(v_toApplicative_3376_, 0);
v_toSeq_3381_ = lean_ctor_get(v_toApplicative_3376_, 2);
v_toSeqLeft_3382_ = lean_ctor_get(v_toApplicative_3376_, 3);
v_toSeqRight_3383_ = lean_ctor_get(v_toApplicative_3376_, 4);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_toApplicative_3376_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; 
v_unused_3407_ = lean_ctor_get(v_toApplicative_3376_, 1);
lean_dec(v_unused_3407_);
v___x_3385_ = v_toApplicative_3376_;
v_isShared_3386_ = v_isSharedCheck_3406_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_toSeqRight_3383_);
lean_inc(v_toSeqLeft_3382_);
lean_inc(v_toSeq_3381_);
lean_inc(v_toFunctor_3380_);
lean_dec(v_toApplicative_3376_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3406_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___f_3387_; lean_object* v___f_3388_; lean_object* v___f_3389_; lean_object* v___f_3390_; lean_object* v___f_3391_; lean_object* v___x_3392_; lean_object* v___f_3393_; lean_object* v___f_3394_; lean_object* v___f_3395_; lean_object* v___x_3397_; 
v___f_3387_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3387_, 0, v_inst_3344_);
v___f_3388_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3389_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3380_);
v___f_3390_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3390_, 0, v_toFunctor_3380_);
v___f_3391_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3391_, 0, v_toFunctor_3380_);
v___x_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___f_3390_);
lean_ctor_set(v___x_3392_, 1, v___f_3391_);
v___f_3393_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3393_, 0, v_toSeqRight_3383_);
v___f_3394_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3394_, 0, v_toSeqLeft_3382_);
v___f_3395_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3395_, 0, v_toSeq_3381_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 4, v___f_3393_);
lean_ctor_set(v___x_3385_, 3, v___f_3394_);
lean_ctor_set(v___x_3385_, 2, v___f_3395_);
lean_ctor_set(v___x_3385_, 1, v___f_3388_);
lean_ctor_set(v___x_3385_, 0, v___x_3392_);
v___x_3397_ = v___x_3385_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v___f_3388_);
lean_ctor_set(v_reuseFailAlloc_3405_, 2, v___f_3395_);
lean_ctor_set(v_reuseFailAlloc_3405_, 3, v___f_3394_);
lean_ctor_set(v_reuseFailAlloc_3405_, 4, v___f_3393_);
v___x_3397_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3399_; 
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 1, v___f_3389_);
lean_ctor_set(v___x_3378_, 0, v___x_3397_);
v___x_3399_ = v___x_3378_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v___f_3389_);
v___x_3399_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
size_t v_sz_3400_; size_t v___x_3401_; lean_object* v___x_190__overap_3402_; lean_object* v___x_3403_; 
v_sz_3400_ = lean_array_size(v_a_3345_);
v___x_3401_ = ((size_t)0ULL);
v___x_190__overap_3402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3399_, v___f_3387_, v_sz_3400_, v___x_3401_, v_a_3345_);
lean_inc(v_a_3349_);
lean_inc_ref(v_a_3348_);
lean_inc(v_a_3347_);
lean_inc_ref(v_a_3346_);
v___x_3403_ = lean_apply_5(v___x_190__overap_3402_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, lean_box(0));
return v___x_3403_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___boxed(lean_object* v_00_u03b1_3416_, lean_object* v_inst_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Compiler_LCNF_Probe_toString(v_00_u03b1_3416_, v_inst_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg(lean_object* v_data_3425_){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3427_ = lean_array_get_size(v_data_3425_);
v___x_3428_ = lean_unsigned_to_nat(1u);
v___x_3429_ = lean_mk_empty_array_with_capacity(v___x_3428_);
v___x_3430_ = lean_array_push(v___x_3429_, v___x_3427_);
v___x_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg___boxed(lean_object* v_data_3432_, lean_object* v_a_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_Compiler_LCNF_Probe_count___redArg(v_data_3432_);
lean_dec_ref(v_data_3432_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count(lean_object* v_00_u03b1_3435_, lean_object* v_data_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3442_ = lean_array_get_size(v_data_3436_);
v___x_3443_ = lean_unsigned_to_nat(1u);
v___x_3444_ = lean_mk_empty_array_with_capacity(v___x_3443_);
v___x_3445_ = lean_array_push(v___x_3444_, v___x_3442_);
v___x_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___boxed(lean_object* v_00_u03b1_3447_, lean_object* v_data_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_Compiler_LCNF_Probe_count(v_00_u03b1_3447_, v_data_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
lean_dec(v_a_3450_);
lean_dec_ref(v_a_3449_);
lean_dec_ref(v_data_3448_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg(lean_object* v_data_3456_){
_start:
{
lean_object* v___y_3459_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v___x_3464_ = lean_unsigned_to_nat(0u);
v___x_3465_ = lean_array_get_size(v_data_3456_);
v___x_3466_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3467_ = lean_nat_dec_lt(v___x_3464_, v___x_3465_);
if (v___x_3467_ == 0)
{
lean_dec_ref(v_data_3456_);
v___y_3459_ = v___x_3464_;
goto v___jp_3458_;
}
else
{
lean_object* v___f_3468_; uint8_t v___x_3469_; 
v___f_3468_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3469_ = lean_nat_dec_le(v___x_3465_, v___x_3465_);
if (v___x_3469_ == 0)
{
if (v___x_3467_ == 0)
{
lean_dec_ref(v_data_3456_);
v___y_3459_ = v___x_3464_;
goto v___jp_3458_;
}
else
{
size_t v___x_3470_; size_t v___x_3471_; lean_object* v___x_3472_; 
v___x_3470_ = ((size_t)0ULL);
v___x_3471_ = lean_usize_of_nat(v___x_3465_);
v___x_3472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3466_, v___f_3468_, v_data_3456_, v___x_3470_, v___x_3471_, v___x_3464_);
v___y_3459_ = v___x_3472_;
goto v___jp_3458_;
}
}
else
{
size_t v___x_3473_; size_t v___x_3474_; lean_object* v___x_3475_; 
v___x_3473_ = ((size_t)0ULL);
v___x_3474_ = lean_usize_of_nat(v___x_3465_);
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3466_, v___f_3468_, v_data_3456_, v___x_3473_, v___x_3474_, v___x_3464_);
v___y_3459_ = v___x_3475_;
goto v___jp_3458_;
}
}
v___jp_3458_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3460_ = lean_unsigned_to_nat(1u);
v___x_3461_ = lean_mk_empty_array_with_capacity(v___x_3460_);
v___x_3462_ = lean_array_push(v___x_3461_, v___y_3459_);
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
return v___x_3463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg___boxed(lean_object* v_data_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_Compiler_LCNF_Probe_sum___redArg(v_data_3476_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum(lean_object* v_data_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v___y_3486_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v___x_3491_ = lean_unsigned_to_nat(0u);
v___x_3492_ = lean_array_get_size(v_data_3479_);
v___x_3493_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3494_ = lean_nat_dec_lt(v___x_3491_, v___x_3492_);
if (v___x_3494_ == 0)
{
lean_dec_ref(v_data_3479_);
v___y_3486_ = v___x_3491_;
goto v___jp_3485_;
}
else
{
lean_object* v___f_3495_; uint8_t v___x_3496_; 
v___f_3495_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3496_ = lean_nat_dec_le(v___x_3492_, v___x_3492_);
if (v___x_3496_ == 0)
{
if (v___x_3494_ == 0)
{
lean_dec_ref(v_data_3479_);
v___y_3486_ = v___x_3491_;
goto v___jp_3485_;
}
else
{
size_t v___x_3497_; size_t v___x_3498_; lean_object* v___x_3499_; 
v___x_3497_ = ((size_t)0ULL);
v___x_3498_ = lean_usize_of_nat(v___x_3492_);
v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3493_, v___f_3495_, v_data_3479_, v___x_3497_, v___x_3498_, v___x_3491_);
v___y_3486_ = v___x_3499_;
goto v___jp_3485_;
}
}
else
{
size_t v___x_3500_; size_t v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = ((size_t)0ULL);
v___x_3501_ = lean_usize_of_nat(v___x_3492_);
v___x_3502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3493_, v___f_3495_, v_data_3479_, v___x_3500_, v___x_3501_, v___x_3491_);
v___y_3486_ = v___x_3502_;
goto v___jp_3485_;
}
}
v___jp_3485_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3487_ = lean_unsigned_to_nat(1u);
v___x_3488_ = lean_mk_empty_array_with_capacity(v___x_3487_);
v___x_3489_ = lean_array_push(v___x_3488_, v___y_3486_);
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
return v___x_3490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___boxed(lean_object* v_data_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_Compiler_LCNF_Probe_sum(v_data_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg(lean_object* v_n_3510_, lean_object* v_data_3511_){
_start:
{
lean_object* v_lower_3514_; lean_object* v_upper_3515_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3519_ = lean_array_get_size(v_data_3511_);
v___x_3520_ = lean_nat_sub(v___x_3519_, v_n_3510_);
v___x_3521_ = lean_unsigned_to_nat(0u);
v___x_3522_ = lean_nat_dec_le(v___x_3520_, v___x_3521_);
if (v___x_3522_ == 0)
{
v_lower_3514_ = v___x_3520_;
v_upper_3515_ = v___x_3519_;
goto v___jp_3513_;
}
else
{
lean_dec(v___x_3520_);
v_lower_3514_ = v___x_3521_;
v_upper_3515_ = v___x_3519_;
goto v___jp_3513_;
}
v___jp_3513_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = l_Array_toSubarray___redArg(v_data_3511_, v_lower_3514_, v_upper_3515_);
v___x_3517_ = l_Subarray_copy___redArg(v___x_3516_);
v___x_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
return v___x_3518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg___boxed(lean_object* v_n_3523_, lean_object* v_data_3524_, lean_object* v_a_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_Compiler_LCNF_Probe_tail___redArg(v_n_3523_, v_data_3524_);
lean_dec(v_n_3523_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail(lean_object* v_00_u03b1_3527_, lean_object* v_n_3528_, lean_object* v_data_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v_lower_3536_; lean_object* v_upper_3537_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v___x_3541_ = lean_array_get_size(v_data_3529_);
v___x_3542_ = lean_nat_sub(v___x_3541_, v_n_3528_);
v___x_3543_ = lean_unsigned_to_nat(0u);
v___x_3544_ = lean_nat_dec_le(v___x_3542_, v___x_3543_);
if (v___x_3544_ == 0)
{
v_lower_3536_ = v___x_3542_;
v_upper_3537_ = v___x_3541_;
goto v___jp_3535_;
}
else
{
lean_dec(v___x_3542_);
v_lower_3536_ = v___x_3543_;
v_upper_3537_ = v___x_3541_;
goto v___jp_3535_;
}
v___jp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = l_Array_toSubarray___redArg(v_data_3529_, v_lower_3536_, v_upper_3537_);
v___x_3539_ = l_Subarray_copy___redArg(v___x_3538_);
v___x_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
return v___x_3540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___boxed(lean_object* v_00_u03b1_3545_, lean_object* v_n_3546_, lean_object* v_data_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_Compiler_LCNF_Probe_tail(v_00_u03b1_3545_, v_n_3546_, v_data_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
lean_dec(v_n_3546_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg(lean_object* v_n_3554_, lean_object* v_data_3555_){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3557_ = lean_unsigned_to_nat(0u);
v___x_3558_ = l_Array_toSubarray___redArg(v_data_3555_, v___x_3557_, v_n_3554_);
v___x_3559_ = l_Subarray_copy___redArg(v___x_3558_);
v___x_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg___boxed(lean_object* v_n_3561_, lean_object* v_data_3562_, lean_object* v_a_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_Compiler_LCNF_Probe_head___redArg(v_n_3561_, v_data_3562_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head(lean_object* v_00_u03b1_3565_, lean_object* v_n_3566_, lean_object* v_data_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3573_ = lean_unsigned_to_nat(0u);
v___x_3574_ = l_Array_toSubarray___redArg(v_data_3567_, v___x_3573_, v_n_3566_);
v___x_3575_ = l_Subarray_copy___redArg(v___x_3574_);
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___boxed(lean_object* v_00_u03b1_3577_, lean_object* v_n_3578_, lean_object* v_data_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_Compiler_LCNF_Probe_head(v_00_u03b1_3577_, v_n_3578_, v_data_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(lean_object* v_probe_3591_, lean_object* v___x_3592_, lean_object* v___x_3593_, lean_object* v___x_3594_, lean_object* v___x_3595_, lean_object* v___x_3596_, lean_object* v___f_3597_, lean_object* v_inst_3598_, lean_object* v_decls_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v___x_3605_; 
lean_inc(v___y_3603_);
lean_inc_ref(v___y_3602_);
lean_inc(v___y_3601_);
lean_inc_ref(v___y_3600_);
lean_inc_ref(v_decls_3599_);
v___x_3605_ = lean_apply_6(v_probe_3591_, v_decls_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, lean_box(0));
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_576__overap_3609_; lean_object* v___x_3610_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref(v___x_3605_);
v___x_3607_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0));
v___x_3608_ = l_Lean_Name_mkStr2(v___x_3607_, v___x_3592_);
lean_inc(v___x_3608_);
lean_inc_ref(v___x_3594_);
lean_inc_ref(v___x_3593_);
v___x_576__overap_3609_ = l_Lean_isTracingEnabledFor___redArg(v___x_3593_, v___x_3594_, v___x_3595_, v___x_3608_);
lean_inc(v___y_3603_);
lean_inc_ref(v___y_3602_);
lean_inc(v___y_3601_);
lean_inc_ref(v___y_3600_);
v___x_3610_ = lean_apply_5(v___x_576__overap_3609_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, lean_box(0));
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3650_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3650_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3650_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
uint8_t v___x_3615_; 
v___x_3615_ = lean_unbox(v_a_3611_);
lean_dec(v_a_3611_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3617_; 
lean_dec(v___x_3608_);
lean_dec(v_a_3606_);
lean_dec_ref(v_inst_3598_);
lean_dec(v___f_3597_);
lean_dec(v___x_3596_);
lean_dec_ref(v___x_3594_);
lean_dec_ref(v___x_3593_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v_decls_3599_);
v___x_3617_ = v___x_3613_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_decls_3599_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
else
{
lean_object* v___f_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v_toMonadRef_3624_; lean_object* v___f_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_592__overap_3632_; lean_object* v___x_3633_; 
lean_del_object(v___x_3613_);
v___f_3619_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__1));
v___x_3620_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2));
v___x_3621_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_3622_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3620_, v___x_3596_, v___x_3621_);
v___x_3623_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3619_, v___f_3597_, v___x_3622_);
v_toMonadRef_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc_ref(v_toMonadRef_3624_);
lean_dec_ref(v___x_3623_);
v___f_3625_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3));
v___x_3626_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__4));
v___x_3627_ = lean_array_to_list(v_a_3606_);
v___x_3628_ = l_List_toString___redArg(v_inst_3598_, v___x_3627_);
v___x_3629_ = lean_string_append(v___x_3626_, v___x_3628_);
lean_dec_ref(v___x_3628_);
v___x_3630_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3629_);
v___x_3631_ = l_Lean_MessageData_ofFormat(v___x_3630_);
v___x_592__overap_3632_ = l_Lean_addTrace___redArg(v___x_3593_, v___x_3594_, v_toMonadRef_3624_, v___f_3625_, v___x_3608_, v___x_3631_);
lean_inc(v___y_3603_);
lean_inc_ref(v___y_3602_);
lean_inc(v___y_3601_);
lean_inc_ref(v___y_3600_);
v___x_3633_ = lean_apply_5(v___x_592__overap_3632_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, lean_box(0));
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3640_ == 0)
{
lean_object* v_unused_3641_; 
v_unused_3641_ = lean_ctor_get(v___x_3633_, 0);
lean_dec(v_unused_3641_);
v___x_3635_ = v___x_3633_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_dec(v___x_3633_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v_decls_3599_);
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_decls_3599_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v_decls_3599_);
v_a_3642_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3633_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3633_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
lean_dec(v___x_3608_);
lean_dec(v_a_3606_);
lean_dec_ref(v_decls_3599_);
lean_dec_ref(v_inst_3598_);
lean_dec(v___f_3597_);
lean_dec(v___x_3596_);
lean_dec_ref(v___x_3594_);
lean_dec_ref(v___x_3593_);
v_a_3651_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3610_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3610_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec_ref(v_decls_3599_);
lean_dec_ref(v_inst_3598_);
lean_dec(v___f_3597_);
lean_dec(v___x_3596_);
lean_dec(v___x_3595_);
lean_dec_ref(v___x_3594_);
lean_dec_ref(v___x_3593_);
lean_dec_ref(v___x_3592_);
v_a_3659_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3605_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3605_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed(lean_object* v_probe_3667_, lean_object* v___x_3668_, lean_object* v___x_3669_, lean_object* v___x_3670_, lean_object* v___x_3671_, lean_object* v___x_3672_, lean_object* v___f_3673_, lean_object* v_inst_3674_, lean_object* v_decls_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(v_probe_3667_, v___x_3668_, v___x_3669_, v___x_3670_, v___x_3671_, v___x_3672_, v___f_3673_, v_inst_3674_, v_decls_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
return v_res_3681_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2(void){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3684_ = l_Lean_Core_instMonadTraceCoreM;
v___x_3685_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3686_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3685_, v___x_3684_);
return v___x_3686_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3(void){
_start:
{
lean_object* v___x_3687_; lean_object* v___f_3688_; lean_object* v___x_3689_; 
v___x_3687_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2);
v___f_3688_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___x_3689_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3688_, v___x_3687_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg(lean_object* v_inst_3698_, uint8_t v_phase_3699_, lean_object* v_probe_3700_){
_start:
{
lean_object* v___x_3701_; lean_object* v_toApplicative_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3769_; 
v___x_3701_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3769_ == 0)
{
lean_object* v_unused_3770_; 
v_unused_3770_ = lean_ctor_get(v___x_3701_, 1);
lean_dec(v_unused_3770_);
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3769_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_toApplicative_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3769_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v_toFunctor_3706_; lean_object* v_toSeq_3707_; lean_object* v_toSeqLeft_3708_; lean_object* v_toSeqRight_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3767_; 
v_toFunctor_3706_ = lean_ctor_get(v_toApplicative_3702_, 0);
v_toSeq_3707_ = lean_ctor_get(v_toApplicative_3702_, 2);
v_toSeqLeft_3708_ = lean_ctor_get(v_toApplicative_3702_, 3);
v_toSeqRight_3709_ = lean_ctor_get(v_toApplicative_3702_, 4);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_toApplicative_3702_);
if (v_isSharedCheck_3767_ == 0)
{
lean_object* v_unused_3768_; 
v_unused_3768_ = lean_ctor_get(v_toApplicative_3702_, 1);
lean_dec(v_unused_3768_);
v___x_3711_ = v_toApplicative_3702_;
v_isShared_3712_ = v_isSharedCheck_3767_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_toSeqRight_3709_);
lean_inc(v_toSeqLeft_3708_);
lean_inc(v_toSeq_3707_);
lean_inc(v_toFunctor_3706_);
lean_dec(v_toApplicative_3702_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3767_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___f_3713_; lean_object* v___f_3714_; lean_object* v___f_3715_; lean_object* v___f_3716_; lean_object* v___x_3717_; lean_object* v___f_3718_; lean_object* v___f_3719_; lean_object* v___f_3720_; lean_object* v___x_3722_; 
v___f_3713_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3714_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref(v_toFunctor_3706_);
v___f_3715_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3715_, 0, v_toFunctor_3706_);
v___f_3716_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3716_, 0, v_toFunctor_3706_);
v___x_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___f_3715_);
lean_ctor_set(v___x_3717_, 1, v___f_3716_);
v___f_3718_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3718_, 0, v_toSeqRight_3709_);
v___f_3719_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3719_, 0, v_toSeqLeft_3708_);
v___f_3720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3720_, 0, v_toSeq_3707_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 4, v___f_3718_);
lean_ctor_set(v___x_3711_, 3, v___f_3719_);
lean_ctor_set(v___x_3711_, 2, v___f_3720_);
lean_ctor_set(v___x_3711_, 1, v___f_3713_);
lean_ctor_set(v___x_3711_, 0, v___x_3717_);
v___x_3722_ = v___x_3711_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3766_, 1, v___f_3713_);
lean_ctor_set(v_reuseFailAlloc_3766_, 2, v___f_3720_);
lean_ctor_set(v_reuseFailAlloc_3766_, 3, v___f_3719_);
lean_ctor_set(v_reuseFailAlloc_3766_, 4, v___f_3718_);
v___x_3722_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3724_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 1, v___f_3714_);
lean_ctor_set(v___x_3704_, 0, v___x_3722_);
v___x_3724_ = v___x_3704_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v___f_3714_);
v___x_3724_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; lean_object* v_toApplicative_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3763_; 
v___x_3725_ = l_StateRefT_x27_instMonad___redArg(v___x_3724_);
v_toApplicative_3726_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; 
v_unused_3764_ = lean_ctor_get(v___x_3725_, 1);
lean_dec(v_unused_3764_);
v___x_3728_ = v___x_3725_;
v_isShared_3729_ = v_isSharedCheck_3763_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_toApplicative_3726_);
lean_dec(v___x_3725_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3763_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v_toFunctor_3730_; lean_object* v_toSeq_3731_; lean_object* v_toSeqLeft_3732_; lean_object* v_toSeqRight_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3761_; 
v_toFunctor_3730_ = lean_ctor_get(v_toApplicative_3726_, 0);
v_toSeq_3731_ = lean_ctor_get(v_toApplicative_3726_, 2);
v_toSeqLeft_3732_ = lean_ctor_get(v_toApplicative_3726_, 3);
v_toSeqRight_3733_ = lean_ctor_get(v_toApplicative_3726_, 4);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_toApplicative_3726_);
if (v_isSharedCheck_3761_ == 0)
{
lean_object* v_unused_3762_; 
v_unused_3762_ = lean_ctor_get(v_toApplicative_3726_, 1);
lean_dec(v_unused_3762_);
v___x_3735_ = v_toApplicative_3726_;
v_isShared_3736_ = v_isSharedCheck_3761_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_toSeqRight_3733_);
lean_inc(v_toSeqLeft_3732_);
lean_inc(v_toSeq_3731_);
lean_inc(v_toFunctor_3730_);
lean_dec(v_toApplicative_3726_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3761_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___f_3737_; lean_object* v___f_3738_; lean_object* v___f_3739_; lean_object* v___f_3740_; lean_object* v___x_3741_; lean_object* v___f_3742_; lean_object* v___f_3743_; lean_object* v___f_3744_; lean_object* v___x_3746_; 
v___f_3737_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3738_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3730_);
v___f_3739_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3739_, 0, v_toFunctor_3730_);
v___f_3740_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3740_, 0, v_toFunctor_3730_);
v___x_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___f_3739_);
lean_ctor_set(v___x_3741_, 1, v___f_3740_);
v___f_3742_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3742_, 0, v_toSeqRight_3733_);
v___f_3743_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3743_, 0, v_toSeqLeft_3732_);
v___f_3744_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3744_, 0, v_toSeq_3731_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 4, v___f_3742_);
lean_ctor_set(v___x_3735_, 3, v___f_3743_);
lean_ctor_set(v___x_3735_, 2, v___f_3744_);
lean_ctor_set(v___x_3735_, 1, v___f_3737_);
lean_ctor_set(v___x_3735_, 0, v___x_3741_);
v___x_3746_ = v___x_3735_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v___f_3737_);
lean_ctor_set(v_reuseFailAlloc_3760_, 2, v___f_3744_);
lean_ctor_set(v_reuseFailAlloc_3760_, 3, v___f_3743_);
lean_ctor_set(v_reuseFailAlloc_3760_, 4, v___f_3742_);
v___x_3746_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 1, v___f_3738_);
lean_ctor_set(v___x_3728_, 0, v___x_3746_);
v___x_3748_ = v___x_3728_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3759_, 1, v___f_3738_);
v___x_3748_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___f_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; uint8_t v___x_3754_; lean_object* v___x_3755_; lean_object* v___f_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___f_3749_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___x_3750_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3751_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3);
v___x_3752_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6));
v___x_3753_ = lean_unsigned_to_nat(0u);
v___x_3754_ = 0;
v___x_3755_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7));
v___f_3756_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_3756_, 0, v_probe_3700_);
lean_closure_set(v___f_3756_, 1, v___x_3755_);
lean_closure_set(v___f_3756_, 2, v___x_3748_);
lean_closure_set(v___f_3756_, 3, v___x_3751_);
lean_closure_set(v___f_3756_, 4, v___x_3752_);
lean_closure_set(v___f_3756_, 5, v___x_3750_);
lean_closure_set(v___f_3756_, 6, v___f_3749_);
lean_closure_set(v___f_3756_, 7, v_inst_3698_);
v___x_3757_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8));
v___x_3758_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3758_, 0, v___x_3753_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
lean_ctor_set(v___x_3758_, 2, v___f_3756_);
lean_ctor_set_uint8(v___x_3758_, sizeof(void*)*3, v_phase_3699_);
lean_ctor_set_uint8(v___x_3758_, sizeof(void*)*3 + 1, v_phase_3699_);
lean_ctor_set_uint8(v___x_3758_, sizeof(void*)*3 + 2, v___x_3754_);
return v___x_3758_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(lean_object* v_inst_3771_, lean_object* v_phase_3772_, lean_object* v_probe_3773_){
_start:
{
uint8_t v_phase_boxed_3774_; lean_object* v_res_3775_; 
v_phase_boxed_3774_ = lean_unbox(v_phase_3772_);
v_res_3775_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3771_, v_phase_boxed_3774_, v_probe_3773_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass(lean_object* v_00_u03b2_3776_, lean_object* v_inst_3777_, uint8_t v_phase_3778_, lean_object* v_probe_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3777_, v_phase_3778_, v_probe_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___boxed(lean_object* v_00_u03b2_3781_, lean_object* v_inst_3782_, lean_object* v_phase_3783_, lean_object* v_probe_3784_){
_start:
{
uint8_t v_phase_boxed_3785_; lean_object* v_res_3786_; 
v_phase_boxed_3785_ = lean_unbox(v_phase_3783_);
v_res_3786_ = l_Lean_Compiler_LCNF_Probe_toPass(v_00_u03b2_3781_, v_inst_3782_, v_phase_boxed_3785_, v_probe_3784_);
return v_res_3786_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3845_ = lean_unsigned_to_nat(4008565020u);
v___x_3846_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3847_ = l_Lean_Name_num___override(v___x_3846_, v___x_3845_);
return v___x_3847_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3849_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3850_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3851_ = l_Lean_Name_str___override(v___x_3850_, v___x_3849_);
return v___x_3851_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3853_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3854_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3855_ = l_Lean_Name_str___override(v___x_3854_, v___x_3853_);
return v___x_3855_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3856_ = lean_unsigned_to_nat(2u);
v___x_3857_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3858_ = l_Lean_Name_num___override(v___x_3857_, v___x_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3860_; uint8_t v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3860_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3861_ = 1;
v___x_3862_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3863_ = l_Lean_registerTraceClass(v___x_3860_, v___x_3861_, v___x_3862_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2____boxed(lean_object* v_a_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
return v_res_3865_;
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
