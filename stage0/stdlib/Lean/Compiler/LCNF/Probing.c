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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
lean_object* l_StateRefT_x27_instMonadFunctor___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadFunctor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3;
static const lean_closure_object l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
v___x_1_ = l_instMonadEIO___redArg();
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
lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg(lean_object* v_f_8_, lean_object* v_data_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_map___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_8_ = stack[0].m_obj;
lean_object* v_data_9_ = stack[1].m_obj;
lean_object* v_a_10_ = stack[2].m_obj;
lean_object* v_a_11_ = stack[3].m_obj;
lean_object* v_a_12_ = stack[4].m_obj;
lean_object* v_a_13_ = stack[5].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_Compiler_LCNF_Probe_map___redArg(v_f_8_, v_data_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map___redArg___boxed(lean_object* v_f_66_, lean_object* v_data_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Compiler_LCNF_Probe_map___redArg(v_f_66_, v_data_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
lean_dec_ref(v_a_68_);
return v_res_73_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_map(lean_object* v_00_u03b1_74_, lean_object* v_00_u03b2_75_, lean_object* v_f_76_, lean_object* v_data_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_83_; lean_object* v_toApplicative_84_; lean_object* v_toFunctor_85_; lean_object* v_toSeq_86_; lean_object* v_toSeqLeft_87_; lean_object* v_toSeqRight_88_; lean_object* v___f_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_toApplicative_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_131_; 
v___x_83_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_84_ = lean_ctor_get(v___x_83_, 0);
v_toFunctor_85_ = lean_ctor_get(v_toApplicative_84_, 0);
v_toSeq_86_ = lean_ctor_get(v_toApplicative_84_, 2);
v_toSeqLeft_87_ = lean_ctor_get(v_toApplicative_84_, 3);
v_toSeqRight_88_ = lean_ctor_get(v_toApplicative_84_, 4);
v___f_89_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_90_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_85_, 2);
v___f_91_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_91_, 0, v_toFunctor_85_);
v___f_92_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_92_, 0, v_toFunctor_85_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v___f_91_);
lean_ctor_set(v___x_93_, 1, v___f_92_);
lean_inc(v_toSeqRight_88_);
v___f_94_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_94_, 0, v_toSeqRight_88_);
lean_inc(v_toSeqLeft_87_);
v___f_95_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_95_, 0, v_toSeqLeft_87_);
lean_inc(v_toSeq_86_);
v___f_96_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_96_, 0, v_toSeq_86_);
v___x_97_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_97_, 0, v___x_93_);
lean_ctor_set(v___x_97_, 1, v___f_89_);
lean_ctor_set(v___x_97_, 2, v___f_96_);
lean_ctor_set(v___x_97_, 3, v___f_95_);
lean_ctor_set(v___x_97_, 4, v___f_94_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___f_90_);
v___x_99_ = l_StateRefT_x27_instMonad___redArg(v___x_98_);
v_toApplicative_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v___x_99_, 1);
lean_dec(v_unused_132_);
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_131_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_toApplicative_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_131_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_toFunctor_104_; lean_object* v_toSeq_105_; lean_object* v_toSeqLeft_106_; lean_object* v_toSeqRight_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_129_; 
v_toFunctor_104_ = lean_ctor_get(v_toApplicative_100_, 0);
v_toSeq_105_ = lean_ctor_get(v_toApplicative_100_, 2);
v_toSeqLeft_106_ = lean_ctor_get(v_toApplicative_100_, 3);
v_toSeqRight_107_ = lean_ctor_get(v_toApplicative_100_, 4);
v_isSharedCheck_129_ = !lean_is_exclusive(v_toApplicative_100_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; 
v_unused_130_ = lean_ctor_get(v_toApplicative_100_, 1);
lean_dec(v_unused_130_);
v___x_109_ = v_toApplicative_100_;
v_isShared_110_ = v_isSharedCheck_129_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_toSeqRight_107_);
lean_inc(v_toSeqLeft_106_);
lean_inc(v_toSeq_105_);
lean_inc(v_toFunctor_104_);
lean_dec(v_toApplicative_100_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_129_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___f_116_; lean_object* v___f_117_; lean_object* v___f_118_; lean_object* v___x_120_; 
v___f_111_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_112_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_104_);
v___f_113_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_113_, 0, v_toFunctor_104_);
v___f_114_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_114_, 0, v_toFunctor_104_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___f_113_);
lean_ctor_set(v___x_115_, 1, v___f_114_);
v___f_116_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_116_, 0, v_toSeqRight_107_);
v___f_117_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_117_, 0, v_toSeqLeft_106_);
v___f_118_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_118_, 0, v_toSeq_105_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 4, v___f_116_);
lean_ctor_set(v___x_109_, 3, v___f_117_);
lean_ctor_set(v___x_109_, 2, v___f_118_);
lean_ctor_set(v___x_109_, 1, v___f_111_);
lean_ctor_set(v___x_109_, 0, v___x_115_);
v___x_120_ = v___x_109_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___f_111_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v___f_118_);
lean_ctor_set(v_reuseFailAlloc_128_, 3, v___f_117_);
lean_ctor_set(v_reuseFailAlloc_128_, 4, v___f_116_);
v___x_120_ = v_reuseFailAlloc_128_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_122_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___f_112_);
lean_ctor_set(v___x_102_, 0, v___x_120_);
v___x_122_ = v___x_102_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v___f_112_);
v___x_122_ = v_reuseFailAlloc_127_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
size_t v_sz_123_; size_t v___x_124_; lean_object* v___x_57__overap_125_; lean_object* v___x_126_; 
v_sz_123_ = lean_array_size(v_data_77_);
v___x_124_ = ((size_t)0ULL);
v___x_57__overap_125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_122_, v_f_76_, v_sz_123_, v___x_124_, v_data_77_);
lean_inc(v_a_81_);
lean_inc_ref(v_a_80_);
lean_inc(v_a_79_);
lean_inc_ref(v_a_78_);
v___x_126_ = lean_apply_5(v___x_57__overap_125_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, lean_box(0));
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_map_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_76_ = stack[2].m_obj;
lean_object* v_data_77_ = stack[3].m_obj;
lean_object* v_a_78_ = stack[4].m_obj;
lean_object* v_a_79_ = stack[5].m_obj;
lean_object* v_a_80_ = stack[6].m_obj;
lean_object* v_a_81_ = stack[7].m_obj;
lean_object* v_res_133_;
v_res_133_ = l_Lean_Compiler_LCNF_Probe_map(lean_box(0), lean_box(0), v_f_76_, v_data_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_map___boxed(lean_object* v_00_u03b1_134_, lean_object* v_00_u03b2_135_, lean_object* v_f_136_, lean_object* v_data_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Compiler_LCNF_Probe_map(v_00_u03b1_134_, v_00_u03b2_135_, v_f_136_, v_data_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
return v_res_143_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0(lean_object* v_f_144_, lean_object* v_acc_145_, lean_object* v_a_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v___x_152_; 
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v_a_146_);
v___x_152_ = lean_apply_6(v_f_144_, v_a_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, lean_box(0));
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_165_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_165_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_165_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_165_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
uint8_t v___x_157_; 
v___x_157_ = lean_unbox(v_a_153_);
lean_dec(v_a_153_);
if (v___x_157_ == 0)
{
lean_object* v___x_159_; 
lean_dec(v_a_146_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v_acc_145_);
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_acc_145_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
else
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = lean_array_push(v_acc_145_, v_a_146_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_161_);
v___x_163_ = v___x_155_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
lean_dec(v_a_146_);
lean_dec_ref(v_acc_145_);
v_a_166_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_152_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_152_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_144_ = stack[0].m_obj;
lean_object* v_acc_145_ = stack[1].m_obj;
lean_object* v_a_146_ = stack[2].m_obj;
lean_object* v___y_147_ = stack[3].m_obj;
lean_object* v___y_148_ = stack[4].m_obj;
lean_object* v___y_149_ = stack[5].m_obj;
lean_object* v___y_150_ = stack[6].m_obj;
lean_object* v_res_174_;
v_res_174_ = l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0(v_f_144_, v_acc_145_, v_a_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed(lean_object* v_f_175_, lean_object* v_acc_176_, lean_object* v_a_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0(v_f_175_, v_acc_176_, v_a_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
return v_res_183_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg(lean_object* v_f_186_, lean_object* v_data_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; lean_object* v_toApplicative_194_; lean_object* v_toFunctor_195_; lean_object* v_toSeq_196_; lean_object* v_toSeqLeft_197_; lean_object* v_toSeqRight_198_; lean_object* v___f_199_; lean_object* v___f_200_; lean_object* v___f_201_; lean_object* v___f_202_; lean_object* v___x_203_; lean_object* v___f_204_; lean_object* v___f_205_; lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_toApplicative_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_253_; 
v___x_193_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_194_ = lean_ctor_get(v___x_193_, 0);
v_toFunctor_195_ = lean_ctor_get(v_toApplicative_194_, 0);
v_toSeq_196_ = lean_ctor_get(v_toApplicative_194_, 2);
v_toSeqLeft_197_ = lean_ctor_get(v_toApplicative_194_, 3);
v_toSeqRight_198_ = lean_ctor_get(v_toApplicative_194_, 4);
v___f_199_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_200_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_195_, 2);
v___f_201_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_201_, 0, v_toFunctor_195_);
v___f_202_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_202_, 0, v_toFunctor_195_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___f_201_);
lean_ctor_set(v___x_203_, 1, v___f_202_);
lean_inc(v_toSeqRight_198_);
v___f_204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_204_, 0, v_toSeqRight_198_);
lean_inc(v_toSeqLeft_197_);
v___f_205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_205_, 0, v_toSeqLeft_197_);
lean_inc(v_toSeq_196_);
v___f_206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_206_, 0, v_toSeq_196_);
v___x_207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_207_, 0, v___x_203_);
lean_ctor_set(v___x_207_, 1, v___f_199_);
lean_ctor_set(v___x_207_, 2, v___f_206_);
lean_ctor_set(v___x_207_, 3, v___f_205_);
lean_ctor_set(v___x_207_, 4, v___f_204_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___f_200_);
v___x_209_ = l_StateRefT_x27_instMonad___redArg(v___x_208_);
v_toApplicative_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; 
v_unused_254_ = lean_ctor_get(v___x_209_, 1);
lean_dec(v_unused_254_);
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_253_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_toApplicative_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_253_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_toFunctor_214_; lean_object* v_toSeq_215_; lean_object* v_toSeqLeft_216_; lean_object* v_toSeqRight_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_251_; 
v_toFunctor_214_ = lean_ctor_get(v_toApplicative_210_, 0);
v_toSeq_215_ = lean_ctor_get(v_toApplicative_210_, 2);
v_toSeqLeft_216_ = lean_ctor_get(v_toApplicative_210_, 3);
v_toSeqRight_217_ = lean_ctor_get(v_toApplicative_210_, 4);
v_isSharedCheck_251_ = !lean_is_exclusive(v_toApplicative_210_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_toApplicative_210_, 1);
lean_dec(v_unused_252_);
v___x_219_ = v_toApplicative_210_;
v_isShared_220_ = v_isSharedCheck_251_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_toSeqRight_217_);
lean_inc(v_toSeqLeft_216_);
lean_inc(v_toSeq_215_);
lean_inc(v_toFunctor_214_);
lean_dec(v_toApplicative_210_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_251_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___f_226_; lean_object* v___f_227_; lean_object* v___f_228_; lean_object* v___x_230_; 
v___f_221_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_222_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_214_);
v___f_223_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_223_, 0, v_toFunctor_214_);
v___f_224_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_224_, 0, v_toFunctor_214_);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v___f_223_);
lean_ctor_set(v___x_225_, 1, v___f_224_);
v___f_226_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_226_, 0, v_toSeqRight_217_);
v___f_227_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_227_, 0, v_toSeqLeft_216_);
v___f_228_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_228_, 0, v_toSeq_215_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 4, v___f_226_);
lean_ctor_set(v___x_219_, 3, v___f_227_);
lean_ctor_set(v___x_219_, 2, v___f_228_);
lean_ctor_set(v___x_219_, 1, v___f_221_);
lean_ctor_set(v___x_219_, 0, v___x_225_);
v___x_230_ = v___x_219_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___f_221_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v___f_228_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v___f_227_);
lean_ctor_set(v_reuseFailAlloc_250_, 4, v___f_226_);
v___x_230_ = v_reuseFailAlloc_250_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_232_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___f_222_);
lean_ctor_set(v___x_212_, 0, v___x_230_);
v___x_232_ = v___x_212_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___f_222_);
v___x_232_ = v_reuseFailAlloc_249_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_array_get_size(v_data_187_);
v___x_235_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0));
v___x_236_ = lean_nat_dec_lt(v___x_233_, v___x_234_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec_ref(v___x_232_);
lean_dec_ref(v_data_187_);
lean_dec_ref(v_f_186_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_235_);
return v___x_237_;
}
else
{
lean_object* v___f_238_; uint8_t v___x_239_; 
v___f_238_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_238_, 0, v_f_186_);
v___x_239_ = lean_nat_dec_le(v___x_234_, v___x_234_);
if (v___x_239_ == 0)
{
if (v___x_236_ == 0)
{
lean_object* v___x_240_; 
lean_dec_ref(v___f_238_);
lean_dec_ref(v___x_232_);
lean_dec_ref(v_data_187_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_235_);
return v___x_240_;
}
else
{
size_t v___x_241_; size_t v___x_242_; lean_object* v___x_348__overap_243_; lean_object* v___x_244_; 
v___x_241_ = ((size_t)0ULL);
v___x_242_ = lean_usize_of_nat(v___x_234_);
v___x_348__overap_243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_232_, v___f_238_, v_data_187_, v___x_241_, v___x_242_, v___x_235_);
lean_inc(v_a_191_);
lean_inc_ref(v_a_190_);
lean_inc(v_a_189_);
lean_inc_ref(v_a_188_);
v___x_244_ = lean_apply_5(v___x_348__overap_243_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, lean_box(0));
return v___x_244_;
}
}
else
{
size_t v___x_245_; size_t v___x_246_; lean_object* v___x_352__overap_247_; lean_object* v___x_248_; 
v___x_245_ = ((size_t)0ULL);
v___x_246_ = lean_usize_of_nat(v___x_234_);
v___x_352__overap_247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_232_, v___f_238_, v_data_187_, v___x_245_, v___x_246_, v___x_235_);
lean_inc(v_a_191_);
lean_inc_ref(v_a_190_);
lean_inc(v_a_189_);
lean_inc_ref(v_a_188_);
v___x_248_ = lean_apply_5(v___x_352__overap_247_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, lean_box(0));
return v___x_248_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_186_ = stack[0].m_obj;
lean_object* v_data_187_ = stack[1].m_obj;
lean_object* v_a_188_ = stack[2].m_obj;
lean_object* v_a_189_ = stack[3].m_obj;
lean_object* v_a_190_ = stack[4].m_obj;
lean_object* v_a_191_ = stack[5].m_obj;
lean_object* v_res_255_;
v_res_255_ = l_Lean_Compiler_LCNF_Probe_filter___redArg(v_f_186_, v_data_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
stack->m_obj
 = v_res_255_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___redArg___boxed(lean_object* v_f_256_, lean_object* v_data_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Compiler_LCNF_Probe_filter___redArg(v_f_256_, v_data_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
return v_res_263_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filter(lean_object* v_00_u03b1_264_, lean_object* v_f_265_, lean_object* v_data_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_272_; lean_object* v_toApplicative_273_; lean_object* v_toFunctor_274_; lean_object* v_toSeq_275_; lean_object* v_toSeqLeft_276_; lean_object* v_toSeqRight_277_; lean_object* v___f_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___f_283_; lean_object* v___f_284_; lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_toApplicative_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_332_; 
v___x_272_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_273_ = lean_ctor_get(v___x_272_, 0);
v_toFunctor_274_ = lean_ctor_get(v_toApplicative_273_, 0);
v_toSeq_275_ = lean_ctor_get(v_toApplicative_273_, 2);
v_toSeqLeft_276_ = lean_ctor_get(v_toApplicative_273_, 3);
v_toSeqRight_277_ = lean_ctor_get(v_toApplicative_273_, 4);
v___f_278_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_279_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_274_, 2);
v___f_280_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_280_, 0, v_toFunctor_274_);
v___f_281_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_281_, 0, v_toFunctor_274_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___f_280_);
lean_ctor_set(v___x_282_, 1, v___f_281_);
lean_inc(v_toSeqRight_277_);
v___f_283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_283_, 0, v_toSeqRight_277_);
lean_inc(v_toSeqLeft_276_);
v___f_284_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_284_, 0, v_toSeqLeft_276_);
lean_inc(v_toSeq_275_);
v___f_285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_285_, 0, v_toSeq_275_);
v___x_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_286_, 0, v___x_282_);
lean_ctor_set(v___x_286_, 1, v___f_278_);
lean_ctor_set(v___x_286_, 2, v___f_285_);
lean_ctor_set(v___x_286_, 3, v___f_284_);
lean_ctor_set(v___x_286_, 4, v___f_283_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___f_279_);
v___x_288_ = l_StateRefT_x27_instMonad___redArg(v___x_287_);
v_toApplicative_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v___x_288_, 1);
lean_dec(v_unused_333_);
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_332_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_toApplicative_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_332_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_toFunctor_293_; lean_object* v_toSeq_294_; lean_object* v_toSeqLeft_295_; lean_object* v_toSeqRight_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_330_; 
v_toFunctor_293_ = lean_ctor_get(v_toApplicative_289_, 0);
v_toSeq_294_ = lean_ctor_get(v_toApplicative_289_, 2);
v_toSeqLeft_295_ = lean_ctor_get(v_toApplicative_289_, 3);
v_toSeqRight_296_ = lean_ctor_get(v_toApplicative_289_, 4);
v_isSharedCheck_330_ = !lean_is_exclusive(v_toApplicative_289_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v_toApplicative_289_, 1);
lean_dec(v_unused_331_);
v___x_298_ = v_toApplicative_289_;
v_isShared_299_ = v_isSharedCheck_330_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_toSeqRight_296_);
lean_inc(v_toSeqLeft_295_);
lean_inc(v_toSeq_294_);
lean_inc(v_toFunctor_293_);
lean_dec(v_toApplicative_289_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_330_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___f_300_; lean_object* v___f_301_; lean_object* v___f_302_; lean_object* v___f_303_; lean_object* v___x_304_; lean_object* v___f_305_; lean_object* v___f_306_; lean_object* v___f_307_; lean_object* v___x_309_; 
v___f_300_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_301_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_293_);
v___f_302_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_302_, 0, v_toFunctor_293_);
v___f_303_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_303_, 0, v_toFunctor_293_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___f_302_);
lean_ctor_set(v___x_304_, 1, v___f_303_);
v___f_305_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_305_, 0, v_toSeqRight_296_);
v___f_306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_306_, 0, v_toSeqLeft_295_);
v___f_307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_307_, 0, v_toSeq_294_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 4, v___f_305_);
lean_ctor_set(v___x_298_, 3, v___f_306_);
lean_ctor_set(v___x_298_, 2, v___f_307_);
lean_ctor_set(v___x_298_, 1, v___f_300_);
lean_ctor_set(v___x_298_, 0, v___x_304_);
v___x_309_ = v___x_298_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_304_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___f_300_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v___f_307_);
lean_ctor_set(v_reuseFailAlloc_329_, 3, v___f_306_);
lean_ctor_set(v_reuseFailAlloc_329_, 4, v___f_305_);
v___x_309_ = v_reuseFailAlloc_329_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v___f_301_);
lean_ctor_set(v___x_291_, 0, v___x_309_);
v___x_311_ = v___x_291_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___f_301_);
v___x_311_ = v_reuseFailAlloc_328_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_array_get_size(v_data_266_);
v___x_314_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___closed__0));
v___x_315_ = lean_nat_dec_lt(v___x_312_, v___x_313_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec_ref(v___x_311_);
lean_dec_ref(v_data_266_);
lean_dec_ref(v_f_265_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
return v___x_316_;
}
else
{
lean_object* v___f_317_; uint8_t v___x_318_; 
v___f_317_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_filter___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_317_, 0, v_f_265_);
v___x_318_ = lean_nat_dec_le(v___x_313_, v___x_313_);
if (v___x_318_ == 0)
{
if (v___x_315_ == 0)
{
lean_object* v___x_319_; 
lean_dec_ref(v___f_317_);
lean_dec_ref(v___x_311_);
lean_dec_ref(v_data_266_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_314_);
return v___x_319_;
}
else
{
size_t v___x_320_; size_t v___x_321_; lean_object* v___x_436__overap_322_; lean_object* v___x_323_; 
v___x_320_ = ((size_t)0ULL);
v___x_321_ = lean_usize_of_nat(v___x_313_);
v___x_436__overap_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_311_, v___f_317_, v_data_266_, v___x_320_, v___x_321_, v___x_314_);
lean_inc(v_a_270_);
lean_inc_ref(v_a_269_);
lean_inc(v_a_268_);
lean_inc_ref(v_a_267_);
v___x_323_ = lean_apply_5(v___x_436__overap_322_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, lean_box(0));
return v___x_323_;
}
}
else
{
size_t v___x_324_; size_t v___x_325_; lean_object* v___x_439__overap_326_; lean_object* v___x_327_; 
v___x_324_ = ((size_t)0ULL);
v___x_325_ = lean_usize_of_nat(v___x_313_);
v___x_439__overap_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_311_, v___f_317_, v_data_266_, v___x_324_, v___x_325_, v___x_314_);
lean_inc(v_a_270_);
lean_inc_ref(v_a_269_);
lean_inc(v_a_268_);
lean_inc_ref(v_a_267_);
v___x_327_ = lean_apply_5(v___x_439__overap_326_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, lean_box(0));
return v___x_327_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filter_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_265_ = stack[1].m_obj;
lean_object* v_data_266_ = stack[2].m_obj;
lean_object* v_a_267_ = stack[3].m_obj;
lean_object* v_a_268_ = stack[4].m_obj;
lean_object* v_a_269_ = stack[5].m_obj;
lean_object* v_a_270_ = stack[6].m_obj;
lean_object* v_res_334_;
v_res_334_ = l_Lean_Compiler_LCNF_Probe_filter(lean_box(0), v_f_265_, v_data_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filter___boxed(lean_object* v_00_u03b1_335_, lean_object* v_f_336_, lean_object* v_data_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Compiler_LCNF_Probe_filter(v_00_u03b1_335_, v_f_336_, v_data_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
return v_res_343_;
}
}
uint8_t l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(lean_object* v_inst_344_, lean_object* v_x1_345_, lean_object* v_x2_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_apply_2(v_inst_344_, v_x1_345_, v_x2_346_);
v___x_348_ = lean_unbox(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_344_ = stack[0].m_obj;
lean_object* v_x1_345_ = stack[1].m_obj;
lean_object* v_x2_346_ = stack[2].m_obj;
uint8_t v_res_349_;
v_res_349_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(v_inst_344_, v_x1_345_, v_x2_346_);
stack->m_num = v_res_349_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed(lean_object* v_inst_350_, lean_object* v_x1_351_, lean_object* v_x2_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0(v_inst_350_, v_x1_351_, v_x2_352_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg(lean_object* v_inst_355_, lean_object* v_data_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_358_ = lean_array_get_size(v_data_356_);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_nat_dec_eq(v___x_358_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___f_361_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___y_370_; uint8_t v___x_372_; 
v___f_361_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_361_, 0, v_inst_355_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_nat_sub(v___x_358_, v___x_367_);
v___x_372_ = lean_nat_dec_le(v___x_359_, v___x_368_);
if (v___x_372_ == 0)
{
lean_inc(v___x_368_);
v___y_370_ = v___x_368_;
goto v___jp_369_;
}
else
{
v___y_370_ = v___x_359_;
goto v___jp_369_;
}
v___jp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_361_, v___x_358_, v_data_356_, v___y_363_, v___y_364_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_364_);
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
v___jp_369_:
{
uint8_t v___x_371_; 
v___x_371_ = lean_nat_dec_le(v___y_370_, v___x_368_);
if (v___x_371_ == 0)
{
lean_dec(v___x_368_);
lean_inc(v___y_370_);
v___y_363_ = v___y_370_;
v___y_364_ = v___y_370_;
goto v___jp_362_;
}
else
{
v___y_363_ = v___y_370_;
v___y_364_ = v___x_368_;
goto v___jp_362_;
}
}
}
else
{
lean_object* v___x_373_; 
lean_dec_ref(v_inst_355_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v_data_356_);
return v___x_373_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_sorted___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_355_ = stack[0].m_obj;
lean_object* v_data_356_ = stack[1].m_obj;
lean_object* v_res_374_;
v_res_374_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg(v_inst_355_, v_data_356_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___redArg___boxed(lean_object* v_inst_375_, lean_object* v_data_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Compiler_LCNF_Probe_sorted___redArg(v_inst_375_, v_data_376_);
return v_res_378_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_sorted(lean_object* v_00_u03b1_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_data_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = lean_array_get_size(v_data_383_);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_nat_dec_eq(v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___f_392_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___y_401_; uint8_t v___x_403_; 
v___f_392_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sorted___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_392_, 0, v_inst_382_);
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_sub(v___x_389_, v___x_398_);
v___x_403_ = lean_nat_dec_le(v___x_390_, v___x_399_);
if (v___x_403_ == 0)
{
lean_inc(v___x_399_);
v___y_401_ = v___x_399_;
goto v___jp_400_;
}
else
{
v___y_401_ = v___x_390_;
goto v___jp_400_;
}
v___jp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_392_, v___x_389_, v_data_383_, v___y_394_, v___y_395_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_395_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
v___jp_400_:
{
uint8_t v___x_402_; 
v___x_402_ = lean_nat_dec_le(v___y_401_, v___x_399_);
if (v___x_402_ == 0)
{
lean_dec(v___x_399_);
lean_inc(v___y_401_);
v___y_394_ = v___y_401_;
v___y_395_ = v___y_401_;
goto v___jp_393_;
}
else
{
v___y_394_ = v___y_401_;
v___y_395_ = v___x_399_;
goto v___jp_393_;
}
}
}
else
{
lean_object* v___x_404_; 
lean_dec_ref(v_inst_382_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v_data_383_);
return v___x_404_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_sorted_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_380_ = stack[1].m_obj;
lean_object* v_inst_381_ = stack[2].m_obj;
lean_object* v_inst_382_ = stack[3].m_obj;
lean_object* v_data_383_ = stack[4].m_obj;
lean_object* v_a_384_ = stack[5].m_obj;
lean_object* v_a_385_ = stack[6].m_obj;
lean_object* v_a_386_ = stack[7].m_obj;
lean_object* v_a_387_ = stack[8].m_obj;
lean_object* v_res_405_;
v_res_405_ = l_Lean_Compiler_LCNF_Probe_sorted(lean_box(0), v_inst_380_, v_inst_381_, v_inst_382_, v_data_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
stack->m_obj
 = v_res_405_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sorted___boxed(lean_object* v_00_u03b1_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_data_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Compiler_LCNF_Probe_sorted(v_00_u03b1_406_, v_inst_407_, v_inst_408_, v_inst_409_, v_data_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_inst_407_);
return v_res_416_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(uint8_t v_pu_417_, lean_object* v_x_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = l_Lean_Compiler_LCNF_Decl_size(v_pu_417_, v_x_418_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v_x_418_);
return v___x_420_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_417_ = stack[0].m_num;
lean_object* v_x_418_ = stack[1].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(v_pu_417_, v_x_418_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed(lean_object* v_pu_422_, lean_object* v_x_423_){
_start:
{
uint8_t v_pu_boxed_424_; lean_object* v_res_425_; 
v_pu_boxed_424_ = lean_unbox(v_pu_422_);
v_res_425_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0(v_pu_boxed_424_, v_x_423_);
return v_res_425_;
}
}
uint8_t l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; uint8_t v___x_432_; 
v_fst_428_ = lean_ctor_get(v_x_426_, 0);
v_snd_429_ = lean_ctor_get(v_x_426_, 1);
v_fst_430_ = lean_ctor_get(v_x_427_, 0);
v_snd_431_ = lean_ctor_get(v_x_427_, 1);
v___x_432_ = lean_nat_dec_eq(v_fst_428_, v_fst_430_);
if (v___x_432_ == 0)
{
uint8_t v___x_433_; 
v___x_433_ = lean_nat_dec_lt(v_fst_428_, v_fst_430_);
return v___x_433_;
}
else
{
lean_object* v_toSignature_434_; lean_object* v_toSignature_435_; lean_object* v_name_436_; lean_object* v_name_437_; uint8_t v___x_438_; 
v_toSignature_434_ = lean_ctor_get(v_snd_429_, 0);
v_toSignature_435_ = lean_ctor_get(v_snd_431_, 0);
v_name_436_ = lean_ctor_get(v_toSignature_434_, 0);
v_name_437_ = lean_ctor_get(v_toSignature_435_, 0);
v___x_438_ = l_Lean_Name_lt(v_name_436_, v_name_437_);
return v___x_438_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_426_ = stack[0].m_obj;
lean_object* v_x_427_ = stack[1].m_obj;
uint8_t v_res_439_;
v_res_439_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(v_x_426_, v_x_427_);
stack->m_num = v_res_439_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1___boxed(lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__1(v_x_440_, v_x_441_);
lean_dec_ref(v_x_441_);
lean_dec_ref(v_x_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(uint8_t v_pu_464_, lean_object* v_decls_465_){
_start:
{
lean_object* v___x_467_; lean_object* v___f_468_; lean_object* v___x_469_; size_t v_sz_470_; size_t v___x_471_; lean_object* v_decls_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_467_ = lean_box(v_pu_464_);
v___f_468_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_468_, 0, v___x_467_);
v___x_469_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v_sz_470_ = lean_array_size(v_decls_465_);
v___x_471_ = ((size_t)0ULL);
v_decls_472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_469_, v___f_468_, v_sz_470_, v___x_471_, v_decls_465_);
v___x_473_ = lean_array_get_size(v_decls_472_);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_nat_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___f_476_; lean_object* v___y_478_; lean_object* v___y_479_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___y_485_; uint8_t v___x_487_; 
v___f_476_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10));
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_sub(v___x_473_, v___x_482_);
v___x_487_ = lean_nat_dec_le(v___x_474_, v___x_483_);
if (v___x_487_ == 0)
{
lean_inc(v___x_483_);
v___y_485_ = v___x_483_;
goto v___jp_484_;
}
else
{
v___y_485_ = v___x_474_;
goto v___jp_484_;
}
v___jp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_476_, v___x_473_, v_decls_472_, v___y_478_, v___y_479_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_479_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
v___jp_484_:
{
uint8_t v___x_486_; 
v___x_486_ = lean_nat_dec_le(v___y_485_, v___x_483_);
if (v___x_486_ == 0)
{
lean_dec(v___x_483_);
lean_inc(v___y_485_);
v___y_478_ = v___y_485_;
v___y_479_ = v___y_485_;
goto v___jp_477_;
}
else
{
v___y_478_ = v___y_485_;
v___y_479_ = v___x_483_;
goto v___jp_477_;
}
}
}
else
{
lean_object* v___x_488_; 
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v_decls_472_);
return v___x_488_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_464_ = stack[0].m_num;
lean_object* v_decls_465_ = stack[1].m_obj;
lean_object* v_res_489_;
v_res_489_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(v_pu_464_, v_decls_465_);
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___boxed(lean_object* v_pu_490_, lean_object* v_decls_491_, lean_object* v_a_492_){
_start:
{
uint8_t v_pu_boxed_493_; lean_object* v_res_494_; 
v_pu_boxed_493_ = lean_unbox(v_pu_490_);
v_res_494_ = l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg(v_pu_boxed_493_, v_decls_491_);
return v_res_494_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize(uint8_t v_pu_495_, lean_object* v_decls_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v___x_502_; lean_object* v___f_503_; lean_object* v___x_504_; size_t v_sz_505_; size_t v___x_506_; lean_object* v_decls_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_502_ = lean_box(v_pu_495_);
v___f_503_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_503_, 0, v___x_502_);
v___x_504_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v_sz_505_ = lean_array_size(v_decls_496_);
v___x_506_ = ((size_t)0ULL);
v_decls_507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_504_, v___f_503_, v_sz_505_, v___x_506_, v_decls_496_);
v___x_508_ = lean_array_get_size(v_decls_507_);
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_nat_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___f_511_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___y_520_; uint8_t v___x_522_; 
v___f_511_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__10));
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_sub(v___x_508_, v___x_517_);
v___x_522_ = lean_nat_dec_le(v___x_509_, v___x_518_);
if (v___x_522_ == 0)
{
lean_inc(v___x_518_);
v___y_520_ = v___x_518_;
goto v___jp_519_;
}
else
{
v___y_520_ = v___x_509_;
goto v___jp_519_;
}
v___jp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_511_, v___x_508_, v_decls_507_, v___y_513_, v___y_514_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
v___jp_519_:
{
uint8_t v___x_521_; 
v___x_521_ = lean_nat_dec_le(v___y_520_, v___x_518_);
if (v___x_521_ == 0)
{
lean_dec(v___x_518_);
lean_inc(v___y_520_);
v___y_513_ = v___y_520_;
v___y_514_ = v___y_520_;
goto v___jp_512_;
}
else
{
v___y_513_ = v___y_520_;
v___y_514_ = v___x_518_;
goto v___jp_512_;
}
}
}
else
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v_decls_507_);
return v___x_523_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_sortedBySize_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_495_ = stack[0].m_num;
lean_object* v_decls_496_ = stack[1].m_obj;
lean_object* v_a_497_ = stack[2].m_obj;
lean_object* v_a_498_ = stack[3].m_obj;
lean_object* v_a_499_ = stack[4].m_obj;
lean_object* v_a_500_ = stack[5].m_obj;
lean_object* v_res_524_;
v_res_524_ = l_Lean_Compiler_LCNF_Probe_sortedBySize(v_pu_495_, v_decls_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sortedBySize___boxed(lean_object* v_pu_525_, lean_object* v_decls_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
uint8_t v_pu_boxed_532_; lean_object* v_res_533_; 
v_pu_boxed_532_ = lean_unbox(v_pu_525_);
v_res_533_ = l_Lean_Compiler_LCNF_Probe_sortedBySize(v_pu_boxed_532_, v_decls_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
return v_res_533_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_a_536_, lean_object* v_x_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; 
lean_inc(v_a_536_);
lean_inc_ref(v_inst_535_);
lean_inc_ref(v_inst_534_);
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_534_, v_inst_535_, v___y_538_, v_a_536_);
if (lean_obj_tag(v___x_544_) == 1)
{
lean_object* v_val_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_556_; 
v_val_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_556_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_val_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_add(v_val_545_, v___x_549_);
lean_dec(v_val_545_);
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_534_, v_inst_535_, v___y_538_, v_a_536_, v___x_550_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_551_);
v___x_553_ = v___x_547_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_555_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; 
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v___x_544_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_534_, v_inst_535_, v___y_538_, v_a_536_, v___x_557_);
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_534_ = stack[0].m_obj;
lean_object* v_inst_535_ = stack[1].m_obj;
lean_object* v_a_536_ = stack[2].m_obj;
lean_object* v___y_538_ = stack[4].m_obj;
lean_object* v___y_539_ = stack[5].m_obj;
lean_object* v___y_540_ = stack[6].m_obj;
lean_object* v___y_541_ = stack[7].m_obj;
lean_object* v___y_542_ = stack[8].m_obj;
lean_object* v_res_561_;
v_res_561_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(v_inst_534_, v_inst_535_, v_a_536_, lean_box(0), v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
stack->m_obj
 = v_res_561_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed(lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_a_564_, lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0(v_inst_562_, v_inst_563_, v_a_564_, v_x_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__1(lean_object* v_x1_573_, lean_object* v_x2_574_, lean_object* v_x3_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_x2_574_);
lean_ctor_set(v___x_576_, 1, v_x3_575_);
v___x_577_ = lean_array_push(v_x1_573_, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__2(lean_object* v___x_578_, lean_object* v___f_579_, lean_object* v_acc_580_, lean_object* v_l_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_578_, v___f_579_, v_acc_580_, v_l_581_);
return v___x_582_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg(lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_data_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; lean_object* v_toApplicative_596_; lean_object* v_toFunctor_597_; lean_object* v_toSeq_598_; lean_object* v_toSeqLeft_599_; lean_object* v_toSeqRight_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_toApplicative_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_682_; 
v___x_595_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_596_ = lean_ctor_get(v___x_595_, 0);
v_toFunctor_597_ = lean_ctor_get(v_toApplicative_596_, 0);
v_toSeq_598_ = lean_ctor_get(v_toApplicative_596_, 2);
v_toSeqLeft_599_ = lean_ctor_get(v_toApplicative_596_, 3);
v_toSeqRight_600_ = lean_ctor_get(v_toApplicative_596_, 4);
v___f_601_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_602_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_597_, 2);
v___f_603_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_603_, 0, v_toFunctor_597_);
v___f_604_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_604_, 0, v_toFunctor_597_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___f_603_);
lean_ctor_set(v___x_605_, 1, v___f_604_);
lean_inc(v_toSeqRight_600_);
v___f_606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_606_, 0, v_toSeqRight_600_);
lean_inc(v_toSeqLeft_599_);
v___f_607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_607_, 0, v_toSeqLeft_599_);
lean_inc(v_toSeq_598_);
v___f_608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_608_, 0, v_toSeq_598_);
v___x_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_609_, 0, v___x_605_);
lean_ctor_set(v___x_609_, 1, v___f_601_);
lean_ctor_set(v___x_609_, 2, v___f_608_);
lean_ctor_set(v___x_609_, 3, v___f_607_);
lean_ctor_set(v___x_609_, 4, v___f_606_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___f_602_);
v___x_611_ = l_StateRefT_x27_instMonad___redArg(v___x_610_);
v_toApplicative_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v___x_611_, 1);
lean_dec(v_unused_683_);
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_682_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_toApplicative_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_682_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_toFunctor_616_; lean_object* v_toSeq_617_; lean_object* v_toSeqLeft_618_; lean_object* v_toSeqRight_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_680_; 
v_toFunctor_616_ = lean_ctor_get(v_toApplicative_612_, 0);
v_toSeq_617_ = lean_ctor_get(v_toApplicative_612_, 2);
v_toSeqLeft_618_ = lean_ctor_get(v_toApplicative_612_, 3);
v_toSeqRight_619_ = lean_ctor_get(v_toApplicative_612_, 4);
v_isSharedCheck_680_ = !lean_is_exclusive(v_toApplicative_612_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v_toApplicative_612_, 1);
lean_dec(v_unused_681_);
v___x_621_ = v_toApplicative_612_;
v_isShared_622_ = v_isSharedCheck_680_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_toSeqRight_619_);
lean_inc(v_toSeqLeft_618_);
lean_inc(v_toSeq_617_);
lean_inc(v_toFunctor_616_);
lean_dec(v_toApplicative_612_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_680_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___f_623_; lean_object* v___f_624_; lean_object* v___f_625_; lean_object* v___f_626_; lean_object* v___f_627_; lean_object* v___x_628_; lean_object* v___f_629_; lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___x_633_; 
v___f_623_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_623_, 0, v_inst_587_);
lean_closure_set(v___f_623_, 1, v_inst_588_);
v___f_624_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_625_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_616_);
v___f_626_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_626_, 0, v_toFunctor_616_);
v___f_627_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_627_, 0, v_toFunctor_616_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___f_626_);
lean_ctor_set(v___x_628_, 1, v___f_627_);
v___f_629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_629_, 0, v_toSeqRight_619_);
v___f_630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_630_, 0, v_toSeqLeft_618_);
v___f_631_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_631_, 0, v_toSeq_617_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 4, v___f_629_);
lean_ctor_set(v___x_621_, 3, v___f_630_);
lean_ctor_set(v___x_621_, 2, v___f_631_);
lean_ctor_set(v___x_621_, 1, v___f_624_);
lean_ctor_set(v___x_621_, 0, v___x_628_);
v___x_633_ = v___x_621_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___f_624_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v___f_631_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v___f_630_);
lean_ctor_set(v_reuseFailAlloc_679_, 4, v___f_629_);
v___x_633_ = v_reuseFailAlloc_679_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___f_625_);
lean_ctor_set(v___x_614_, 0, v___x_633_);
v___x_635_ = v___x_614_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___f_625_);
v___x_635_ = v_reuseFailAlloc_678_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_map_645_; size_t v_sz_646_; size_t v___x_647_; lean_object* v___x_720__overap_648_; lean_object* v___x_649_; 
v___x_636_ = lean_array_get_size(v_data_589_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_unsigned_to_nat(4u);
v___x_639_ = lean_nat_mul(v___x_636_, v___x_638_);
v___x_640_ = lean_unsigned_to_nat(3u);
v___x_641_ = lean_nat_div(v___x_639_, v___x_640_);
lean_dec(v___x_639_);
v___x_642_ = l_Nat_nextPowerOfTwo(v___x_641_);
lean_dec(v___x_641_);
v___x_643_ = lean_box(0);
v___x_644_ = lean_mk_array(v___x_642_, v___x_643_);
v_map_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_map_645_, 0, v___x_637_);
lean_ctor_set(v_map_645_, 1, v___x_644_);
v_sz_646_ = lean_array_size(v_data_589_);
v___x_647_ = ((size_t)0ULL);
v___x_720__overap_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_635_, v_data_589_, v___f_623_, v_sz_646_, v___x_647_, v_map_645_);
lean_inc(v_a_593_);
lean_inc_ref(v_a_592_);
lean_inc(v_a_591_);
lean_inc_ref(v_a_590_);
v___x_649_ = lean_apply_5(v___x_720__overap_648_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, lean_box(0));
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_669_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_669_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_669_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_669_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_size_654_; lean_object* v_buckets_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_size_654_ = lean_ctor_get(v_a_650_, 0);
lean_inc(v_size_654_);
v_buckets_655_ = lean_ctor_get(v_a_650_, 1);
lean_inc_ref(v_buckets_655_);
lean_dec(v_a_650_);
v___x_656_ = lean_mk_empty_array_with_capacity(v_size_654_);
lean_dec(v_size_654_);
v___x_657_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_658_ = lean_array_get_size(v_buckets_655_);
v___x_659_ = lean_nat_dec_lt(v___x_637_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v_buckets_655_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_656_);
v___x_661_ = v___x_652_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v___f_663_; size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___f_663_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUnique___redArg___closed__1));
v___x_664_ = lean_usize_of_nat(v___x_658_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_657_, v___f_663_, v_buckets_655_, v___x_647_, v___x_664_, v___x_656_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_665_);
v___x_667_ = v___x_652_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_649_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_649_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_countUnique___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_587_ = stack[0].m_obj;
lean_object* v_inst_588_ = stack[1].m_obj;
lean_object* v_data_589_ = stack[2].m_obj;
lean_object* v_a_590_ = stack[3].m_obj;
lean_object* v_a_591_ = stack[4].m_obj;
lean_object* v_a_592_ = stack[5].m_obj;
lean_object* v_a_593_ = stack[6].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_587_, v_inst_588_, v_data_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___redArg___boxed(lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_data_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_685_, v_inst_686_, v_data_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_693_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_countUnique(lean_object* v_00_u03b1_694_, lean_object* v_inst_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_data_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_696_, v_inst_697_, v_data_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
return v___x_704_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_countUnique_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_695_ = stack[1].m_obj;
lean_object* v_inst_696_ = stack[2].m_obj;
lean_object* v_inst_697_ = stack[3].m_obj;
lean_object* v_data_698_ = stack[4].m_obj;
lean_object* v_a_699_ = stack[5].m_obj;
lean_object* v_a_700_ = stack[6].m_obj;
lean_object* v_a_701_ = stack[7].m_obj;
lean_object* v_a_702_ = stack[8].m_obj;
lean_object* v_res_705_;
v_res_705_ = l_Lean_Compiler_LCNF_Probe_countUnique(lean_box(0), v_inst_695_, v_inst_696_, v_inst_697_, v_data_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
stack->m_obj
 = v_res_705_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUnique___boxed(lean_object* v_00_u03b1_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_data_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Compiler_LCNF_Probe_countUnique(v_00_u03b1_706_, v_inst_707_, v_inst_708_, v_inst_709_, v_data_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_inst_707_);
return v_res_716_;
}
}
uint8_t l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(lean_object* v_l_717_, lean_object* v_r_718_){
_start:
{
lean_object* v_snd_719_; lean_object* v_snd_720_; uint8_t v___x_721_; 
v_snd_719_ = lean_ctor_get(v_l_717_, 1);
v_snd_720_ = lean_ctor_get(v_r_718_, 1);
v___x_721_ = lean_nat_dec_lt(v_snd_719_, v_snd_720_);
return v___x_721_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_717_ = stack[0].m_obj;
lean_object* v_r_718_ = stack[1].m_obj;
uint8_t v_res_722_;
v_res_722_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(v_l_717_, v_r_718_);
stack->m_num = v_res_722_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0___boxed(lean_object* v_l_723_, lean_object* v_r_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___lam__0(v_l_723_, v_r_724_);
lean_dec_ref(v_r_724_);
lean_dec_ref(v_l_723_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___f_736_; lean_object* v___x_737_; 
v___f_736_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_737_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_728_, v_inst_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_739_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v___x_739_ = lean_array_get_size(v_a_738_);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_nat_dec_eq(v___x_739_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___y_750_; uint8_t v___x_752_; 
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_747_ = lean_unsigned_to_nat(1u);
v___x_748_ = lean_nat_sub(v___x_739_, v___x_747_);
v___x_752_ = lean_nat_dec_le(v___x_745_, v___x_748_);
if (v___x_752_ == 0)
{
lean_inc(v___x_748_);
v___y_750_ = v___x_748_;
goto v___jp_749_;
}
else
{
v___y_750_ = v___x_745_;
goto v___jp_749_;
}
v___jp_749_:
{
uint8_t v___x_751_; 
v___x_751_ = lean_nat_dec_le(v___y_750_, v___x_748_);
if (v___x_751_ == 0)
{
lean_dec(v___x_748_);
lean_inc(v___y_750_);
v___y_741_ = v___y_750_;
v___y_742_ = v___y_750_;
goto v___jp_740_;
}
else
{
v___y_741_ = v___y_750_;
v___y_742_ = v___x_748_;
goto v___jp_740_;
}
}
}
else
{
return v___x_737_;
}
v___jp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_736_, v___x_739_, v_a_738_, v___y_741_, v___y_742_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_742_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
else
{
return v___x_737_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_728_ = stack[0].m_obj;
lean_object* v_inst_729_ = stack[1].m_obj;
lean_object* v_a_730_ = stack[2].m_obj;
lean_object* v_a_731_ = stack[3].m_obj;
lean_object* v_a_732_ = stack[4].m_obj;
lean_object* v_a_733_ = stack[5].m_obj;
lean_object* v_a_734_ = stack[6].m_obj;
lean_object* v_res_753_;
v_res_753_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(v_inst_728_, v_inst_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___boxed(lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg(v_inst_754_, v_inst_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
return v_res_762_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted(lean_object* v_00_u03b1_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v___f_774_; lean_object* v___x_775_; 
v___f_774_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_countUniqueSorted___redArg___closed__0));
v___x_775_ = l_Lean_Compiler_LCNF_Probe_countUnique___redArg(v_inst_765_, v_inst_766_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v___x_777_ = lean_array_get_size(v_a_776_);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_nat_dec_eq(v___x_777_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___y_788_; uint8_t v___x_790_; 
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_sub(v___x_777_, v___x_785_);
v___x_790_ = lean_nat_dec_le(v___x_783_, v___x_786_);
if (v___x_790_ == 0)
{
lean_inc(v___x_786_);
v___y_788_ = v___x_786_;
goto v___jp_787_;
}
else
{
v___y_788_ = v___x_783_;
goto v___jp_787_;
}
v___jp_787_:
{
uint8_t v___x_789_; 
v___x_789_ = lean_nat_dec_le(v___y_788_, v___x_786_);
if (v___x_789_ == 0)
{
lean_dec(v___x_786_);
lean_inc(v___y_788_);
v___y_779_ = v___y_788_;
v___y_780_ = v___y_788_;
goto v___jp_778_;
}
else
{
v___y_779_ = v___y_788_;
v___y_780_ = v___x_786_;
goto v___jp_778_;
}
}
}
else
{
return v___x_775_;
}
v___jp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_774_, v___x_777_, v_a_776_, v___y_779_, v___y_780_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_780_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
else
{
return v___x_775_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_countUniqueSorted_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_764_ = stack[1].m_obj;
lean_object* v_inst_765_ = stack[2].m_obj;
lean_object* v_inst_766_ = stack[3].m_obj;
lean_object* v_inst_767_ = stack[4].m_obj;
lean_object* v_a_768_ = stack[5].m_obj;
lean_object* v_a_769_ = stack[6].m_obj;
lean_object* v_a_770_ = stack[7].m_obj;
lean_object* v_a_771_ = stack[8].m_obj;
lean_object* v_a_772_ = stack[9].m_obj;
lean_object* v_res_791_;
v_res_791_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted(lean_box(0), v_inst_764_, v_inst_765_, v_inst_766_, v_inst_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_countUniqueSorted___boxed(lean_object* v_00_u03b1_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Compiler_LCNF_Probe_countUniqueSorted(v_00_u03b1_792_, v_inst_793_, v_inst_794_, v_inst_795_, v_inst_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_inst_796_);
lean_dec_ref(v_inst_793_);
return v_res_803_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(uint8_t v_pu_804_, lean_object* v_c_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
switch(lean_obj_tag(v_c_805_))
{
case 0:
{
lean_object* v_decl_812_; lean_object* v_k_813_; lean_object* v___x_814_; lean_object* v_value_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v_decl_812_ = lean_ctor_get(v_c_805_, 0);
lean_inc_ref(v_decl_812_);
v_k_813_ = lean_ctor_get(v_c_805_, 1);
lean_inc_ref(v_k_813_);
lean_dec_ref_known(v_c_805_, 2);
v___x_814_ = lean_st_ref_take(v_a_806_);
v_value_815_ = lean_ctor_get(v_decl_812_, 3);
lean_inc(v_value_815_);
lean_dec_ref(v_decl_812_);
v___x_816_ = lean_array_push(v___x_814_, v_value_815_);
v___x_817_ = lean_st_ref_put(v_a_806_, v___x_816_);
v_c_805_ = v_k_813_;
goto _start;
}
case 1:
{
lean_object* v_decl_819_; lean_object* v_k_820_; lean_object* v_value_821_; lean_object* v___x_822_; 
v_decl_819_ = lean_ctor_get(v_c_805_, 0);
lean_inc_ref(v_decl_819_);
v_k_820_ = lean_ctor_get(v_c_805_, 1);
lean_inc_ref(v_k_820_);
lean_dec_ref_known(v_c_805_, 2);
v_value_821_ = lean_ctor_get(v_decl_819_, 4);
lean_inc_ref(v_value_821_);
lean_dec_ref(v_decl_819_);
v___x_822_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_804_, v_value_821_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_dec_ref_known(v___x_822_, 1);
v_c_805_ = v_k_820_;
goto _start;
}
else
{
lean_dec_ref(v_k_820_);
return v___x_822_;
}
}
case 2:
{
lean_object* v_decl_824_; lean_object* v_k_825_; lean_object* v_value_826_; lean_object* v___x_827_; 
v_decl_824_ = lean_ctor_get(v_c_805_, 0);
lean_inc_ref(v_decl_824_);
v_k_825_ = lean_ctor_get(v_c_805_, 1);
lean_inc_ref(v_k_825_);
lean_dec_ref_known(v_c_805_, 2);
v_value_826_ = lean_ctor_get(v_decl_824_, 4);
lean_inc_ref(v_value_826_);
lean_dec_ref(v_decl_824_);
v___x_827_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_804_, v_value_826_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_dec_ref_known(v___x_827_, 1);
v_c_805_ = v_k_825_;
goto _start;
}
else
{
lean_dec_ref(v_k_825_);
return v___x_827_;
}
}
case 4:
{
lean_object* v_cases_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_851_; 
v_cases_829_ = lean_ctor_get(v_c_805_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v_c_805_);
if (v_isSharedCheck_851_ == 0)
{
v___x_831_ = v_c_805_;
v_isShared_832_ = v_isSharedCheck_851_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_cases_829_);
lean_dec(v_c_805_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_851_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_alts_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_alts_833_ = lean_ctor_get(v_cases_829_, 3);
lean_inc_ref(v_alts_833_);
lean_dec_ref(v_cases_829_);
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_array_get_size(v_alts_833_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_nat_dec_lt(v___x_834_, v___x_835_);
if (v___x_837_ == 0)
{
lean_object* v___x_839_; 
lean_dec_ref(v_alts_833_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
lean_ctor_set(v___x_831_, 0, v___x_836_);
v___x_839_ = v___x_831_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_836_);
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
uint8_t v___x_841_; 
v___x_841_ = lean_nat_dec_le(v___x_835_, v___x_835_);
if (v___x_841_ == 0)
{
if (v___x_837_ == 0)
{
lean_object* v___x_843_; 
lean_dec_ref(v_alts_833_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
lean_ctor_set(v___x_831_, 0, v___x_836_);
v___x_843_ = v___x_831_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_836_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
lean_del_object(v___x_831_);
v___x_845_ = ((size_t)0ULL);
v___x_846_ = lean_usize_of_nat(v___x_835_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_804_, v_alts_833_, v___x_845_, v___x_846_, v___x_836_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec_ref(v_alts_833_);
return v___x_847_;
}
}
else
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
lean_del_object(v___x_831_);
v___x_848_ = ((size_t)0ULL);
v___x_849_ = lean_usize_of_nat(v___x_835_);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_804_, v_alts_833_, v___x_848_, v___x_849_, v___x_836_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec_ref(v_alts_833_);
return v___x_850_;
}
}
}
}
case 7:
{
lean_object* v_k_852_; 
v_k_852_ = lean_ctor_get(v_c_805_, 3);
lean_inc_ref(v_k_852_);
lean_dec_ref_known(v_c_805_, 4);
v_c_805_ = v_k_852_;
goto _start;
}
case 8:
{
lean_object* v_k_854_; 
v_k_854_ = lean_ctor_get(v_c_805_, 3);
lean_inc_ref(v_k_854_);
lean_dec_ref_known(v_c_805_, 4);
v_c_805_ = v_k_854_;
goto _start;
}
case 9:
{
lean_object* v_k_856_; 
v_k_856_ = lean_ctor_get(v_c_805_, 5);
lean_inc_ref(v_k_856_);
lean_dec_ref_known(v_c_805_, 6);
v_c_805_ = v_k_856_;
goto _start;
}
case 10:
{
lean_object* v_k_858_; 
v_k_858_ = lean_ctor_get(v_c_805_, 2);
lean_inc_ref(v_k_858_);
lean_dec_ref_known(v_c_805_, 3);
v_c_805_ = v_k_858_;
goto _start;
}
case 11:
{
lean_object* v_k_860_; 
v_k_860_ = lean_ctor_get(v_c_805_, 2);
lean_inc_ref(v_k_860_);
lean_dec_ref_known(v_c_805_, 3);
v_c_805_ = v_k_860_;
goto _start;
}
case 12:
{
lean_object* v_k_862_; 
v_k_862_ = lean_ctor_get(v_c_805_, 3);
lean_inc_ref(v_k_862_);
lean_dec_ref_known(v_c_805_, 4);
v_c_805_ = v_k_862_;
goto _start;
}
case 13:
{
lean_object* v_k_864_; 
v_k_864_ = lean_ctor_get(v_c_805_, 1);
lean_inc_ref(v_k_864_);
lean_dec_ref_known(v_c_805_, 2);
v_c_805_ = v_k_864_;
goto _start;
}
default: 
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec_ref(v_c_805_);
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_804_ = stack[0].m_num;
lean_object* v_c_805_ = stack[1].m_obj;
lean_object* v_a_806_ = stack[2].m_obj;
lean_object* v_a_807_ = stack[3].m_obj;
lean_object* v_a_808_ = stack[4].m_obj;
lean_object* v_a_809_ = stack[5].m_obj;
lean_object* v_a_810_ = stack[6].m_obj;
lean_object* v_res_868_;
v_res_868_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_804_, v_c_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
stack->m_obj
 = v_res_868_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(uint8_t v_pu_869_, lean_object* v_as_870_, size_t v_i_871_, size_t v_stop_872_, lean_object* v_b_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___y_881_; uint8_t v___x_887_; 
v___x_887_ = lean_usize_dec_eq(v_i_871_, v_stop_872_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
v___x_888_ = lean_array_uget_borrowed(v_as_870_, v_i_871_);
switch(lean_obj_tag(v___x_888_))
{
case 0:
{
lean_object* v_code_889_; 
v_code_889_ = lean_ctor_get(v___x_888_, 2);
lean_inc_ref(v_code_889_);
v___y_881_ = v_code_889_;
goto v___jp_880_;
}
case 1:
{
lean_object* v_code_890_; 
v_code_890_ = lean_ctor_get(v___x_888_, 1);
lean_inc_ref(v_code_890_);
v___y_881_ = v_code_890_;
goto v___jp_880_;
}
default: 
{
lean_object* v_code_891_; 
v_code_891_ = lean_ctor_get(v___x_888_, 0);
lean_inc_ref(v_code_891_);
v___y_881_ = v_code_891_;
goto v___jp_880_;
}
}
}
else
{
lean_object* v___x_892_; 
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v_b_873_);
return v___x_892_;
}
v___jp_880_:
{
lean_object* v___x_882_; 
v___x_882_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_869_, v___y_881_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; size_t v___x_884_; size_t v___x_885_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_add(v_i_871_, v___x_884_);
v_i_871_ = v___x_885_;
v_b_873_ = v_a_883_;
goto _start;
}
else
{
return v___x_882_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_869_ = stack[0].m_num;
lean_object* v_as_870_ = stack[1].m_obj;
size_t v_i_871_ = stack[2].m_num;
size_t v_stop_872_ = stack[3].m_num;
lean_object* v_b_873_ = stack[4].m_obj;
lean_object* v___y_874_ = stack[5].m_obj;
lean_object* v___y_875_ = stack[6].m_obj;
lean_object* v___y_876_ = stack[7].m_obj;
lean_object* v___y_877_ = stack[8].m_obj;
lean_object* v___y_878_ = stack[9].m_obj;
lean_object* v_res_893_;
v_res_893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_869_, v_as_870_, v_i_871_, v_stop_872_, v_b_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
stack->m_obj
 = v_res_893_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0___boxed(lean_object* v_pu_894_, lean_object* v_as_895_, lean_object* v_i_896_, lean_object* v_stop_897_, lean_object* v_b_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
uint8_t v_pu_boxed_905_; size_t v_i_boxed_906_; size_t v_stop_boxed_907_; lean_object* v_res_908_; 
v_pu_boxed_905_ = lean_unbox(v_pu_894_);
v_i_boxed_906_ = lean_unbox_usize(v_i_896_);
lean_dec(v_i_896_);
v_stop_boxed_907_ = lean_unbox_usize(v_stop_897_);
lean_dec(v_stop_897_);
v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go_spec__0(v_pu_boxed_905_, v_as_895_, v_i_boxed_906_, v_stop_boxed_907_, v_b_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v_as_895_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed(lean_object* v_pu_909_, lean_object* v_c_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
uint8_t v_pu_boxed_917_; lean_object* v_res_918_; 
v_pu_boxed_917_ = lean_unbox(v_pu_909_);
v_res_918_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go(v_pu_boxed_917_, v_c_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
return v_res_918_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(lean_object* v_f_919_, lean_object* v_v_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
if (lean_obj_tag(v_v_920_) == 0)
{
lean_object* v_code_927_; lean_object* v___x_928_; 
v_code_927_ = lean_ctor_get(v_v_920_, 0);
lean_inc_ref(v_code_927_);
lean_dec_ref_known(v_v_920_, 1);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
v___x_928_ = lean_apply_7(v_f_919_, v_code_927_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, lean_box(0));
return v___x_928_;
}
else
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v_f_919_);
v_isSharedCheck_936_ = !lean_is_exclusive(v_v_920_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v_v_920_, 0);
lean_dec(v_unused_937_);
v___x_930_ = v_v_920_;
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
else
{
lean_dec(v_v_920_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_box(0);
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 0);
lean_ctor_set(v___x_930_, 0, v___x_932_);
v___x_934_ = v___x_930_;
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
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_919_ = stack[0].m_obj;
lean_object* v_v_920_ = stack[1].m_obj;
lean_object* v___y_921_ = stack[2].m_obj;
lean_object* v___y_922_ = stack[3].m_obj;
lean_object* v___y_923_ = stack[4].m_obj;
lean_object* v___y_924_ = stack[5].m_obj;
lean_object* v___y_925_ = stack[6].m_obj;
lean_object* v_res_938_;
v_res_938_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_919_, v_v_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
stack->m_obj
 = v_res_938_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg___boxed(lean_object* v_f_939_, lean_object* v_v_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_939_, v_v_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
return v_res_947_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(uint8_t v_pu_948_, lean_object* v_f_949_, lean_object* v_v_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v_f_949_, v_v_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
return v___x_957_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_948_ = stack[0].m_num;
lean_object* v_f_949_ = stack[1].m_obj;
lean_object* v_v_950_ = stack[2].m_obj;
lean_object* v___y_951_ = stack[3].m_obj;
lean_object* v___y_952_ = stack[4].m_obj;
lean_object* v___y_953_ = stack[5].m_obj;
lean_object* v___y_954_ = stack[6].m_obj;
lean_object* v___y_955_ = stack[7].m_obj;
lean_object* v_res_958_;
v_res_958_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(v_pu_948_, v_f_949_, v_v_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
stack->m_obj
 = v_res_958_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___boxed(lean_object* v_pu_959_, lean_object* v_f_960_, lean_object* v_v_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
uint8_t v_pu_boxed_968_; lean_object* v_res_969_; 
v_pu_boxed_968_ = lean_unbox(v_pu_959_);
v_res_969_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0(v_pu_boxed_968_, v_f_960_, v_v_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
return v_res_969_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(uint8_t v_pu_970_, lean_object* v_as_971_, size_t v_i_972_, size_t v_stop_973_, lean_object* v_b_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_eq(v_i_972_, v_stop_973_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v_value_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_982_ = lean_array_uget_borrowed(v_as_971_, v_i_972_);
v_value_983_ = lean_ctor_get(v___x_982_, 1);
v___x_984_ = lean_box(v_pu_970_);
v___x_985_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_go___boxed), 8, 1);
lean_closure_set(v___x_985_, 0, v___x_984_);
lean_inc_ref(v_value_983_);
v___x_986_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__0___redArg(v___x_985_, v_value_983_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; size_t v___x_988_; size_t v___x_989_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_988_ = ((size_t)1ULL);
v___x_989_ = lean_usize_add(v_i_972_, v___x_988_);
v_i_972_ = v___x_989_;
v_b_974_ = v_a_987_;
goto _start;
}
else
{
return v___x_986_;
}
}
else
{
lean_object* v___x_991_; 
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v_b_974_);
return v___x_991_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_970_ = stack[0].m_num;
lean_object* v_as_971_ = stack[1].m_obj;
size_t v_i_972_ = stack[2].m_num;
size_t v_stop_973_ = stack[3].m_num;
lean_object* v_b_974_ = stack[4].m_obj;
lean_object* v___y_975_ = stack[5].m_obj;
lean_object* v___y_976_ = stack[6].m_obj;
lean_object* v___y_977_ = stack[7].m_obj;
lean_object* v___y_978_ = stack[8].m_obj;
lean_object* v___y_979_ = stack[9].m_obj;
lean_object* v_res_992_;
v_res_992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_spec__1(v_pu_970_, v_as_971_, v_i_972_, v_stop_973_, v_b_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
stack->m_obj
 = v_res_992_;
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
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(uint8_t v_pu_1008_, lean_object* v_decls_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
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
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1008_ = stack[0].m_num;
lean_object* v_decls_1009_ = stack[1].m_obj;
lean_object* v_a_1010_ = stack[2].m_obj;
lean_object* v_a_1011_ = stack[3].m_obj;
lean_object* v_a_1012_ = stack[4].m_obj;
lean_object* v_a_1013_ = stack[5].m_obj;
lean_object* v_a_1014_ = stack[6].m_obj;
lean_object* v_res_1029_;
v_res_1029_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_1008_, v_decls_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
stack->m_obj
 = v_res_1029_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start___boxed(lean_object* v_pu_1030_, lean_object* v_decls_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
uint8_t v_pu_boxed_1038_; lean_object* v_res_1039_; 
v_pu_boxed_1038_ = lean_unbox(v_pu_1030_);
v_res_1039_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_boxed_1038_, v_decls_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_decls_1031_);
return v_res_1039_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues(uint8_t v_pu_1042_, lean_object* v_decls_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getLetValues___closed__0));
v___x_1050_ = lean_st_mk_ref(v___x_1049_);
v___x_1051_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getLetValues_start(v_pu_1042_, v_decls_1043_, v___x_1050_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v___x_1051_, 0);
lean_dec(v_unused_1060_);
v___x_1053_ = v___x_1051_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v___x_1051_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_st_ref_get(v___x_1050_);
lean_dec(v___x_1050_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v___x_1050_);
v_a_1061_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1051_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1051_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_getLetValues_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1042_ = stack[0].m_num;
lean_object* v_decls_1043_ = stack[1].m_obj;
lean_object* v_a_1044_ = stack[2].m_obj;
lean_object* v_a_1045_ = stack[3].m_obj;
lean_object* v_a_1046_ = stack[4].m_obj;
lean_object* v_a_1047_ = stack[5].m_obj;
lean_object* v_res_1069_;
v_res_1069_ = l_Lean_Compiler_LCNF_Probe_getLetValues(v_pu_1042_, v_decls_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
stack->m_obj
 = v_res_1069_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getLetValues___boxed(lean_object* v_pu_1070_, lean_object* v_decls_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
uint8_t v_pu_boxed_1077_; lean_object* v_res_1078_; 
v_pu_boxed_1077_ = lean_unbox(v_pu_1070_);
v_res_1078_ = l_Lean_Compiler_LCNF_Probe_getLetValues(v_pu_boxed_1077_, v_decls_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec_ref(v_decls_1071_);
return v_res_1078_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(uint8_t v_pu_1079_, lean_object* v_code_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
switch(lean_obj_tag(v_code_1080_))
{
case 0:
{
lean_object* v_k_1087_; 
v_k_1087_ = lean_ctor_get(v_code_1080_, 1);
lean_inc_ref(v_k_1087_);
lean_dec_ref_known(v_code_1080_, 2);
v_code_1080_ = v_k_1087_;
goto _start;
}
case 1:
{
lean_object* v_decl_1089_; lean_object* v_k_1090_; lean_object* v_value_1091_; lean_object* v___x_1092_; 
v_decl_1089_ = lean_ctor_get(v_code_1080_, 0);
lean_inc_ref(v_decl_1089_);
v_k_1090_ = lean_ctor_get(v_code_1080_, 1);
lean_inc_ref(v_k_1090_);
lean_dec_ref_known(v_code_1080_, 2);
v_value_1091_ = lean_ctor_get(v_decl_1089_, 4);
lean_inc_ref(v_value_1091_);
lean_dec_ref(v_decl_1089_);
v___x_1092_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1079_, v_value_1091_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_dec_ref_known(v___x_1092_, 1);
v_code_1080_ = v_k_1090_;
goto _start;
}
else
{
lean_dec_ref(v_k_1090_);
return v___x_1092_;
}
}
case 2:
{
lean_object* v_decl_1094_; lean_object* v_k_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_value_1099_; lean_object* v___x_1100_; 
v_decl_1094_ = lean_ctor_get(v_code_1080_, 0);
lean_inc_ref_n(v_decl_1094_, 2);
v_k_1095_ = lean_ctor_get(v_code_1080_, 1);
lean_inc_ref(v_k_1095_);
lean_dec_ref_known(v_code_1080_, 2);
v___x_1096_ = lean_st_ref_take(v_a_1081_);
v___x_1097_ = lean_array_push(v___x_1096_, v_decl_1094_);
v___x_1098_ = lean_st_ref_put(v_a_1081_, v___x_1097_);
v_value_1099_ = lean_ctor_get(v_decl_1094_, 4);
lean_inc_ref(v_value_1099_);
lean_dec_ref(v_decl_1094_);
v___x_1100_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1079_, v_value_1099_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_dec_ref_known(v___x_1100_, 1);
v_code_1080_ = v_k_1095_;
goto _start;
}
else
{
lean_dec_ref(v_k_1095_);
return v___x_1100_;
}
}
case 4:
{
lean_object* v_cases_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1124_; 
v_cases_1102_ = lean_ctor_get(v_code_1080_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_code_1080_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1104_ = v_code_1080_;
v_isShared_1105_ = v_isSharedCheck_1124_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_cases_1102_);
lean_dec(v_code_1080_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1124_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_alts_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_alts_1106_ = lean_ctor_get(v_cases_1102_, 3);
lean_inc_ref(v_alts_1106_);
lean_dec_ref(v_cases_1102_);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_array_get_size(v_alts_1106_);
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_nat_dec_lt(v___x_1107_, v___x_1108_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1112_; 
lean_dec_ref(v_alts_1106_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set_tag(v___x_1104_, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1109_);
v___x_1112_ = v___x_1104_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1109_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_nat_dec_le(v___x_1108_, v___x_1108_);
if (v___x_1114_ == 0)
{
if (v___x_1110_ == 0)
{
lean_object* v___x_1116_; 
lean_dec_ref(v_alts_1106_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set_tag(v___x_1104_, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1109_);
v___x_1116_ = v___x_1104_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1109_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
else
{
size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
lean_del_object(v___x_1104_);
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = lean_usize_of_nat(v___x_1108_);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1079_, v_alts_1106_, v___x_1118_, v___x_1119_, v___x_1109_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec_ref(v_alts_1106_);
return v___x_1120_;
}
}
else
{
size_t v___x_1121_; size_t v___x_1122_; lean_object* v___x_1123_; 
lean_del_object(v___x_1104_);
v___x_1121_ = ((size_t)0ULL);
v___x_1122_ = lean_usize_of_nat(v___x_1108_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1079_, v_alts_1106_, v___x_1121_, v___x_1122_, v___x_1109_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec_ref(v_alts_1106_);
return v___x_1123_;
}
}
}
}
case 7:
{
lean_object* v_k_1125_; 
v_k_1125_ = lean_ctor_get(v_code_1080_, 3);
lean_inc_ref(v_k_1125_);
lean_dec_ref_known(v_code_1080_, 4);
v_code_1080_ = v_k_1125_;
goto _start;
}
case 8:
{
lean_object* v_k_1127_; 
v_k_1127_ = lean_ctor_get(v_code_1080_, 3);
lean_inc_ref(v_k_1127_);
lean_dec_ref_known(v_code_1080_, 4);
v_code_1080_ = v_k_1127_;
goto _start;
}
case 9:
{
lean_object* v_k_1129_; 
v_k_1129_ = lean_ctor_get(v_code_1080_, 5);
lean_inc_ref(v_k_1129_);
lean_dec_ref_known(v_code_1080_, 6);
v_code_1080_ = v_k_1129_;
goto _start;
}
case 10:
{
lean_object* v_k_1131_; 
v_k_1131_ = lean_ctor_get(v_code_1080_, 2);
lean_inc_ref(v_k_1131_);
lean_dec_ref_known(v_code_1080_, 3);
v_code_1080_ = v_k_1131_;
goto _start;
}
case 11:
{
lean_object* v_k_1133_; 
v_k_1133_ = lean_ctor_get(v_code_1080_, 2);
lean_inc_ref(v_k_1133_);
lean_dec_ref_known(v_code_1080_, 3);
v_code_1080_ = v_k_1133_;
goto _start;
}
case 12:
{
lean_object* v_k_1135_; 
v_k_1135_ = lean_ctor_get(v_code_1080_, 3);
lean_inc_ref(v_k_1135_);
lean_dec_ref_known(v_code_1080_, 4);
v_code_1080_ = v_k_1135_;
goto _start;
}
case 13:
{
lean_object* v_k_1137_; 
v_k_1137_ = lean_ctor_get(v_code_1080_, 1);
lean_inc_ref(v_k_1137_);
lean_dec_ref_known(v_code_1080_, 2);
v_code_1080_ = v_k_1137_;
goto _start;
}
default: 
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v_code_1080_);
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1079_ = stack[0].m_num;
lean_object* v_code_1080_ = stack[1].m_obj;
lean_object* v_a_1081_ = stack[2].m_obj;
lean_object* v_a_1082_ = stack[3].m_obj;
lean_object* v_a_1083_ = stack[4].m_obj;
lean_object* v_a_1084_ = stack[5].m_obj;
lean_object* v_a_1085_ = stack[6].m_obj;
lean_object* v_res_1141_;
v_res_1141_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1079_, v_code_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
stack->m_obj
 = v_res_1141_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(uint8_t v_pu_1142_, lean_object* v_as_1143_, size_t v_i_1144_, size_t v_stop_1145_, lean_object* v_b_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___y_1154_; uint8_t v___x_1160_; 
v___x_1160_ = lean_usize_dec_eq(v_i_1144_, v_stop_1145_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_array_uget_borrowed(v_as_1143_, v_i_1144_);
switch(lean_obj_tag(v___x_1161_))
{
case 0:
{
lean_object* v_code_1162_; 
v_code_1162_ = lean_ctor_get(v___x_1161_, 2);
lean_inc_ref(v_code_1162_);
v___y_1154_ = v_code_1162_;
goto v___jp_1153_;
}
case 1:
{
lean_object* v_code_1163_; 
v_code_1163_ = lean_ctor_get(v___x_1161_, 1);
lean_inc_ref(v_code_1163_);
v___y_1154_ = v_code_1163_;
goto v___jp_1153_;
}
default: 
{
lean_object* v_code_1164_; 
v_code_1164_ = lean_ctor_get(v___x_1161_, 0);
lean_inc_ref(v_code_1164_);
v___y_1154_ = v_code_1164_;
goto v___jp_1153_;
}
}
}
else
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v_b_1146_);
return v___x_1165_;
}
v___jp_1153_:
{
lean_object* v___x_1155_; 
v___x_1155_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_1142_, v___y_1154_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; size_t v___x_1157_; size_t v___x_1158_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = ((size_t)1ULL);
v___x_1158_ = lean_usize_add(v_i_1144_, v___x_1157_);
v_i_1144_ = v___x_1158_;
v_b_1146_ = v_a_1156_;
goto _start;
}
else
{
return v___x_1155_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1142_ = stack[0].m_num;
lean_object* v_as_1143_ = stack[1].m_obj;
size_t v_i_1144_ = stack[2].m_num;
size_t v_stop_1145_ = stack[3].m_num;
lean_object* v_b_1146_ = stack[4].m_obj;
lean_object* v___y_1147_ = stack[5].m_obj;
lean_object* v___y_1148_ = stack[6].m_obj;
lean_object* v___y_1149_ = stack[7].m_obj;
lean_object* v___y_1150_ = stack[8].m_obj;
lean_object* v___y_1151_ = stack[9].m_obj;
lean_object* v_res_1166_;
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_1142_, v_as_1143_, v_i_1144_, v_stop_1145_, v_b_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
stack->m_obj
 = v_res_1166_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0___boxed(lean_object* v_pu_1167_, lean_object* v_as_1168_, lean_object* v_i_1169_, lean_object* v_stop_1170_, lean_object* v_b_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
uint8_t v_pu_boxed_1178_; size_t v_i_boxed_1179_; size_t v_stop_boxed_1180_; lean_object* v_res_1181_; 
v_pu_boxed_1178_ = lean_unbox(v_pu_1167_);
v_i_boxed_1179_ = lean_unbox_usize(v_i_1169_);
lean_dec(v_i_1169_);
v_stop_boxed_1180_ = lean_unbox_usize(v_stop_1170_);
lean_dec(v_stop_1170_);
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go_spec__0(v_pu_boxed_1178_, v_as_1168_, v_i_boxed_1179_, v_stop_boxed_1180_, v_b_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v_as_1168_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed(lean_object* v_pu_1182_, lean_object* v_code_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
uint8_t v_pu_boxed_1190_; lean_object* v_res_1191_; 
v_pu_boxed_1190_ = lean_unbox(v_pu_1182_);
v_res_1191_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go(v_pu_boxed_1190_, v_code_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
return v_res_1191_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(lean_object* v_f_1192_, lean_object* v_v_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
if (lean_obj_tag(v_v_1193_) == 0)
{
lean_object* v_code_1200_; lean_object* v___x_1201_; 
v_code_1200_ = lean_ctor_get(v_v_1193_, 0);
lean_inc_ref(v_code_1200_);
lean_dec_ref_known(v_v_1193_, 1);
lean_inc(v___y_1198_);
lean_inc_ref(v___y_1197_);
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1195_);
lean_inc(v___y_1194_);
v___x_1201_ = lean_apply_7(v_f_1192_, v_code_1200_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, lean_box(0));
return v___x_1201_;
}
else
{
lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_f_1192_);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_v_1193_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v_v_1193_, 0);
lean_dec(v_unused_1210_);
v___x_1203_ = v_v_1193_;
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
else
{
lean_dec(v_v_1193_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1209_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = lean_box(0);
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1192_ = stack[0].m_obj;
lean_object* v_v_1193_ = stack[1].m_obj;
lean_object* v___y_1194_ = stack[2].m_obj;
lean_object* v___y_1195_ = stack[3].m_obj;
lean_object* v___y_1196_ = stack[4].m_obj;
lean_object* v___y_1197_ = stack[5].m_obj;
lean_object* v___y_1198_ = stack[6].m_obj;
lean_object* v_res_1211_;
v_res_1211_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1192_, v_v_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
stack->m_obj
 = v_res_1211_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg___boxed(lean_object* v_f_1212_, lean_object* v_v_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1212_, v_v_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
return v_res_1220_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(uint8_t v_pu_1221_, lean_object* v_f_1222_, lean_object* v_v_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v_f_1222_, v_v_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1221_ = stack[0].m_num;
lean_object* v_f_1222_ = stack[1].m_obj;
lean_object* v_v_1223_ = stack[2].m_obj;
lean_object* v___y_1224_ = stack[3].m_obj;
lean_object* v___y_1225_ = stack[4].m_obj;
lean_object* v___y_1226_ = stack[5].m_obj;
lean_object* v___y_1227_ = stack[6].m_obj;
lean_object* v___y_1228_ = stack[7].m_obj;
lean_object* v_res_1231_;
v_res_1231_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(v_pu_1221_, v_f_1222_, v_v_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___boxed(lean_object* v_pu_1232_, lean_object* v_f_1233_, lean_object* v_v_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
uint8_t v_pu_boxed_1241_; lean_object* v_res_1242_; 
v_pu_boxed_1241_ = lean_unbox(v_pu_1232_);
v_res_1242_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0(v_pu_boxed_1241_, v_f_1233_, v_v_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
return v_res_1242_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(uint8_t v_pu_1243_, lean_object* v_as_1244_, size_t v_i_1245_, size_t v_stop_1246_, lean_object* v_b_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_eq(v_i_1245_, v_stop_1246_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v_value_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1255_ = lean_array_uget_borrowed(v_as_1244_, v_i_1245_);
v_value_1256_ = lean_ctor_get(v___x_1255_, 1);
v___x_1257_ = lean_box(v_pu_1243_);
v___x_1258_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_go___boxed), 8, 1);
lean_closure_set(v___x_1258_, 0, v___x_1257_);
lean_inc_ref(v_value_1256_);
v___x_1259_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__0___redArg(v___x_1258_, v_value_1256_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; size_t v___x_1261_; size_t v___x_1262_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v___x_1261_ = ((size_t)1ULL);
v___x_1262_ = lean_usize_add(v_i_1245_, v___x_1261_);
v_i_1245_ = v___x_1262_;
v_b_1247_ = v_a_1260_;
goto _start;
}
else
{
return v___x_1259_;
}
}
else
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_b_1247_);
return v___x_1264_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1243_ = stack[0].m_num;
lean_object* v_as_1244_ = stack[1].m_obj;
size_t v_i_1245_ = stack[2].m_num;
size_t v_stop_1246_ = stack[3].m_num;
lean_object* v_b_1247_ = stack[4].m_obj;
lean_object* v___y_1248_ = stack[5].m_obj;
lean_object* v___y_1249_ = stack[6].m_obj;
lean_object* v___y_1250_ = stack[7].m_obj;
lean_object* v___y_1251_ = stack[8].m_obj;
lean_object* v___y_1252_ = stack[9].m_obj;
lean_object* v_res_1265_;
v_res_1265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1243_, v_as_1244_, v_i_1245_, v_stop_1246_, v_b_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
stack->m_obj
 = v_res_1265_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1___boxed(lean_object* v_pu_1266_, lean_object* v_as_1267_, lean_object* v_i_1268_, lean_object* v_stop_1269_, lean_object* v_b_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v_pu_boxed_1277_; size_t v_i_boxed_1278_; size_t v_stop_boxed_1279_; lean_object* v_res_1280_; 
v_pu_boxed_1277_ = lean_unbox(v_pu_1266_);
v_i_boxed_1278_ = lean_unbox_usize(v_i_1268_);
lean_dec(v_i_1268_);
v_stop_boxed_1279_ = lean_unbox_usize(v_stop_1269_);
lean_dec(v_stop_1269_);
v_res_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_boxed_1277_, v_as_1267_, v_i_boxed_1278_, v_stop_boxed_1279_, v_b_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v_as_1267_);
return v_res_1280_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(uint8_t v_pu_1281_, lean_object* v_decls_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_array_get_size(v_decls_1282_);
v___x_1291_ = lean_box(0);
v___x_1292_ = lean_nat_dec_lt(v___x_1289_, v___x_1290_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
return v___x_1293_;
}
else
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_nat_dec_le(v___x_1290_, v___x_1290_);
if (v___x_1294_ == 0)
{
if (v___x_1292_ == 0)
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1291_);
return v___x_1295_;
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = lean_usize_of_nat(v___x_1290_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1281_, v_decls_1282_, v___x_1296_, v___x_1297_, v___x_1291_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
return v___x_1298_;
}
}
else
{
size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = ((size_t)0ULL);
v___x_1300_ = lean_usize_of_nat(v___x_1290_);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_spec__1(v_pu_1281_, v_decls_1282_, v___x_1299_, v___x_1300_, v___x_1291_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
return v___x_1301_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1281_ = stack[0].m_num;
lean_object* v_decls_1282_ = stack[1].m_obj;
lean_object* v_a_1283_ = stack[2].m_obj;
lean_object* v_a_1284_ = stack[3].m_obj;
lean_object* v_a_1285_ = stack[4].m_obj;
lean_object* v_a_1286_ = stack[5].m_obj;
lean_object* v_a_1287_ = stack[6].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_1281_, v_decls_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start___boxed(lean_object* v_pu_1303_, lean_object* v_decls_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
uint8_t v_pu_boxed_1311_; lean_object* v_res_1312_; 
v_pu_boxed_1311_ = lean_unbox(v_pu_1303_);
v_res_1312_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_boxed_1311_, v_decls_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_decls_1304_);
return v_res_1312_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_getJps(uint8_t v_pu_1315_, lean_object* v_decls_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_getJps___closed__0));
v___x_1323_ = lean_st_mk_ref(v___x_1322_);
v___x_1324_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_getJps_start(v_pu_1315_, v_decls_1316_, v___x_1323_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1332_; 
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v___x_1324_, 0);
lean_dec(v_unused_1333_);
v___x_1326_ = v___x_1324_;
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v___x_1324_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = lean_st_ref_get(v___x_1323_);
lean_dec(v___x_1323_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1328_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v___x_1323_);
v_a_1334_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1324_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1324_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_getJps_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1315_ = stack[0].m_num;
lean_object* v_decls_1316_ = stack[1].m_obj;
lean_object* v_a_1317_ = stack[2].m_obj;
lean_object* v_a_1318_ = stack[3].m_obj;
lean_object* v_a_1319_ = stack[4].m_obj;
lean_object* v_a_1320_ = stack[5].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l_Lean_Compiler_LCNF_Probe_getJps(v_pu_1315_, v_decls_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_getJps___boxed(lean_object* v_pu_1343_, lean_object* v_decls_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
uint8_t v_pu_boxed_1350_; lean_object* v_res_1351_; 
v_pu_boxed_1350_ = lean_unbox(v_pu_1343_);
v_res_1351_ = l_Lean_Compiler_LCNF_Probe_getJps(v_pu_boxed_1350_, v_decls_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec_ref(v_decls_1344_);
return v_res_1351_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(uint8_t v_pu_1352_, lean_object* v_f_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
switch(lean_obj_tag(v_a_1354_))
{
case 0:
{
lean_object* v_decl_1360_; lean_object* v_k_1361_; lean_object* v___x_1362_; 
v_decl_1360_ = lean_ctor_get(v_a_1354_, 0);
lean_inc_ref(v_decl_1360_);
v_k_1361_ = lean_ctor_get(v_a_1354_, 1);
lean_inc_ref(v_k_1361_);
lean_dec_ref_known(v_a_1354_, 2);
lean_inc_ref(v_f_1353_);
lean_inc(v_a_1358_);
lean_inc_ref(v_a_1357_);
lean_inc(v_a_1356_);
lean_inc_ref(v_a_1355_);
v___x_1362_ = lean_apply_6(v_f_1353_, v_decl_1360_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, lean_box(0));
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; uint8_t v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
v___x_1364_ = lean_unbox(v_a_1363_);
lean_dec(v_a_1363_);
if (v___x_1364_ == 0)
{
lean_dec_ref_known(v___x_1362_, 1);
v_a_1354_ = v_k_1361_;
goto _start;
}
else
{
lean_dec_ref(v_k_1361_);
lean_dec_ref(v_f_1353_);
return v___x_1362_;
}
}
else
{
lean_dec_ref(v_k_1361_);
lean_dec_ref(v_f_1353_);
return v___x_1362_;
}
}
case 1:
{
lean_object* v_decl_1366_; lean_object* v_k_1367_; lean_object* v_value_1368_; lean_object* v___x_1369_; 
v_decl_1366_ = lean_ctor_get(v_a_1354_, 0);
lean_inc_ref(v_decl_1366_);
v_k_1367_ = lean_ctor_get(v_a_1354_, 1);
lean_inc_ref(v_k_1367_);
lean_dec_ref_known(v_a_1354_, 2);
v_value_1368_ = lean_ctor_get(v_decl_1366_, 4);
lean_inc_ref(v_value_1368_);
lean_dec_ref(v_decl_1366_);
lean_inc_ref(v_f_1353_);
v___x_1369_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1352_, v_f_1353_, v_value_1368_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; uint8_t v___x_1371_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v___x_1371_ = lean_unbox(v_a_1370_);
if (v___x_1371_ == 0)
{
lean_dec_ref_known(v___x_1369_, 1);
v_a_1354_ = v_k_1367_;
goto _start;
}
else
{
lean_dec_ref(v_k_1367_);
lean_dec_ref(v_f_1353_);
return v___x_1369_;
}
}
else
{
lean_dec_ref(v_k_1367_);
lean_dec_ref(v_f_1353_);
return v___x_1369_;
}
}
case 2:
{
lean_object* v_decl_1373_; lean_object* v_k_1374_; lean_object* v_value_1375_; lean_object* v___x_1376_; 
v_decl_1373_ = lean_ctor_get(v_a_1354_, 0);
lean_inc_ref(v_decl_1373_);
v_k_1374_ = lean_ctor_get(v_a_1354_, 1);
lean_inc_ref(v_k_1374_);
lean_dec_ref_known(v_a_1354_, 2);
v_value_1375_ = lean_ctor_get(v_decl_1373_, 4);
lean_inc_ref(v_value_1375_);
lean_dec_ref(v_decl_1373_);
lean_inc_ref(v_f_1353_);
v___x_1376_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1352_, v_f_1353_, v_value_1375_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; uint8_t v___x_1378_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v___x_1378_ = lean_unbox(v_a_1377_);
if (v___x_1378_ == 0)
{
lean_dec_ref_known(v___x_1376_, 1);
v_a_1354_ = v_k_1374_;
goto _start;
}
else
{
lean_dec_ref(v_k_1374_);
lean_dec_ref(v_f_1353_);
return v___x_1376_;
}
}
else
{
lean_dec_ref(v_k_1374_);
lean_dec_ref(v_f_1353_);
return v___x_1376_;
}
}
case 4:
{
lean_object* v_cases_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1399_; 
v_cases_1380_ = lean_ctor_get(v_a_1354_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_a_1354_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1382_ = v_a_1354_;
v_isShared_1383_ = v_isSharedCheck_1399_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_cases_1380_);
lean_dec(v_a_1354_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1399_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_alts_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_alts_1384_ = lean_ctor_get(v_cases_1380_, 3);
lean_inc_ref(v_alts_1384_);
lean_dec_ref(v_cases_1380_);
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = lean_array_get_size(v_alts_1384_);
v___x_1387_ = lean_nat_dec_lt(v___x_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
lean_dec_ref(v_alts_1384_);
lean_dec_ref(v_f_1353_);
v___x_1388_ = lean_box(v___x_1387_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1388_);
v___x_1390_ = v___x_1382_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
if (v___x_1387_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
lean_dec_ref(v_alts_1384_);
lean_dec_ref(v_f_1353_);
v___x_1392_ = lean_box(v___x_1387_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1392_);
v___x_1394_ = v___x_1382_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
else
{
size_t v___x_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
lean_del_object(v___x_1382_);
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = lean_usize_of_nat(v___x_1386_);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_1352_, v_f_1353_, v_alts_1384_, v___x_1396_, v___x_1397_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec_ref(v_alts_1384_);
return v___x_1398_;
}
}
}
}
case 7:
{
lean_object* v_k_1400_; 
v_k_1400_ = lean_ctor_get(v_a_1354_, 3);
lean_inc_ref(v_k_1400_);
lean_dec_ref_known(v_a_1354_, 4);
v_a_1354_ = v_k_1400_;
goto _start;
}
case 8:
{
lean_object* v_k_1402_; 
v_k_1402_ = lean_ctor_get(v_a_1354_, 3);
lean_inc_ref(v_k_1402_);
lean_dec_ref_known(v_a_1354_, 4);
v_a_1354_ = v_k_1402_;
goto _start;
}
case 9:
{
lean_object* v_k_1404_; 
v_k_1404_ = lean_ctor_get(v_a_1354_, 5);
lean_inc_ref(v_k_1404_);
lean_dec_ref_known(v_a_1354_, 6);
v_a_1354_ = v_k_1404_;
goto _start;
}
case 10:
{
lean_object* v_k_1406_; 
v_k_1406_ = lean_ctor_get(v_a_1354_, 2);
lean_inc_ref(v_k_1406_);
lean_dec_ref_known(v_a_1354_, 3);
v_a_1354_ = v_k_1406_;
goto _start;
}
case 11:
{
lean_object* v_k_1408_; 
v_k_1408_ = lean_ctor_get(v_a_1354_, 2);
lean_inc_ref(v_k_1408_);
lean_dec_ref_known(v_a_1354_, 3);
v_a_1354_ = v_k_1408_;
goto _start;
}
case 12:
{
lean_object* v_k_1410_; 
v_k_1410_ = lean_ctor_get(v_a_1354_, 3);
lean_inc_ref(v_k_1410_);
lean_dec_ref_known(v_a_1354_, 4);
v_a_1354_ = v_k_1410_;
goto _start;
}
case 13:
{
lean_object* v_k_1412_; 
v_k_1412_ = lean_ctor_get(v_a_1354_, 1);
lean_inc_ref(v_k_1412_);
lean_dec_ref_known(v_a_1354_, 2);
v_a_1354_ = v_k_1412_;
goto _start;
}
default: 
{
uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec_ref(v_a_1354_);
lean_dec_ref(v_f_1353_);
v___x_1414_ = 0;
v___x_1415_ = lean_box(v___x_1414_);
v___x_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1352_ = stack[0].m_num;
lean_object* v_f_1353_ = stack[1].m_obj;
lean_object* v_a_1354_ = stack[2].m_obj;
lean_object* v_a_1355_ = stack[3].m_obj;
lean_object* v_a_1356_ = stack[4].m_obj;
lean_object* v_a_1357_ = stack[5].m_obj;
lean_object* v_a_1358_ = stack[6].m_obj;
lean_object* v_res_1417_;
v_res_1417_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1352_, v_f_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
stack->m_obj
 = v_res_1417_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(uint8_t v_pu_1418_, lean_object* v_f_1419_, lean_object* v_as_1420_, size_t v_i_1421_, size_t v_stop_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_usize_dec_eq(v_i_1421_, v_stop_1422_);
if (v___x_1428_ == 0)
{
uint8_t v___x_1429_; lean_object* v___y_1431_; lean_object* v___x_1446_; 
v___x_1429_ = 1;
v___x_1446_ = lean_array_uget_borrowed(v_as_1420_, v_i_1421_);
switch(lean_obj_tag(v___x_1446_))
{
case 0:
{
lean_object* v_code_1447_; 
v_code_1447_ = lean_ctor_get(v___x_1446_, 2);
lean_inc_ref(v_code_1447_);
v___y_1431_ = v_code_1447_;
goto v___jp_1430_;
}
case 1:
{
lean_object* v_code_1448_; 
v_code_1448_ = lean_ctor_get(v___x_1446_, 1);
lean_inc_ref(v_code_1448_);
v___y_1431_ = v_code_1448_;
goto v___jp_1430_;
}
default: 
{
lean_object* v_code_1449_; 
v_code_1449_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_ref(v_code_1449_);
v___y_1431_ = v_code_1449_;
goto v___jp_1430_;
}
}
v___jp_1430_:
{
lean_object* v___x_1432_; 
lean_inc_ref(v_f_1419_);
v___x_1432_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_1418_, v_f_1419_, v___y_1431_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1445_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1445_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1445_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_unbox(v_a_1433_);
lean_dec(v_a_1433_);
if (v___x_1437_ == 0)
{
size_t v___x_1438_; size_t v___x_1439_; 
lean_del_object(v___x_1435_);
v___x_1438_ = ((size_t)1ULL);
v___x_1439_ = lean_usize_add(v_i_1421_, v___x_1438_);
v_i_1421_ = v___x_1439_;
goto _start;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
lean_dec_ref(v_f_1419_);
v___x_1441_ = lean_box(v___x_1429_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1441_);
v___x_1443_ = v___x_1435_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_dec_ref(v_f_1419_);
return v___x_1432_;
}
}
}
else
{
uint8_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec_ref(v_f_1419_);
v___x_1450_ = 0;
v___x_1451_ = lean_box(v___x_1450_);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1418_ = stack[0].m_num;
lean_object* v_f_1419_ = stack[1].m_obj;
lean_object* v_as_1420_ = stack[2].m_obj;
size_t v_i_1421_ = stack[3].m_num;
size_t v_stop_1422_ = stack[4].m_num;
lean_object* v___y_1423_ = stack[5].m_obj;
lean_object* v___y_1424_ = stack[6].m_obj;
lean_object* v___y_1425_ = stack[7].m_obj;
lean_object* v___y_1426_ = stack[8].m_obj;
lean_object* v_res_1453_;
v_res_1453_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_1418_, v_f_1419_, v_as_1420_, v_i_1421_, v_stop_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
stack->m_obj
 = v_res_1453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0___boxed(lean_object* v_pu_1454_, lean_object* v_f_1455_, lean_object* v_as_1456_, lean_object* v_i_1457_, lean_object* v_stop_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v_pu_boxed_1464_; size_t v_i_boxed_1465_; size_t v_stop_boxed_1466_; lean_object* v_res_1467_; 
v_pu_boxed_1464_ = lean_unbox(v_pu_1454_);
v_i_boxed_1465_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_stop_boxed_1466_ = lean_unbox_usize(v_stop_1458_);
lean_dec(v_stop_1458_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go_spec__0(v_pu_boxed_1464_, v_f_1455_, v_as_1456_, v_i_boxed_1465_, v_stop_boxed_1466_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec_ref(v_as_1456_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed(lean_object* v_pu_1468_, lean_object* v_f_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
uint8_t v_pu_boxed_1476_; lean_object* v_res_1477_; 
v_pu_boxed_1476_ = lean_unbox(v_pu_1468_);
v_res_1477_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go(v_pu_boxed_1476_, v_f_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec(v_a_1472_);
lean_dec_ref(v_a_1471_);
return v_res_1477_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(lean_object* v_v_1478_, lean_object* v_f_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
if (lean_obj_tag(v_v_1478_) == 0)
{
lean_object* v_code_1485_; lean_object* v___x_1486_; 
v_code_1485_ = lean_ctor_get(v_v_1478_, 0);
lean_inc_ref(v_code_1485_);
lean_dec_ref_known(v_v_1478_, 1);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
v___x_1486_ = lean_apply_6(v_f_1479_, v_code_1485_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
return v___x_1486_;
}
else
{
lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1495_; 
lean_dec_ref(v_f_1479_);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_v_1478_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v_v_1478_, 0);
lean_dec(v_unused_1496_);
v___x_1488_ = v_v_1478_;
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
else
{
lean_dec(v_v_1478_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1495_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
uint8_t v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1490_ = 0;
v___x_1491_ = lean_box(v___x_1490_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1491_);
v___x_1493_ = v___x_1488_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1478_ = stack[0].m_obj;
lean_object* v_f_1479_ = stack[1].m_obj;
lean_object* v___y_1480_ = stack[2].m_obj;
lean_object* v___y_1481_ = stack[3].m_obj;
lean_object* v___y_1482_ = stack[4].m_obj;
lean_object* v___y_1483_ = stack[5].m_obj;
lean_object* v_res_1497_;
v_res_1497_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1478_, v_f_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_);
stack->m_obj
 = v_res_1497_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg___boxed(lean_object* v_v_1498_, lean_object* v_f_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1498_, v_f_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1505_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(uint8_t v_pu_1506_, lean_object* v_v_1507_, lean_object* v_f_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_v_1507_, v_f_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1506_ = stack[0].m_num;
lean_object* v_v_1507_ = stack[1].m_obj;
lean_object* v_f_1508_ = stack[2].m_obj;
lean_object* v___y_1509_ = stack[3].m_obj;
lean_object* v___y_1510_ = stack[4].m_obj;
lean_object* v___y_1511_ = stack[5].m_obj;
lean_object* v___y_1512_ = stack[6].m_obj;
lean_object* v_res_1515_;
v_res_1515_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(v_pu_1506_, v_v_1507_, v_f_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
stack->m_obj
 = v_res_1515_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___boxed(lean_object* v_pu_1516_, lean_object* v_v_1517_, lean_object* v_f_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
uint8_t v_pu_boxed_1524_; lean_object* v_res_1525_; 
v_pu_boxed_1524_ = lean_unbox(v_pu_1516_);
v_res_1525_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0(v_pu_boxed_1524_, v_v_1517_, v_f_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
return v_res_1525_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(uint8_t v_pu_1526_, lean_object* v_f_1527_, lean_object* v_as_1528_, size_t v_i_1529_, size_t v_stop_1530_, lean_object* v_b_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_a_1538_; uint8_t v___x_1542_; 
v___x_1542_ = lean_usize_dec_eq(v_i_1529_, v_stop_1530_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v_value_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1543_ = lean_array_uget_borrowed(v_as_1528_, v_i_1529_);
v_value_1544_ = lean_ctor_get(v___x_1543_, 1);
v___x_1545_ = lean_box(v_pu_1526_);
lean_inc_ref(v_f_1527_);
v___x_1546_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByLet_go___boxed), 8, 2);
lean_closure_set(v___x_1546_, 0, v___x_1545_);
lean_closure_set(v___x_1546_, 1, v_f_1527_);
lean_inc_ref(v_value_1544_);
v___x_1547_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1544_, v___x_1546_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; uint8_t v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v___x_1549_ = lean_unbox(v_a_1548_);
lean_dec(v_a_1548_);
if (v___x_1549_ == 0)
{
v_a_1538_ = v_b_1531_;
goto v___jp_1537_;
}
else
{
lean_object* v___x_1550_; 
lean_inc(v___x_1543_);
v___x_1550_ = lean_array_push(v_b_1531_, v___x_1543_);
v_a_1538_ = v___x_1550_;
goto v___jp_1537_;
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v_b_1531_);
lean_dec_ref(v_f_1527_);
v_a_1551_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1547_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1547_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v___x_1559_; 
lean_dec_ref(v_f_1527_);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v_b_1531_);
return v___x_1559_;
}
v___jp_1537_:
{
size_t v___x_1539_; size_t v___x_1540_; 
v___x_1539_ = ((size_t)1ULL);
v___x_1540_ = lean_usize_add(v_i_1529_, v___x_1539_);
v_i_1529_ = v___x_1540_;
v_b_1531_ = v_a_1538_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1526_ = stack[0].m_num;
lean_object* v_f_1527_ = stack[1].m_obj;
lean_object* v_as_1528_ = stack[2].m_obj;
size_t v_i_1529_ = stack[3].m_num;
size_t v_stop_1530_ = stack[4].m_num;
lean_object* v_b_1531_ = stack[5].m_obj;
lean_object* v___y_1532_ = stack[6].m_obj;
lean_object* v___y_1533_ = stack[7].m_obj;
lean_object* v___y_1534_ = stack[8].m_obj;
lean_object* v___y_1535_ = stack[9].m_obj;
lean_object* v_res_1560_;
v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1526_, v_f_1527_, v_as_1528_, v_i_1529_, v_stop_1530_, v_b_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
stack->m_obj
 = v_res_1560_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1___boxed(lean_object* v_pu_1561_, lean_object* v_f_1562_, lean_object* v_as_1563_, lean_object* v_i_1564_, lean_object* v_stop_1565_, lean_object* v_b_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
uint8_t v_pu_boxed_1572_; size_t v_i_boxed_1573_; size_t v_stop_boxed_1574_; lean_object* v_res_1575_; 
v_pu_boxed_1572_ = lean_unbox(v_pu_1561_);
v_i_boxed_1573_ = lean_unbox_usize(v_i_1564_);
lean_dec(v_i_1564_);
v_stop_boxed_1574_ = lean_unbox_usize(v_stop_1565_);
lean_dec(v_stop_1565_);
v_res_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_boxed_1572_, v_f_1562_, v_as_1563_, v_i_boxed_1573_, v_stop_boxed_1574_, v_b_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_as_1563_);
return v_res_1575_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet(uint8_t v_pu_1578_, lean_object* v_f_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = lean_array_get_size(v_a_1580_);
v___x_1588_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1589_ = lean_nat_dec_lt(v___x_1586_, v___x_1587_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; 
lean_dec_ref(v_f_1579_);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
return v___x_1590_;
}
else
{
size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = ((size_t)0ULL);
v___x_1592_ = lean_usize_of_nat(v___x_1587_);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__1(v_pu_1578_, v_f_1579_, v_a_1580_, v___x_1591_, v___x_1592_, v___x_1588_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
return v___x_1593_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filterByLet_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1578_ = stack[0].m_num;
lean_object* v_f_1579_ = stack[1].m_obj;
lean_object* v_a_1580_ = stack[2].m_obj;
lean_object* v_a_1581_ = stack[3].m_obj;
lean_object* v_a_1582_ = stack[4].m_obj;
lean_object* v_a_1583_ = stack[5].m_obj;
lean_object* v_a_1584_ = stack[6].m_obj;
lean_object* v_res_1594_;
v_res_1594_ = l_Lean_Compiler_LCNF_Probe_filterByLet(v_pu_1578_, v_f_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
stack->m_obj
 = v_res_1594_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByLet___boxed(lean_object* v_pu_1595_, lean_object* v_f_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
uint8_t v_pu_boxed_1603_; lean_object* v_res_1604_; 
v_pu_boxed_1603_ = lean_unbox(v_pu_1595_);
v_res_1604_ = l_Lean_Compiler_LCNF_Probe_filterByLet(v_pu_boxed_1603_, v_f_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec_ref(v_a_1597_);
return v_res_1604_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(uint8_t v_pu_1605_, lean_object* v_f_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_){
_start:
{
switch(lean_obj_tag(v_a_1607_))
{
case 0:
{
lean_object* v_k_1613_; 
v_k_1613_ = lean_ctor_get(v_a_1607_, 1);
lean_inc_ref(v_k_1613_);
lean_dec_ref_known(v_a_1607_, 2);
v_a_1607_ = v_k_1613_;
goto _start;
}
case 1:
{
lean_object* v_decl_1615_; lean_object* v_k_1616_; lean_object* v___x_1617_; 
v_decl_1615_ = lean_ctor_get(v_a_1607_, 0);
lean_inc_ref_n(v_decl_1615_, 2);
v_k_1616_ = lean_ctor_get(v_a_1607_, 1);
lean_inc_ref(v_k_1616_);
lean_dec_ref_known(v_a_1607_, 2);
lean_inc_ref(v_f_1606_);
lean_inc(v_a_1611_);
lean_inc_ref(v_a_1610_);
lean_inc(v_a_1609_);
lean_inc_ref(v_a_1608_);
v___x_1617_ = lean_apply_6(v_f_1606_, v_decl_1615_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, lean_box(0));
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; uint8_t v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
v___x_1619_ = lean_unbox(v_a_1618_);
lean_dec(v_a_1618_);
if (v___x_1619_ == 0)
{
lean_object* v_value_1620_; lean_object* v___x_1621_; 
lean_dec_ref_known(v___x_1617_, 1);
v_value_1620_ = lean_ctor_get(v_decl_1615_, 4);
lean_inc_ref(v_value_1620_);
lean_dec_ref(v_decl_1615_);
lean_inc_ref(v_f_1606_);
v___x_1621_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1605_, v_f_1606_, v_value_1620_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; uint8_t v___x_1623_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v___x_1623_ = lean_unbox(v_a_1622_);
if (v___x_1623_ == 0)
{
lean_dec_ref_known(v___x_1621_, 1);
v_a_1607_ = v_k_1616_;
goto _start;
}
else
{
lean_dec_ref(v_k_1616_);
lean_dec_ref(v_f_1606_);
return v___x_1621_;
}
}
else
{
lean_dec_ref(v_k_1616_);
lean_dec_ref(v_f_1606_);
return v___x_1621_;
}
}
else
{
lean_dec_ref(v_k_1616_);
lean_dec_ref(v_decl_1615_);
lean_dec_ref(v_f_1606_);
return v___x_1617_;
}
}
else
{
lean_dec_ref(v_k_1616_);
lean_dec_ref(v_decl_1615_);
lean_dec_ref(v_f_1606_);
return v___x_1617_;
}
}
case 2:
{
lean_object* v_k_1625_; 
v_k_1625_ = lean_ctor_get(v_a_1607_, 1);
lean_inc_ref(v_k_1625_);
lean_dec_ref_known(v_a_1607_, 2);
v_a_1607_ = v_k_1625_;
goto _start;
}
case 4:
{
lean_object* v_cases_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1646_; 
v_cases_1627_ = lean_ctor_get(v_a_1607_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_a_1607_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1629_ = v_a_1607_;
v_isShared_1630_ = v_isSharedCheck_1646_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_cases_1627_);
lean_dec(v_a_1607_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1646_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v_alts_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v_alts_1631_ = lean_ctor_get(v_cases_1627_, 3);
lean_inc_ref(v_alts_1631_);
lean_dec_ref(v_cases_1627_);
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = lean_array_get_size(v_alts_1631_);
v___x_1634_ = lean_nat_dec_lt(v___x_1632_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_dec_ref(v_alts_1631_);
lean_dec_ref(v_f_1606_);
v___x_1635_ = lean_box(v___x_1634_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1635_);
v___x_1637_ = v___x_1629_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
else
{
if (v___x_1634_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec_ref(v_alts_1631_);
lean_dec_ref(v_f_1606_);
v___x_1639_ = lean_box(v___x_1634_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1639_);
v___x_1641_ = v___x_1629_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
size_t v___x_1643_; size_t v___x_1644_; lean_object* v___x_1645_; 
lean_del_object(v___x_1629_);
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = lean_usize_of_nat(v___x_1633_);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_1605_, v_f_1606_, v_alts_1631_, v___x_1643_, v___x_1644_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
lean_dec_ref(v_alts_1631_);
return v___x_1645_;
}
}
}
}
case 7:
{
lean_object* v_k_1647_; 
v_k_1647_ = lean_ctor_get(v_a_1607_, 3);
lean_inc_ref(v_k_1647_);
lean_dec_ref_known(v_a_1607_, 4);
v_a_1607_ = v_k_1647_;
goto _start;
}
case 8:
{
lean_object* v_k_1649_; 
v_k_1649_ = lean_ctor_get(v_a_1607_, 3);
lean_inc_ref(v_k_1649_);
lean_dec_ref_known(v_a_1607_, 4);
v_a_1607_ = v_k_1649_;
goto _start;
}
case 9:
{
lean_object* v_k_1651_; 
v_k_1651_ = lean_ctor_get(v_a_1607_, 5);
lean_inc_ref(v_k_1651_);
lean_dec_ref_known(v_a_1607_, 6);
v_a_1607_ = v_k_1651_;
goto _start;
}
case 10:
{
lean_object* v_k_1653_; 
v_k_1653_ = lean_ctor_get(v_a_1607_, 2);
lean_inc_ref(v_k_1653_);
lean_dec_ref_known(v_a_1607_, 3);
v_a_1607_ = v_k_1653_;
goto _start;
}
case 11:
{
lean_object* v_k_1655_; 
v_k_1655_ = lean_ctor_get(v_a_1607_, 2);
lean_inc_ref(v_k_1655_);
lean_dec_ref_known(v_a_1607_, 3);
v_a_1607_ = v_k_1655_;
goto _start;
}
case 12:
{
lean_object* v_k_1657_; 
v_k_1657_ = lean_ctor_get(v_a_1607_, 3);
lean_inc_ref(v_k_1657_);
lean_dec_ref_known(v_a_1607_, 4);
v_a_1607_ = v_k_1657_;
goto _start;
}
case 13:
{
lean_object* v_k_1659_; 
v_k_1659_ = lean_ctor_get(v_a_1607_, 1);
lean_inc_ref(v_k_1659_);
lean_dec_ref_known(v_a_1607_, 2);
v_a_1607_ = v_k_1659_;
goto _start;
}
default: 
{
uint8_t v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec_ref(v_a_1607_);
lean_dec_ref(v_f_1606_);
v___x_1661_ = 0;
v___x_1662_ = lean_box(v___x_1661_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1605_ = stack[0].m_num;
lean_object* v_f_1606_ = stack[1].m_obj;
lean_object* v_a_1607_ = stack[2].m_obj;
lean_object* v_a_1608_ = stack[3].m_obj;
lean_object* v_a_1609_ = stack[4].m_obj;
lean_object* v_a_1610_ = stack[5].m_obj;
lean_object* v_a_1611_ = stack[6].m_obj;
lean_object* v_res_1664_;
v_res_1664_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1605_, v_f_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
stack->m_obj
 = v_res_1664_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(uint8_t v_pu_1665_, lean_object* v_f_1666_, lean_object* v_as_1667_, size_t v_i_1668_, size_t v_stop_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_usize_dec_eq(v_i_1668_, v_stop_1669_);
if (v___x_1675_ == 0)
{
uint8_t v___x_1676_; lean_object* v___y_1678_; lean_object* v___x_1693_; 
v___x_1676_ = 1;
v___x_1693_ = lean_array_uget_borrowed(v_as_1667_, v_i_1668_);
switch(lean_obj_tag(v___x_1693_))
{
case 0:
{
lean_object* v_code_1694_; 
v_code_1694_ = lean_ctor_get(v___x_1693_, 2);
lean_inc_ref(v_code_1694_);
v___y_1678_ = v_code_1694_;
goto v___jp_1677_;
}
case 1:
{
lean_object* v_code_1695_; 
v_code_1695_ = lean_ctor_get(v___x_1693_, 1);
lean_inc_ref(v_code_1695_);
v___y_1678_ = v_code_1695_;
goto v___jp_1677_;
}
default: 
{
lean_object* v_code_1696_; 
v_code_1696_ = lean_ctor_get(v___x_1693_, 0);
lean_inc_ref(v_code_1696_);
v___y_1678_ = v_code_1696_;
goto v___jp_1677_;
}
}
v___jp_1677_:
{
lean_object* v___x_1679_; 
lean_inc_ref(v_f_1666_);
v___x_1679_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_1665_, v_f_1666_, v___y_1678_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1692_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1692_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1692_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_unbox(v_a_1680_);
lean_dec(v_a_1680_);
if (v___x_1684_ == 0)
{
size_t v___x_1685_; size_t v___x_1686_; 
lean_del_object(v___x_1682_);
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1668_, v___x_1685_);
v_i_1668_ = v___x_1686_;
goto _start;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
lean_dec_ref(v_f_1666_);
v___x_1688_ = lean_box(v___x_1676_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1688_);
v___x_1690_ = v___x_1682_;
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
lean_dec_ref(v_f_1666_);
return v___x_1679_;
}
}
}
else
{
uint8_t v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec_ref(v_f_1666_);
v___x_1697_ = 0;
v___x_1698_ = lean_box(v___x_1697_);
v___x_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
return v___x_1699_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1665_ = stack[0].m_num;
lean_object* v_f_1666_ = stack[1].m_obj;
lean_object* v_as_1667_ = stack[2].m_obj;
size_t v_i_1668_ = stack[3].m_num;
size_t v_stop_1669_ = stack[4].m_num;
lean_object* v___y_1670_ = stack[5].m_obj;
lean_object* v___y_1671_ = stack[6].m_obj;
lean_object* v___y_1672_ = stack[7].m_obj;
lean_object* v___y_1673_ = stack[8].m_obj;
lean_object* v_res_1700_;
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_1665_, v_f_1666_, v_as_1667_, v_i_1668_, v_stop_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
stack->m_obj
 = v_res_1700_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0___boxed(lean_object* v_pu_1701_, lean_object* v_f_1702_, lean_object* v_as_1703_, lean_object* v_i_1704_, lean_object* v_stop_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
uint8_t v_pu_boxed_1711_; size_t v_i_boxed_1712_; size_t v_stop_boxed_1713_; lean_object* v_res_1714_; 
v_pu_boxed_1711_ = lean_unbox(v_pu_1701_);
v_i_boxed_1712_ = lean_unbox_usize(v_i_1704_);
lean_dec(v_i_1704_);
v_stop_boxed_1713_ = lean_unbox_usize(v_stop_1705_);
lean_dec(v_stop_1705_);
v_res_1714_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go_spec__0(v_pu_boxed_1711_, v_f_1702_, v_as_1703_, v_i_boxed_1712_, v_stop_boxed_1713_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec_ref(v_as_1703_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed(lean_object* v_pu_1715_, lean_object* v_f_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
uint8_t v_pu_boxed_1723_; lean_object* v_res_1724_; 
v_pu_boxed_1723_ = lean_unbox(v_pu_1715_);
v_res_1724_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go(v_pu_boxed_1723_, v_f_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
return v_res_1724_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(uint8_t v_pu_1725_, lean_object* v_f_1726_, lean_object* v_as_1727_, size_t v_i_1728_, size_t v_stop_1729_, lean_object* v_b_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_a_1737_; uint8_t v___x_1741_; 
v___x_1741_ = lean_usize_dec_eq(v_i_1728_, v_stop_1729_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v_value_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1742_ = lean_array_uget_borrowed(v_as_1727_, v_i_1728_);
v_value_1743_ = lean_ctor_get(v___x_1742_, 1);
v___x_1744_ = lean_box(v_pu_1725_);
lean_inc_ref(v_f_1726_);
v___x_1745_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFun_go___boxed), 8, 2);
lean_closure_set(v___x_1745_, 0, v___x_1744_);
lean_closure_set(v___x_1745_, 1, v_f_1726_);
lean_inc_ref(v_value_1743_);
v___x_1746_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1743_, v___x_1745_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; uint8_t v___x_1748_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = lean_unbox(v_a_1747_);
lean_dec(v_a_1747_);
if (v___x_1748_ == 0)
{
v_a_1737_ = v_b_1730_;
goto v___jp_1736_;
}
else
{
lean_object* v___x_1749_; 
lean_inc(v___x_1742_);
v___x_1749_ = lean_array_push(v_b_1730_, v___x_1742_);
v_a_1737_ = v___x_1749_;
goto v___jp_1736_;
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec_ref(v_b_1730_);
lean_dec_ref(v_f_1726_);
v_a_1750_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1746_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1746_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v___x_1758_; 
lean_dec_ref(v_f_1726_);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v_b_1730_);
return v___x_1758_;
}
v___jp_1736_:
{
size_t v___x_1738_; size_t v___x_1739_; 
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_add(v_i_1728_, v___x_1738_);
v_i_1728_ = v___x_1739_;
v_b_1730_ = v_a_1737_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1725_ = stack[0].m_num;
lean_object* v_f_1726_ = stack[1].m_obj;
lean_object* v_as_1727_ = stack[2].m_obj;
size_t v_i_1728_ = stack[3].m_num;
size_t v_stop_1729_ = stack[4].m_num;
lean_object* v_b_1730_ = stack[5].m_obj;
lean_object* v___y_1731_ = stack[6].m_obj;
lean_object* v___y_1732_ = stack[7].m_obj;
lean_object* v___y_1733_ = stack[8].m_obj;
lean_object* v___y_1734_ = stack[9].m_obj;
lean_object* v_res_1759_;
v_res_1759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1725_, v_f_1726_, v_as_1727_, v_i_1728_, v_stop_1729_, v_b_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
stack->m_obj
 = v_res_1759_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0___boxed(lean_object* v_pu_1760_, lean_object* v_f_1761_, lean_object* v_as_1762_, lean_object* v_i_1763_, lean_object* v_stop_1764_, lean_object* v_b_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
uint8_t v_pu_boxed_1771_; size_t v_i_boxed_1772_; size_t v_stop_boxed_1773_; lean_object* v_res_1774_; 
v_pu_boxed_1771_ = lean_unbox(v_pu_1760_);
v_i_boxed_1772_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_stop_boxed_1773_ = lean_unbox_usize(v_stop_1764_);
lean_dec(v_stop_1764_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_boxed_1771_, v_f_1761_, v_as_1762_, v_i_boxed_1772_, v_stop_boxed_1773_, v_b_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec_ref(v_as_1762_);
return v_res_1774_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun(uint8_t v_pu_1775_, lean_object* v_f_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1783_ = lean_unsigned_to_nat(0u);
v___x_1784_ = lean_array_get_size(v_a_1777_);
v___x_1785_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1786_ = lean_nat_dec_lt(v___x_1783_, v___x_1784_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; 
lean_dec_ref(v_f_1776_);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
return v___x_1787_;
}
else
{
size_t v___x_1788_; size_t v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = ((size_t)0ULL);
v___x_1789_ = lean_usize_of_nat(v___x_1784_);
v___x_1790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFun_spec__0(v_pu_1775_, v_f_1776_, v_a_1777_, v___x_1788_, v___x_1789_, v___x_1785_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
return v___x_1790_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filterByFun_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1775_ = stack[0].m_num;
lean_object* v_f_1776_ = stack[1].m_obj;
lean_object* v_a_1777_ = stack[2].m_obj;
lean_object* v_a_1778_ = stack[3].m_obj;
lean_object* v_a_1779_ = stack[4].m_obj;
lean_object* v_a_1780_ = stack[5].m_obj;
lean_object* v_a_1781_ = stack[6].m_obj;
lean_object* v_res_1791_;
v_res_1791_ = l_Lean_Compiler_LCNF_Probe_filterByFun(v_pu_1775_, v_f_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
stack->m_obj
 = v_res_1791_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFun___boxed(lean_object* v_pu_1792_, lean_object* v_f_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
uint8_t v_pu_boxed_1800_; lean_object* v_res_1801_; 
v_pu_boxed_1800_ = lean_unbox(v_pu_1792_);
v_res_1801_ = l_Lean_Compiler_LCNF_Probe_filterByFun(v_pu_boxed_1800_, v_f_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec_ref(v_a_1795_);
lean_dec_ref(v_a_1794_);
return v_res_1801_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(uint8_t v_pu_1802_, lean_object* v_f_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
switch(lean_obj_tag(v_a_1804_))
{
case 0:
{
lean_object* v_k_1810_; 
v_k_1810_ = lean_ctor_get(v_a_1804_, 1);
lean_inc_ref(v_k_1810_);
lean_dec_ref_known(v_a_1804_, 2);
v_a_1804_ = v_k_1810_;
goto _start;
}
case 1:
{
lean_object* v_decl_1812_; lean_object* v_k_1813_; lean_object* v_value_1814_; lean_object* v___x_1815_; 
v_decl_1812_ = lean_ctor_get(v_a_1804_, 0);
lean_inc_ref(v_decl_1812_);
v_k_1813_ = lean_ctor_get(v_a_1804_, 1);
lean_inc_ref(v_k_1813_);
lean_dec_ref_known(v_a_1804_, 2);
v_value_1814_ = lean_ctor_get(v_decl_1812_, 4);
lean_inc_ref(v_value_1814_);
lean_dec_ref(v_decl_1812_);
lean_inc_ref(v_f_1803_);
v___x_1815_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1802_, v_f_1803_, v_value_1814_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; uint8_t v___x_1817_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v___x_1817_ = lean_unbox(v_a_1816_);
if (v___x_1817_ == 0)
{
lean_dec_ref_known(v___x_1815_, 1);
v_a_1804_ = v_k_1813_;
goto _start;
}
else
{
lean_dec_ref(v_k_1813_);
lean_dec_ref(v_f_1803_);
return v___x_1815_;
}
}
else
{
lean_dec_ref(v_k_1813_);
lean_dec_ref(v_f_1803_);
return v___x_1815_;
}
}
case 2:
{
lean_object* v_decl_1819_; lean_object* v_k_1820_; lean_object* v___x_1821_; 
v_decl_1819_ = lean_ctor_get(v_a_1804_, 0);
lean_inc_ref_n(v_decl_1819_, 2);
v_k_1820_ = lean_ctor_get(v_a_1804_, 1);
lean_inc_ref(v_k_1820_);
lean_dec_ref_known(v_a_1804_, 2);
lean_inc_ref(v_f_1803_);
lean_inc(v_a_1808_);
lean_inc_ref(v_a_1807_);
lean_inc(v_a_1806_);
lean_inc_ref(v_a_1805_);
v___x_1821_ = lean_apply_6(v_f_1803_, v_decl_1819_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, lean_box(0));
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; uint8_t v___x_1823_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
v___x_1823_ = lean_unbox(v_a_1822_);
lean_dec(v_a_1822_);
if (v___x_1823_ == 0)
{
lean_object* v_value_1824_; lean_object* v___x_1825_; 
lean_dec_ref_known(v___x_1821_, 1);
v_value_1824_ = lean_ctor_get(v_decl_1819_, 4);
lean_inc_ref(v_value_1824_);
lean_dec_ref(v_decl_1819_);
lean_inc_ref(v_f_1803_);
v___x_1825_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1802_, v_f_1803_, v_value_1824_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; uint8_t v___x_1827_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v___x_1827_ = lean_unbox(v_a_1826_);
if (v___x_1827_ == 0)
{
lean_dec_ref_known(v___x_1825_, 1);
v_a_1804_ = v_k_1820_;
goto _start;
}
else
{
lean_dec_ref(v_k_1820_);
lean_dec_ref(v_f_1803_);
return v___x_1825_;
}
}
else
{
lean_dec_ref(v_k_1820_);
lean_dec_ref(v_f_1803_);
return v___x_1825_;
}
}
else
{
lean_dec_ref(v_k_1820_);
lean_dec_ref(v_decl_1819_);
lean_dec_ref(v_f_1803_);
return v___x_1821_;
}
}
else
{
lean_dec_ref(v_k_1820_);
lean_dec_ref(v_decl_1819_);
lean_dec_ref(v_f_1803_);
return v___x_1821_;
}
}
case 4:
{
lean_object* v_cases_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1848_; 
v_cases_1829_ = lean_ctor_get(v_a_1804_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_a_1804_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1831_ = v_a_1804_;
v_isShared_1832_ = v_isSharedCheck_1848_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_cases_1829_);
lean_dec(v_a_1804_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1848_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_alts_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v_alts_1833_ = lean_ctor_get(v_cases_1829_, 3);
lean_inc_ref(v_alts_1833_);
lean_dec_ref(v_cases_1829_);
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = lean_array_get_size(v_alts_1833_);
v___x_1836_ = lean_nat_dec_lt(v___x_1834_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec_ref(v_alts_1833_);
lean_dec_ref(v_f_1803_);
v___x_1837_ = lean_box(v___x_1836_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set_tag(v___x_1831_, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1837_);
v___x_1839_ = v___x_1831_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
if (v___x_1836_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
lean_dec_ref(v_alts_1833_);
lean_dec_ref(v_f_1803_);
v___x_1841_ = lean_box(v___x_1836_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set_tag(v___x_1831_, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1841_);
v___x_1843_ = v___x_1831_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
else
{
size_t v___x_1845_; size_t v___x_1846_; lean_object* v___x_1847_; 
lean_del_object(v___x_1831_);
v___x_1845_ = ((size_t)0ULL);
v___x_1846_ = lean_usize_of_nat(v___x_1835_);
v___x_1847_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_1802_, v_f_1803_, v_alts_1833_, v___x_1845_, v___x_1846_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec_ref(v_alts_1833_);
return v___x_1847_;
}
}
}
}
case 7:
{
lean_object* v_k_1849_; 
v_k_1849_ = lean_ctor_get(v_a_1804_, 3);
lean_inc_ref(v_k_1849_);
lean_dec_ref_known(v_a_1804_, 4);
v_a_1804_ = v_k_1849_;
goto _start;
}
case 8:
{
lean_object* v_k_1851_; 
v_k_1851_ = lean_ctor_get(v_a_1804_, 3);
lean_inc_ref(v_k_1851_);
lean_dec_ref_known(v_a_1804_, 4);
v_a_1804_ = v_k_1851_;
goto _start;
}
case 9:
{
lean_object* v_k_1853_; 
v_k_1853_ = lean_ctor_get(v_a_1804_, 5);
lean_inc_ref(v_k_1853_);
lean_dec_ref_known(v_a_1804_, 6);
v_a_1804_ = v_k_1853_;
goto _start;
}
case 10:
{
lean_object* v_k_1855_; 
v_k_1855_ = lean_ctor_get(v_a_1804_, 2);
lean_inc_ref(v_k_1855_);
lean_dec_ref_known(v_a_1804_, 3);
v_a_1804_ = v_k_1855_;
goto _start;
}
case 11:
{
lean_object* v_k_1857_; 
v_k_1857_ = lean_ctor_get(v_a_1804_, 2);
lean_inc_ref(v_k_1857_);
lean_dec_ref_known(v_a_1804_, 3);
v_a_1804_ = v_k_1857_;
goto _start;
}
case 12:
{
lean_object* v_k_1859_; 
v_k_1859_ = lean_ctor_get(v_a_1804_, 3);
lean_inc_ref(v_k_1859_);
lean_dec_ref_known(v_a_1804_, 4);
v_a_1804_ = v_k_1859_;
goto _start;
}
case 13:
{
lean_object* v_k_1861_; 
v_k_1861_ = lean_ctor_get(v_a_1804_, 1);
lean_inc_ref(v_k_1861_);
lean_dec_ref_known(v_a_1804_, 2);
v_a_1804_ = v_k_1861_;
goto _start;
}
default: 
{
uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
lean_dec_ref(v_a_1804_);
lean_dec_ref(v_f_1803_);
v___x_1863_ = 0;
v___x_1864_ = lean_box(v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
return v___x_1865_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1802_ = stack[0].m_num;
lean_object* v_f_1803_ = stack[1].m_obj;
lean_object* v_a_1804_ = stack[2].m_obj;
lean_object* v_a_1805_ = stack[3].m_obj;
lean_object* v_a_1806_ = stack[4].m_obj;
lean_object* v_a_1807_ = stack[5].m_obj;
lean_object* v_a_1808_ = stack[6].m_obj;
lean_object* v_res_1866_;
v_res_1866_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1802_, v_f_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
stack->m_obj
 = v_res_1866_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(uint8_t v_pu_1867_, lean_object* v_f_1868_, lean_object* v_as_1869_, size_t v_i_1870_, size_t v_stop_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
uint8_t v___x_1877_; 
v___x_1877_ = lean_usize_dec_eq(v_i_1870_, v_stop_1871_);
if (v___x_1877_ == 0)
{
uint8_t v___x_1878_; lean_object* v___y_1880_; lean_object* v___x_1895_; 
v___x_1878_ = 1;
v___x_1895_ = lean_array_uget_borrowed(v_as_1869_, v_i_1870_);
switch(lean_obj_tag(v___x_1895_))
{
case 0:
{
lean_object* v_code_1896_; 
v_code_1896_ = lean_ctor_get(v___x_1895_, 2);
lean_inc_ref(v_code_1896_);
v___y_1880_ = v_code_1896_;
goto v___jp_1879_;
}
case 1:
{
lean_object* v_code_1897_; 
v_code_1897_ = lean_ctor_get(v___x_1895_, 1);
lean_inc_ref(v_code_1897_);
v___y_1880_ = v_code_1897_;
goto v___jp_1879_;
}
default: 
{
lean_object* v_code_1898_; 
v_code_1898_ = lean_ctor_get(v___x_1895_, 0);
lean_inc_ref(v_code_1898_);
v___y_1880_ = v_code_1898_;
goto v___jp_1879_;
}
}
v___jp_1879_:
{
lean_object* v___x_1881_; 
lean_inc_ref(v_f_1868_);
v___x_1881_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_1867_, v_f_1868_, v___y_1880_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1894_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1894_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1894_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_unbox(v_a_1882_);
lean_dec(v_a_1882_);
if (v___x_1886_ == 0)
{
size_t v___x_1887_; size_t v___x_1888_; 
lean_del_object(v___x_1884_);
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_add(v_i_1870_, v___x_1887_);
v_i_1870_ = v___x_1888_;
goto _start;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
lean_dec_ref(v_f_1868_);
v___x_1890_ = lean_box(v___x_1878_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1890_);
v___x_1892_ = v___x_1884_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
else
{
lean_dec_ref(v_f_1868_);
return v___x_1881_;
}
}
}
else
{
uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_dec_ref(v_f_1868_);
v___x_1899_ = 0;
v___x_1900_ = lean_box(v___x_1899_);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1867_ = stack[0].m_num;
lean_object* v_f_1868_ = stack[1].m_obj;
lean_object* v_as_1869_ = stack[2].m_obj;
size_t v_i_1870_ = stack[3].m_num;
size_t v_stop_1871_ = stack[4].m_num;
lean_object* v___y_1872_ = stack[5].m_obj;
lean_object* v___y_1873_ = stack[6].m_obj;
lean_object* v___y_1874_ = stack[7].m_obj;
lean_object* v___y_1875_ = stack[8].m_obj;
lean_object* v_res_1902_;
v_res_1902_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_1867_, v_f_1868_, v_as_1869_, v_i_1870_, v_stop_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
stack->m_obj
 = v_res_1902_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0___boxed(lean_object* v_pu_1903_, lean_object* v_f_1904_, lean_object* v_as_1905_, lean_object* v_i_1906_, lean_object* v_stop_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
uint8_t v_pu_boxed_1913_; size_t v_i_boxed_1914_; size_t v_stop_boxed_1915_; lean_object* v_res_1916_; 
v_pu_boxed_1913_ = lean_unbox(v_pu_1903_);
v_i_boxed_1914_ = lean_unbox_usize(v_i_1906_);
lean_dec(v_i_1906_);
v_stop_boxed_1915_ = lean_unbox_usize(v_stop_1907_);
lean_dec(v_stop_1907_);
v_res_1916_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go_spec__0(v_pu_boxed_1913_, v_f_1904_, v_as_1905_, v_i_boxed_1914_, v_stop_boxed_1915_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec_ref(v_as_1905_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed(lean_object* v_pu_1917_, lean_object* v_f_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
uint8_t v_pu_boxed_1925_; lean_object* v_res_1926_; 
v_pu_boxed_1925_ = lean_unbox(v_pu_1917_);
v_res_1926_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go(v_pu_boxed_1925_, v_f_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
return v_res_1926_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(uint8_t v_pu_1927_, lean_object* v_f_1928_, lean_object* v_as_1929_, size_t v_i_1930_, size_t v_stop_1931_, lean_object* v_b_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_a_1939_; uint8_t v___x_1943_; 
v___x_1943_ = lean_usize_dec_eq(v_i_1930_, v_stop_1931_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v_value_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1944_ = lean_array_uget_borrowed(v_as_1929_, v_i_1930_);
v_value_1945_ = lean_ctor_get(v___x_1944_, 1);
v___x_1946_ = lean_box(v_pu_1927_);
lean_inc_ref(v_f_1928_);
v___x_1947_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJp_go___boxed), 8, 2);
lean_closure_set(v___x_1947_, 0, v___x_1946_);
lean_closure_set(v___x_1947_, 1, v_f_1928_);
lean_inc_ref(v_value_1945_);
v___x_1948_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_1945_, v___x_1947_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; uint8_t v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
v___x_1950_ = lean_unbox(v_a_1949_);
lean_dec(v_a_1949_);
if (v___x_1950_ == 0)
{
v_a_1939_ = v_b_1932_;
goto v___jp_1938_;
}
else
{
lean_object* v___x_1951_; 
lean_inc(v___x_1944_);
v___x_1951_ = lean_array_push(v_b_1932_, v___x_1944_);
v_a_1939_ = v___x_1951_;
goto v___jp_1938_;
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_b_1932_);
lean_dec_ref(v_f_1928_);
v_a_1952_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1948_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1948_);
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
else
{
lean_object* v___x_1960_; 
lean_dec_ref(v_f_1928_);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v_b_1932_);
return v___x_1960_;
}
v___jp_1938_:
{
size_t v___x_1940_; size_t v___x_1941_; 
v___x_1940_ = ((size_t)1ULL);
v___x_1941_ = lean_usize_add(v_i_1930_, v___x_1940_);
v_i_1930_ = v___x_1941_;
v_b_1932_ = v_a_1939_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1927_ = stack[0].m_num;
lean_object* v_f_1928_ = stack[1].m_obj;
lean_object* v_as_1929_ = stack[2].m_obj;
size_t v_i_1930_ = stack[3].m_num;
size_t v_stop_1931_ = stack[4].m_num;
lean_object* v_b_1932_ = stack[5].m_obj;
lean_object* v___y_1933_ = stack[6].m_obj;
lean_object* v___y_1934_ = stack[7].m_obj;
lean_object* v___y_1935_ = stack[8].m_obj;
lean_object* v___y_1936_ = stack[9].m_obj;
lean_object* v_res_1961_;
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_1927_, v_f_1928_, v_as_1929_, v_i_1930_, v_stop_1931_, v_b_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
stack->m_obj
 = v_res_1961_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0___boxed(lean_object* v_pu_1962_, lean_object* v_f_1963_, lean_object* v_as_1964_, lean_object* v_i_1965_, lean_object* v_stop_1966_, lean_object* v_b_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
uint8_t v_pu_boxed_1973_; size_t v_i_boxed_1974_; size_t v_stop_boxed_1975_; lean_object* v_res_1976_; 
v_pu_boxed_1973_ = lean_unbox(v_pu_1962_);
v_i_boxed_1974_ = lean_unbox_usize(v_i_1965_);
lean_dec(v_i_1965_);
v_stop_boxed_1975_ = lean_unbox_usize(v_stop_1966_);
lean_dec(v_stop_1966_);
v_res_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_boxed_1973_, v_f_1963_, v_as_1964_, v_i_boxed_1974_, v_stop_boxed_1975_, v_b_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec_ref(v_as_1964_);
return v_res_1976_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp(uint8_t v_pu_1977_, lean_object* v_f_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1985_ = lean_unsigned_to_nat(0u);
v___x_1986_ = lean_array_get_size(v_a_1979_);
v___x_1987_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_1988_ = lean_nat_dec_lt(v___x_1985_, v___x_1986_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_dec_ref(v_f_1978_);
v___x_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
return v___x_1989_;
}
else
{
size_t v___x_1990_; size_t v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = ((size_t)0ULL);
v___x_1991_ = lean_usize_of_nat(v___x_1986_);
v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJp_spec__0(v_pu_1977_, v_f_1978_, v_a_1979_, v___x_1990_, v___x_1991_, v___x_1987_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
return v___x_1992_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filterByJp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1977_ = stack[0].m_num;
lean_object* v_f_1978_ = stack[1].m_obj;
lean_object* v_a_1979_ = stack[2].m_obj;
lean_object* v_a_1980_ = stack[3].m_obj;
lean_object* v_a_1981_ = stack[4].m_obj;
lean_object* v_a_1982_ = stack[5].m_obj;
lean_object* v_a_1983_ = stack[6].m_obj;
lean_object* v_res_1993_;
v_res_1993_ = l_Lean_Compiler_LCNF_Probe_filterByJp(v_pu_1977_, v_f_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
stack->m_obj
 = v_res_1993_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJp___boxed(lean_object* v_pu_1994_, lean_object* v_f_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
uint8_t v_pu_boxed_2002_; lean_object* v_res_2003_; 
v_pu_boxed_2002_ = lean_unbox(v_pu_1994_);
v_res_2003_ = l_Lean_Compiler_LCNF_Probe_filterByJp(v_pu_boxed_2002_, v_f_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec_ref(v_a_1996_);
return v_res_2003_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(uint8_t v_pu_2004_, lean_object* v_f_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
switch(lean_obj_tag(v_a_2006_))
{
case 0:
{
lean_object* v_k_2012_; 
v_k_2012_ = lean_ctor_get(v_a_2006_, 1);
lean_inc_ref(v_k_2012_);
lean_dec_ref_known(v_a_2006_, 2);
v_a_2006_ = v_k_2012_;
goto _start;
}
case 1:
{
lean_object* v_decl_2014_; lean_object* v_k_2015_; lean_object* v___x_2016_; 
v_decl_2014_ = lean_ctor_get(v_a_2006_, 0);
lean_inc_ref_n(v_decl_2014_, 2);
v_k_2015_ = lean_ctor_get(v_a_2006_, 1);
lean_inc_ref(v_k_2015_);
lean_dec_ref_known(v_a_2006_, 2);
lean_inc_ref(v_f_2005_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
v___x_2016_ = lean_apply_6(v_f_2005_, v_decl_2014_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, lean_box(0));
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; uint8_t v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
v___x_2018_ = lean_unbox(v_a_2017_);
lean_dec(v_a_2017_);
if (v___x_2018_ == 0)
{
lean_object* v_value_2019_; lean_object* v___x_2020_; 
lean_dec_ref_known(v___x_2016_, 1);
v_value_2019_ = lean_ctor_get(v_decl_2014_, 4);
lean_inc_ref(v_value_2019_);
lean_dec_ref(v_decl_2014_);
lean_inc_ref(v_f_2005_);
v___x_2020_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2004_, v_f_2005_, v_value_2019_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; uint8_t v___x_2022_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v___x_2022_ = lean_unbox(v_a_2021_);
if (v___x_2022_ == 0)
{
lean_dec_ref_known(v___x_2020_, 1);
v_a_2006_ = v_k_2015_;
goto _start;
}
else
{
lean_dec_ref(v_k_2015_);
lean_dec_ref(v_f_2005_);
return v___x_2020_;
}
}
else
{
lean_dec_ref(v_k_2015_);
lean_dec_ref(v_f_2005_);
return v___x_2020_;
}
}
else
{
lean_dec_ref(v_k_2015_);
lean_dec_ref(v_decl_2014_);
lean_dec_ref(v_f_2005_);
return v___x_2016_;
}
}
else
{
lean_dec_ref(v_k_2015_);
lean_dec_ref(v_decl_2014_);
lean_dec_ref(v_f_2005_);
return v___x_2016_;
}
}
case 2:
{
lean_object* v_decl_2024_; lean_object* v_k_2025_; lean_object* v___x_2026_; 
v_decl_2024_ = lean_ctor_get(v_a_2006_, 0);
lean_inc_ref_n(v_decl_2024_, 2);
v_k_2025_ = lean_ctor_get(v_a_2006_, 1);
lean_inc_ref(v_k_2025_);
lean_dec_ref_known(v_a_2006_, 2);
lean_inc_ref(v_f_2005_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
v___x_2026_ = lean_apply_6(v_f_2005_, v_decl_2024_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, lean_box(0));
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; uint8_t v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
v___x_2028_ = lean_unbox(v_a_2027_);
lean_dec(v_a_2027_);
if (v___x_2028_ == 0)
{
lean_object* v_value_2029_; lean_object* v___x_2030_; 
lean_dec_ref_known(v___x_2026_, 1);
v_value_2029_ = lean_ctor_get(v_decl_2024_, 4);
lean_inc_ref(v_value_2029_);
lean_dec_ref(v_decl_2024_);
lean_inc_ref(v_f_2005_);
v___x_2030_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2004_, v_f_2005_, v_value_2029_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; uint8_t v___x_2032_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v___x_2032_ = lean_unbox(v_a_2031_);
if (v___x_2032_ == 0)
{
lean_dec_ref_known(v___x_2030_, 1);
v_a_2006_ = v_k_2025_;
goto _start;
}
else
{
lean_dec_ref(v_k_2025_);
lean_dec_ref(v_f_2005_);
return v___x_2030_;
}
}
else
{
lean_dec_ref(v_k_2025_);
lean_dec_ref(v_f_2005_);
return v___x_2030_;
}
}
else
{
lean_dec_ref(v_k_2025_);
lean_dec_ref(v_decl_2024_);
lean_dec_ref(v_f_2005_);
return v___x_2026_;
}
}
else
{
lean_dec_ref(v_k_2025_);
lean_dec_ref(v_decl_2024_);
lean_dec_ref(v_f_2005_);
return v___x_2026_;
}
}
case 4:
{
lean_object* v_cases_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2053_; 
v_cases_2034_ = lean_ctor_get(v_a_2006_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_2006_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2036_ = v_a_2006_;
v_isShared_2037_ = v_isSharedCheck_2053_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_cases_2034_);
lean_dec(v_a_2006_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2053_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v_alts_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v_alts_2038_ = lean_ctor_get(v_cases_2034_, 3);
lean_inc_ref(v_alts_2038_);
lean_dec_ref(v_cases_2034_);
v___x_2039_ = lean_unsigned_to_nat(0u);
v___x_2040_ = lean_array_get_size(v_alts_2038_);
v___x_2041_ = lean_nat_dec_lt(v___x_2039_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
lean_dec_ref(v_alts_2038_);
lean_dec_ref(v_f_2005_);
v___x_2042_ = lean_box(v___x_2041_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2042_);
v___x_2044_ = v___x_2036_;
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
else
{
if (v___x_2041_ == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_dec_ref(v_alts_2038_);
lean_dec_ref(v_f_2005_);
v___x_2046_ = lean_box(v___x_2041_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2046_);
v___x_2048_ = v___x_2036_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
else
{
size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
lean_del_object(v___x_2036_);
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = lean_usize_of_nat(v___x_2040_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_2004_, v_f_2005_, v_alts_2038_, v___x_2050_, v___x_2051_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
lean_dec_ref(v_alts_2038_);
return v___x_2052_;
}
}
}
}
case 7:
{
lean_object* v_k_2054_; 
v_k_2054_ = lean_ctor_get(v_a_2006_, 3);
lean_inc_ref(v_k_2054_);
lean_dec_ref_known(v_a_2006_, 4);
v_a_2006_ = v_k_2054_;
goto _start;
}
case 8:
{
lean_object* v_k_2056_; 
v_k_2056_ = lean_ctor_get(v_a_2006_, 3);
lean_inc_ref(v_k_2056_);
lean_dec_ref_known(v_a_2006_, 4);
v_a_2006_ = v_k_2056_;
goto _start;
}
case 9:
{
lean_object* v_k_2058_; 
v_k_2058_ = lean_ctor_get(v_a_2006_, 5);
lean_inc_ref(v_k_2058_);
lean_dec_ref_known(v_a_2006_, 6);
v_a_2006_ = v_k_2058_;
goto _start;
}
case 10:
{
lean_object* v_k_2060_; 
v_k_2060_ = lean_ctor_get(v_a_2006_, 2);
lean_inc_ref(v_k_2060_);
lean_dec_ref_known(v_a_2006_, 3);
v_a_2006_ = v_k_2060_;
goto _start;
}
case 11:
{
lean_object* v_k_2062_; 
v_k_2062_ = lean_ctor_get(v_a_2006_, 2);
lean_inc_ref(v_k_2062_);
lean_dec_ref_known(v_a_2006_, 3);
v_a_2006_ = v_k_2062_;
goto _start;
}
case 12:
{
lean_object* v_k_2064_; 
v_k_2064_ = lean_ctor_get(v_a_2006_, 3);
lean_inc_ref(v_k_2064_);
lean_dec_ref_known(v_a_2006_, 4);
v_a_2006_ = v_k_2064_;
goto _start;
}
case 13:
{
lean_object* v_k_2066_; 
v_k_2066_ = lean_ctor_get(v_a_2006_, 1);
lean_inc_ref(v_k_2066_);
lean_dec_ref_known(v_a_2006_, 2);
v_a_2006_ = v_k_2066_;
goto _start;
}
default: 
{
uint8_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_f_2005_);
v___x_2068_ = 0;
v___x_2069_ = lean_box(v___x_2068_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2004_ = stack[0].m_num;
lean_object* v_f_2005_ = stack[1].m_obj;
lean_object* v_a_2006_ = stack[2].m_obj;
lean_object* v_a_2007_ = stack[3].m_obj;
lean_object* v_a_2008_ = stack[4].m_obj;
lean_object* v_a_2009_ = stack[5].m_obj;
lean_object* v_a_2010_ = stack[6].m_obj;
lean_object* v_res_2071_;
v_res_2071_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2004_, v_f_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
stack->m_obj
 = v_res_2071_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(uint8_t v_pu_2072_, lean_object* v_f_2073_, lean_object* v_as_2074_, size_t v_i_2075_, size_t v_stop_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_usize_dec_eq(v_i_2075_, v_stop_2076_);
if (v___x_2082_ == 0)
{
uint8_t v___x_2083_; lean_object* v___y_2085_; lean_object* v___x_2100_; 
v___x_2083_ = 1;
v___x_2100_ = lean_array_uget_borrowed(v_as_2074_, v_i_2075_);
switch(lean_obj_tag(v___x_2100_))
{
case 0:
{
lean_object* v_code_2101_; 
v_code_2101_ = lean_ctor_get(v___x_2100_, 2);
lean_inc_ref(v_code_2101_);
v___y_2085_ = v_code_2101_;
goto v___jp_2084_;
}
case 1:
{
lean_object* v_code_2102_; 
v_code_2102_ = lean_ctor_get(v___x_2100_, 1);
lean_inc_ref(v_code_2102_);
v___y_2085_ = v_code_2102_;
goto v___jp_2084_;
}
default: 
{
lean_object* v_code_2103_; 
v_code_2103_ = lean_ctor_get(v___x_2100_, 0);
lean_inc_ref(v_code_2103_);
v___y_2085_ = v_code_2103_;
goto v___jp_2084_;
}
}
v___jp_2084_:
{
lean_object* v___x_2086_; 
lean_inc_ref(v_f_2073_);
v___x_2086_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_2072_, v_f_2073_, v___y_2085_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2099_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2099_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2099_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
uint8_t v___x_2091_; 
v___x_2091_ = lean_unbox(v_a_2087_);
lean_dec(v_a_2087_);
if (v___x_2091_ == 0)
{
size_t v___x_2092_; size_t v___x_2093_; 
lean_del_object(v___x_2089_);
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_add(v_i_2075_, v___x_2092_);
v_i_2075_ = v___x_2093_;
goto _start;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
lean_dec_ref(v_f_2073_);
v___x_2095_ = lean_box(v___x_2083_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2095_);
v___x_2097_ = v___x_2089_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_dec_ref(v_f_2073_);
return v___x_2086_;
}
}
}
else
{
uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
lean_dec_ref(v_f_2073_);
v___x_2104_ = 0;
v___x_2105_ = lean_box(v___x_2104_);
v___x_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
return v___x_2106_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2072_ = stack[0].m_num;
lean_object* v_f_2073_ = stack[1].m_obj;
lean_object* v_as_2074_ = stack[2].m_obj;
size_t v_i_2075_ = stack[3].m_num;
size_t v_stop_2076_ = stack[4].m_num;
lean_object* v___y_2077_ = stack[5].m_obj;
lean_object* v___y_2078_ = stack[6].m_obj;
lean_object* v___y_2079_ = stack[7].m_obj;
lean_object* v___y_2080_ = stack[8].m_obj;
lean_object* v_res_2107_;
v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_2072_, v_f_2073_, v_as_2074_, v_i_2075_, v_stop_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
stack->m_obj
 = v_res_2107_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0___boxed(lean_object* v_pu_2108_, lean_object* v_f_2109_, lean_object* v_as_2110_, lean_object* v_i_2111_, lean_object* v_stop_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
uint8_t v_pu_boxed_2118_; size_t v_i_boxed_2119_; size_t v_stop_boxed_2120_; lean_object* v_res_2121_; 
v_pu_boxed_2118_ = lean_unbox(v_pu_2108_);
v_i_boxed_2119_ = lean_unbox_usize(v_i_2111_);
lean_dec(v_i_2111_);
v_stop_boxed_2120_ = lean_unbox_usize(v_stop_2112_);
lean_dec(v_stop_2112_);
v_res_2121_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go_spec__0(v_pu_boxed_2118_, v_f_2109_, v_as_2110_, v_i_boxed_2119_, v_stop_boxed_2120_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec_ref(v_as_2110_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed(lean_object* v_pu_2122_, lean_object* v_f_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
uint8_t v_pu_boxed_2130_; lean_object* v_res_2131_; 
v_pu_boxed_2130_ = lean_unbox(v_pu_2122_);
v_res_2131_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go(v_pu_boxed_2130_, v_f_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
return v_res_2131_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(uint8_t v_pu_2132_, lean_object* v_f_2133_, lean_object* v_as_2134_, size_t v_i_2135_, size_t v_stop_2136_, lean_object* v_b_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_a_2144_; uint8_t v___x_2148_; 
v___x_2148_ = lean_usize_dec_eq(v_i_2135_, v_stop_2136_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v_value_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2149_ = lean_array_uget_borrowed(v_as_2134_, v_i_2135_);
v_value_2150_ = lean_ctor_get(v___x_2149_, 1);
v___x_2151_ = lean_box(v_pu_2132_);
lean_inc_ref(v_f_2133_);
v___x_2152_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByFunDecl_go___boxed), 8, 2);
lean_closure_set(v___x_2152_, 0, v___x_2151_);
lean_closure_set(v___x_2152_, 1, v_f_2133_);
lean_inc_ref(v_value_2150_);
v___x_2153_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2150_, v___x_2152_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; uint8_t v___x_2155_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = lean_unbox(v_a_2154_);
lean_dec(v_a_2154_);
if (v___x_2155_ == 0)
{
v_a_2144_ = v_b_2137_;
goto v___jp_2143_;
}
else
{
lean_object* v___x_2156_; 
lean_inc(v___x_2149_);
v___x_2156_ = lean_array_push(v_b_2137_, v___x_2149_);
v_a_2144_ = v___x_2156_;
goto v___jp_2143_;
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref(v_b_2137_);
lean_dec_ref(v_f_2133_);
v_a_2157_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2153_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2153_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v___x_2165_; 
lean_dec_ref(v_f_2133_);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_b_2137_);
return v___x_2165_;
}
v___jp_2143_:
{
size_t v___x_2145_; size_t v___x_2146_; 
v___x_2145_ = ((size_t)1ULL);
v___x_2146_ = lean_usize_add(v_i_2135_, v___x_2145_);
v_i_2135_ = v___x_2146_;
v_b_2137_ = v_a_2144_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2132_ = stack[0].m_num;
lean_object* v_f_2133_ = stack[1].m_obj;
lean_object* v_as_2134_ = stack[2].m_obj;
size_t v_i_2135_ = stack[3].m_num;
size_t v_stop_2136_ = stack[4].m_num;
lean_object* v_b_2137_ = stack[5].m_obj;
lean_object* v___y_2138_ = stack[6].m_obj;
lean_object* v___y_2139_ = stack[7].m_obj;
lean_object* v___y_2140_ = stack[8].m_obj;
lean_object* v___y_2141_ = stack[9].m_obj;
lean_object* v_res_2166_;
v_res_2166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2132_, v_f_2133_, v_as_2134_, v_i_2135_, v_stop_2136_, v_b_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
stack->m_obj
 = v_res_2166_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0___boxed(lean_object* v_pu_2167_, lean_object* v_f_2168_, lean_object* v_as_2169_, lean_object* v_i_2170_, lean_object* v_stop_2171_, lean_object* v_b_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v_pu_boxed_2178_; size_t v_i_boxed_2179_; size_t v_stop_boxed_2180_; lean_object* v_res_2181_; 
v_pu_boxed_2178_ = lean_unbox(v_pu_2167_);
v_i_boxed_2179_ = lean_unbox_usize(v_i_2170_);
lean_dec(v_i_2170_);
v_stop_boxed_2180_ = lean_unbox_usize(v_stop_2171_);
lean_dec(v_stop_2171_);
v_res_2181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_boxed_2178_, v_f_2168_, v_as_2169_, v_i_boxed_2179_, v_stop_boxed_2180_, v_b_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec_ref(v_as_2169_);
return v_res_2181_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl(uint8_t v_pu_2182_, lean_object* v_f_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = lean_array_get_size(v_a_2184_);
v___x_2192_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2193_ = lean_nat_dec_lt(v___x_2190_, v___x_2191_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_dec_ref(v_f_2183_);
v___x_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
return v___x_2194_;
}
else
{
size_t v___x_2195_; size_t v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = ((size_t)0ULL);
v___x_2196_ = lean_usize_of_nat(v___x_2191_);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByFunDecl_spec__0(v_pu_2182_, v_f_2183_, v_a_2184_, v___x_2195_, v___x_2196_, v___x_2192_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
return v___x_2197_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filterByFunDecl_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2182_ = stack[0].m_num;
lean_object* v_f_2183_ = stack[1].m_obj;
lean_object* v_a_2184_ = stack[2].m_obj;
lean_object* v_a_2185_ = stack[3].m_obj;
lean_object* v_a_2186_ = stack[4].m_obj;
lean_object* v_a_2187_ = stack[5].m_obj;
lean_object* v_a_2188_ = stack[6].m_obj;
lean_object* v_res_2198_;
v_res_2198_ = l_Lean_Compiler_LCNF_Probe_filterByFunDecl(v_pu_2182_, v_f_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
stack->m_obj
 = v_res_2198_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByFunDecl___boxed(lean_object* v_pu_2199_, lean_object* v_f_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
uint8_t v_pu_boxed_2207_; lean_object* v_res_2208_; 
v_pu_boxed_2207_ = lean_unbox(v_pu_2199_);
v_res_2208_ = l_Lean_Compiler_LCNF_Probe_filterByFunDecl(v_pu_boxed_2207_, v_f_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec_ref(v_a_2201_);
return v_res_2208_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(uint8_t v_pu_2209_, lean_object* v_f_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_){
_start:
{
switch(lean_obj_tag(v_a_2211_))
{
case 0:
{
lean_object* v_k_2217_; 
v_k_2217_ = lean_ctor_get(v_a_2211_, 1);
lean_inc_ref(v_k_2217_);
lean_dec_ref_known(v_a_2211_, 2);
v_a_2211_ = v_k_2217_;
goto _start;
}
case 1:
{
lean_object* v_decl_2219_; lean_object* v_k_2220_; lean_object* v_value_2221_; lean_object* v___x_2222_; 
v_decl_2219_ = lean_ctor_get(v_a_2211_, 0);
lean_inc_ref(v_decl_2219_);
v_k_2220_ = lean_ctor_get(v_a_2211_, 1);
lean_inc_ref(v_k_2220_);
lean_dec_ref_known(v_a_2211_, 2);
v_value_2221_ = lean_ctor_get(v_decl_2219_, 4);
lean_inc_ref(v_value_2221_);
lean_dec_ref(v_decl_2219_);
lean_inc_ref(v_f_2210_);
v___x_2222_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2209_, v_f_2210_, v_value_2221_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; uint8_t v___x_2224_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v___x_2224_ = lean_unbox(v_a_2223_);
if (v___x_2224_ == 0)
{
lean_dec_ref_known(v___x_2222_, 1);
v_a_2211_ = v_k_2220_;
goto _start;
}
else
{
lean_dec_ref(v_k_2220_);
lean_dec_ref(v_f_2210_);
return v___x_2222_;
}
}
else
{
lean_dec_ref(v_k_2220_);
lean_dec_ref(v_f_2210_);
return v___x_2222_;
}
}
case 2:
{
lean_object* v_decl_2226_; lean_object* v_k_2227_; lean_object* v_value_2228_; lean_object* v___x_2229_; 
v_decl_2226_ = lean_ctor_get(v_a_2211_, 0);
lean_inc_ref(v_decl_2226_);
v_k_2227_ = lean_ctor_get(v_a_2211_, 1);
lean_inc_ref(v_k_2227_);
lean_dec_ref_known(v_a_2211_, 2);
v_value_2228_ = lean_ctor_get(v_decl_2226_, 4);
lean_inc_ref(v_value_2228_);
lean_dec_ref(v_decl_2226_);
lean_inc_ref(v_f_2210_);
v___x_2229_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2209_, v_f_2210_, v_value_2228_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; uint8_t v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v___x_2231_ = lean_unbox(v_a_2230_);
if (v___x_2231_ == 0)
{
lean_dec_ref_known(v___x_2229_, 1);
v_a_2211_ = v_k_2227_;
goto _start;
}
else
{
lean_dec_ref(v_k_2227_);
lean_dec_ref(v_f_2210_);
return v___x_2229_;
}
}
else
{
lean_dec_ref(v_k_2227_);
lean_dec_ref(v_f_2210_);
return v___x_2229_;
}
}
case 4:
{
lean_object* v_cases_2233_; lean_object* v___x_2234_; 
v_cases_2233_ = lean_ctor_get(v_a_2211_, 0);
lean_inc_ref_n(v_cases_2233_, 2);
lean_dec_ref_known(v_a_2211_, 1);
lean_inc_ref(v_f_2210_);
lean_inc(v_a_2215_);
lean_inc_ref(v_a_2214_);
lean_inc(v_a_2213_);
lean_inc_ref(v_a_2212_);
v___x_2234_ = lean_apply_6(v_f_2210_, v_cases_2233_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, lean_box(0));
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; uint8_t v___x_2236_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
v___x_2236_ = lean_unbox(v_a_2235_);
lean_dec(v_a_2235_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2255_; 
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v___x_2234_, 0);
lean_dec(v_unused_2256_);
v___x_2238_ = v___x_2234_;
v_isShared_2239_ = v_isSharedCheck_2255_;
goto v_resetjp_2237_;
}
else
{
lean_dec(v___x_2234_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2255_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_alts_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v_alts_2240_ = lean_ctor_get(v_cases_2233_, 3);
lean_inc_ref(v_alts_2240_);
lean_dec_ref(v_cases_2233_);
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = lean_array_get_size(v_alts_2240_);
v___x_2243_ = lean_nat_dec_lt(v___x_2241_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
lean_dec_ref(v_alts_2240_);
lean_dec_ref(v_f_2210_);
v___x_2244_ = lean_box(v___x_2243_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2244_);
v___x_2246_ = v___x_2238_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
else
{
if (v___x_2243_ == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
lean_dec_ref(v_alts_2240_);
lean_dec_ref(v_f_2210_);
v___x_2248_ = lean_box(v___x_2243_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2248_);
v___x_2250_ = v___x_2238_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
size_t v___x_2252_; size_t v___x_2253_; lean_object* v___x_2254_; 
lean_del_object(v___x_2238_);
v___x_2252_ = ((size_t)0ULL);
v___x_2253_ = lean_usize_of_nat(v___x_2242_);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_2209_, v_f_2210_, v_alts_2240_, v___x_2252_, v___x_2253_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
lean_dec_ref(v_alts_2240_);
return v___x_2254_;
}
}
}
}
else
{
lean_dec_ref(v_cases_2233_);
lean_dec_ref(v_f_2210_);
return v___x_2234_;
}
}
else
{
lean_dec_ref(v_cases_2233_);
lean_dec_ref(v_f_2210_);
return v___x_2234_;
}
}
case 7:
{
lean_object* v_k_2257_; 
v_k_2257_ = lean_ctor_get(v_a_2211_, 3);
lean_inc_ref(v_k_2257_);
lean_dec_ref_known(v_a_2211_, 4);
v_a_2211_ = v_k_2257_;
goto _start;
}
case 8:
{
lean_object* v_k_2259_; 
v_k_2259_ = lean_ctor_get(v_a_2211_, 3);
lean_inc_ref(v_k_2259_);
lean_dec_ref_known(v_a_2211_, 4);
v_a_2211_ = v_k_2259_;
goto _start;
}
case 9:
{
lean_object* v_k_2261_; 
v_k_2261_ = lean_ctor_get(v_a_2211_, 5);
lean_inc_ref(v_k_2261_);
lean_dec_ref_known(v_a_2211_, 6);
v_a_2211_ = v_k_2261_;
goto _start;
}
case 10:
{
lean_object* v_k_2263_; 
v_k_2263_ = lean_ctor_get(v_a_2211_, 2);
lean_inc_ref(v_k_2263_);
lean_dec_ref_known(v_a_2211_, 3);
v_a_2211_ = v_k_2263_;
goto _start;
}
case 11:
{
lean_object* v_k_2265_; 
v_k_2265_ = lean_ctor_get(v_a_2211_, 2);
lean_inc_ref(v_k_2265_);
lean_dec_ref_known(v_a_2211_, 3);
v_a_2211_ = v_k_2265_;
goto _start;
}
case 12:
{
lean_object* v_k_2267_; 
v_k_2267_ = lean_ctor_get(v_a_2211_, 3);
lean_inc_ref(v_k_2267_);
lean_dec_ref_known(v_a_2211_, 4);
v_a_2211_ = v_k_2267_;
goto _start;
}
case 13:
{
lean_object* v_k_2269_; 
v_k_2269_ = lean_ctor_get(v_a_2211_, 1);
lean_inc_ref(v_k_2269_);
lean_dec_ref_known(v_a_2211_, 2);
v_a_2211_ = v_k_2269_;
goto _start;
}
default: 
{
uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_f_2210_);
v___x_2271_ = 0;
v___x_2272_ = lean_box(v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2209_ = stack[0].m_num;
lean_object* v_f_2210_ = stack[1].m_obj;
lean_object* v_a_2211_ = stack[2].m_obj;
lean_object* v_a_2212_ = stack[3].m_obj;
lean_object* v_a_2213_ = stack[4].m_obj;
lean_object* v_a_2214_ = stack[5].m_obj;
lean_object* v_a_2215_ = stack[6].m_obj;
lean_object* v_res_2274_;
v_res_2274_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2209_, v_f_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
stack->m_obj
 = v_res_2274_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(uint8_t v_pu_2275_, lean_object* v_f_2276_, lean_object* v_as_2277_, size_t v_i_2278_, size_t v_stop_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
uint8_t v___x_2285_; 
v___x_2285_ = lean_usize_dec_eq(v_i_2278_, v_stop_2279_);
if (v___x_2285_ == 0)
{
uint8_t v___x_2286_; lean_object* v___y_2288_; lean_object* v___x_2303_; 
v___x_2286_ = 1;
v___x_2303_ = lean_array_uget_borrowed(v_as_2277_, v_i_2278_);
switch(lean_obj_tag(v___x_2303_))
{
case 0:
{
lean_object* v_code_2304_; 
v_code_2304_ = lean_ctor_get(v___x_2303_, 2);
lean_inc_ref(v_code_2304_);
v___y_2288_ = v_code_2304_;
goto v___jp_2287_;
}
case 1:
{
lean_object* v_code_2305_; 
v_code_2305_ = lean_ctor_get(v___x_2303_, 1);
lean_inc_ref(v_code_2305_);
v___y_2288_ = v_code_2305_;
goto v___jp_2287_;
}
default: 
{
lean_object* v_code_2306_; 
v_code_2306_ = lean_ctor_get(v___x_2303_, 0);
lean_inc_ref(v_code_2306_);
v___y_2288_ = v_code_2306_;
goto v___jp_2287_;
}
}
v___jp_2287_:
{
lean_object* v___x_2289_; 
lean_inc_ref(v_f_2276_);
v___x_2289_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_2275_, v_f_2276_, v___y_2288_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2302_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2302_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2302_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
uint8_t v___x_2294_; 
v___x_2294_ = lean_unbox(v_a_2290_);
lean_dec(v_a_2290_);
if (v___x_2294_ == 0)
{
size_t v___x_2295_; size_t v___x_2296_; 
lean_del_object(v___x_2292_);
v___x_2295_ = ((size_t)1ULL);
v___x_2296_ = lean_usize_add(v_i_2278_, v___x_2295_);
v_i_2278_ = v___x_2296_;
goto _start;
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
lean_dec_ref(v_f_2276_);
v___x_2298_ = lean_box(v___x_2286_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2298_);
v___x_2300_ = v___x_2292_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_dec_ref(v_f_2276_);
return v___x_2289_;
}
}
}
else
{
uint8_t v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
lean_dec_ref(v_f_2276_);
v___x_2307_ = 0;
v___x_2308_ = lean_box(v___x_2307_);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2275_ = stack[0].m_num;
lean_object* v_f_2276_ = stack[1].m_obj;
lean_object* v_as_2277_ = stack[2].m_obj;
size_t v_i_2278_ = stack[3].m_num;
size_t v_stop_2279_ = stack[4].m_num;
lean_object* v___y_2280_ = stack[5].m_obj;
lean_object* v___y_2281_ = stack[6].m_obj;
lean_object* v___y_2282_ = stack[7].m_obj;
lean_object* v___y_2283_ = stack[8].m_obj;
lean_object* v_res_2310_;
v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_2275_, v_f_2276_, v_as_2277_, v_i_2278_, v_stop_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
stack->m_obj
 = v_res_2310_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0___boxed(lean_object* v_pu_2311_, lean_object* v_f_2312_, lean_object* v_as_2313_, lean_object* v_i_2314_, lean_object* v_stop_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
uint8_t v_pu_boxed_2321_; size_t v_i_boxed_2322_; size_t v_stop_boxed_2323_; lean_object* v_res_2324_; 
v_pu_boxed_2321_ = lean_unbox(v_pu_2311_);
v_i_boxed_2322_ = lean_unbox_usize(v_i_2314_);
lean_dec(v_i_2314_);
v_stop_boxed_2323_ = lean_unbox_usize(v_stop_2315_);
lean_dec(v_stop_2315_);
v_res_2324_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go_spec__0(v_pu_boxed_2321_, v_f_2312_, v_as_2313_, v_i_boxed_2322_, v_stop_boxed_2323_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v_as_2313_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed(lean_object* v_pu_2325_, lean_object* v_f_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
uint8_t v_pu_boxed_2333_; lean_object* v_res_2334_; 
v_pu_boxed_2333_ = lean_unbox(v_pu_2325_);
v_res_2334_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go(v_pu_boxed_2333_, v_f_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
return v_res_2334_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(uint8_t v_pu_2335_, lean_object* v_f_2336_, lean_object* v_as_2337_, size_t v_i_2338_, size_t v_stop_2339_, lean_object* v_b_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_a_2347_; uint8_t v___x_2351_; 
v___x_2351_ = lean_usize_dec_eq(v_i_2338_, v_stop_2339_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; lean_object* v_value_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2352_ = lean_array_uget_borrowed(v_as_2337_, v_i_2338_);
v_value_2353_ = lean_ctor_get(v___x_2352_, 1);
v___x_2354_ = lean_box(v_pu_2335_);
lean_inc_ref(v_f_2336_);
v___x_2355_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByCases_go___boxed), 8, 2);
lean_closure_set(v___x_2355_, 0, v___x_2354_);
lean_closure_set(v___x_2355_, 1, v_f_2336_);
lean_inc_ref(v_value_2353_);
v___x_2356_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2353_, v___x_2355_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; uint8_t v___x_2358_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v___x_2358_ = lean_unbox(v_a_2357_);
lean_dec(v_a_2357_);
if (v___x_2358_ == 0)
{
v_a_2347_ = v_b_2340_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2359_; 
lean_inc(v___x_2352_);
v___x_2359_ = lean_array_push(v_b_2340_, v___x_2352_);
v_a_2347_ = v___x_2359_;
goto v___jp_2346_;
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v_b_2340_);
lean_dec_ref(v_f_2336_);
v_a_2360_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2356_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2356_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v___x_2368_; 
lean_dec_ref(v_f_2336_);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v_b_2340_);
return v___x_2368_;
}
v___jp_2346_:
{
size_t v___x_2348_; size_t v___x_2349_; 
v___x_2348_ = ((size_t)1ULL);
v___x_2349_ = lean_usize_add(v_i_2338_, v___x_2348_);
v_i_2338_ = v___x_2349_;
v_b_2340_ = v_a_2347_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2335_ = stack[0].m_num;
lean_object* v_f_2336_ = stack[1].m_obj;
lean_object* v_as_2337_ = stack[2].m_obj;
size_t v_i_2338_ = stack[3].m_num;
size_t v_stop_2339_ = stack[4].m_num;
lean_object* v_b_2340_ = stack[5].m_obj;
lean_object* v___y_2341_ = stack[6].m_obj;
lean_object* v___y_2342_ = stack[7].m_obj;
lean_object* v___y_2343_ = stack[8].m_obj;
lean_object* v___y_2344_ = stack[9].m_obj;
lean_object* v_res_2369_;
v_res_2369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2335_, v_f_2336_, v_as_2337_, v_i_2338_, v_stop_2339_, v_b_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
stack->m_obj
 = v_res_2369_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0___boxed(lean_object* v_pu_2370_, lean_object* v_f_2371_, lean_object* v_as_2372_, lean_object* v_i_2373_, lean_object* v_stop_2374_, lean_object* v_b_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
uint8_t v_pu_boxed_2381_; size_t v_i_boxed_2382_; size_t v_stop_boxed_2383_; lean_object* v_res_2384_; 
v_pu_boxed_2381_ = lean_unbox(v_pu_2370_);
v_i_boxed_2382_ = lean_unbox_usize(v_i_2373_);
lean_dec(v_i_2373_);
v_stop_boxed_2383_ = lean_unbox_usize(v_stop_2374_);
lean_dec(v_stop_2374_);
v_res_2384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_boxed_2381_, v_f_2371_, v_as_2372_, v_i_boxed_2382_, v_stop_boxed_2383_, v_b_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec_ref(v_as_2372_);
return v_res_2384_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases(uint8_t v_pu_2385_, lean_object* v_f_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2393_ = lean_unsigned_to_nat(0u);
v___x_2394_ = lean_array_get_size(v_a_2387_);
v___x_2395_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2396_ = lean_nat_dec_lt(v___x_2393_, v___x_2394_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2397_; 
lean_dec_ref(v_f_2386_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2395_);
return v___x_2397_;
}
else
{
size_t v___x_2398_; size_t v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = ((size_t)0ULL);
v___x_2399_ = lean_usize_of_nat(v___x_2394_);
v___x_2400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByCases_spec__0(v_pu_2385_, v_f_2386_, v_a_2387_, v___x_2398_, v___x_2399_, v___x_2395_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
return v___x_2400_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filterByCases_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2385_ = stack[0].m_num;
lean_object* v_f_2386_ = stack[1].m_obj;
lean_object* v_a_2387_ = stack[2].m_obj;
lean_object* v_a_2388_ = stack[3].m_obj;
lean_object* v_a_2389_ = stack[4].m_obj;
lean_object* v_a_2390_ = stack[5].m_obj;
lean_object* v_a_2391_ = stack[6].m_obj;
lean_object* v_res_2401_;
v_res_2401_ = l_Lean_Compiler_LCNF_Probe_filterByCases(v_pu_2385_, v_f_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
stack->m_obj
 = v_res_2401_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByCases___boxed(lean_object* v_pu_2402_, lean_object* v_f_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
uint8_t v_pu_boxed_2410_; lean_object* v_res_2411_; 
v_pu_boxed_2410_ = lean_unbox(v_pu_2402_);
v_res_2411_ = l_Lean_Compiler_LCNF_Probe_filterByCases(v_pu_boxed_2410_, v_f_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec_ref(v_a_2404_);
return v_res_2411_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(uint8_t v_pu_2412_, lean_object* v_f_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
switch(lean_obj_tag(v_a_2414_))
{
case 0:
{
lean_object* v_k_2420_; 
v_k_2420_ = lean_ctor_get(v_a_2414_, 1);
lean_inc_ref(v_k_2420_);
lean_dec_ref_known(v_a_2414_, 2);
v_a_2414_ = v_k_2420_;
goto _start;
}
case 1:
{
lean_object* v_decl_2422_; lean_object* v_k_2423_; lean_object* v_value_2424_; lean_object* v___x_2425_; 
v_decl_2422_ = lean_ctor_get(v_a_2414_, 0);
lean_inc_ref(v_decl_2422_);
v_k_2423_ = lean_ctor_get(v_a_2414_, 1);
lean_inc_ref(v_k_2423_);
lean_dec_ref_known(v_a_2414_, 2);
v_value_2424_ = lean_ctor_get(v_decl_2422_, 4);
lean_inc_ref(v_value_2424_);
lean_dec_ref(v_decl_2422_);
lean_inc_ref(v_f_2413_);
v___x_2425_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2412_, v_f_2413_, v_value_2424_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; uint8_t v___x_2427_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v___x_2427_ = lean_unbox(v_a_2426_);
if (v___x_2427_ == 0)
{
lean_dec_ref_known(v___x_2425_, 1);
v_a_2414_ = v_k_2423_;
goto _start;
}
else
{
lean_dec_ref(v_k_2423_);
lean_dec_ref(v_f_2413_);
return v___x_2425_;
}
}
else
{
lean_dec_ref(v_k_2423_);
lean_dec_ref(v_f_2413_);
return v___x_2425_;
}
}
case 2:
{
lean_object* v_decl_2429_; lean_object* v_k_2430_; lean_object* v_value_2431_; lean_object* v___x_2432_; 
v_decl_2429_ = lean_ctor_get(v_a_2414_, 0);
lean_inc_ref(v_decl_2429_);
v_k_2430_ = lean_ctor_get(v_a_2414_, 1);
lean_inc_ref(v_k_2430_);
lean_dec_ref_known(v_a_2414_, 2);
v_value_2431_ = lean_ctor_get(v_decl_2429_, 4);
lean_inc_ref(v_value_2431_);
lean_dec_ref(v_decl_2429_);
lean_inc_ref(v_f_2413_);
v___x_2432_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2412_, v_f_2413_, v_value_2431_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; uint8_t v___x_2434_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v___x_2434_ = lean_unbox(v_a_2433_);
if (v___x_2434_ == 0)
{
lean_dec_ref_known(v___x_2432_, 1);
v_a_2414_ = v_k_2430_;
goto _start;
}
else
{
lean_dec_ref(v_k_2430_);
lean_dec_ref(v_f_2413_);
return v___x_2432_;
}
}
else
{
lean_dec_ref(v_k_2430_);
lean_dec_ref(v_f_2413_);
return v___x_2432_;
}
}
case 3:
{
lean_object* v_fvarId_2436_; lean_object* v_args_2437_; lean_object* v___x_2438_; 
v_fvarId_2436_ = lean_ctor_get(v_a_2414_, 0);
lean_inc(v_fvarId_2436_);
v_args_2437_ = lean_ctor_get(v_a_2414_, 1);
lean_inc_ref(v_args_2437_);
lean_dec_ref_known(v_a_2414_, 2);
lean_inc(v_a_2418_);
lean_inc_ref(v_a_2417_);
lean_inc(v_a_2416_);
lean_inc_ref(v_a_2415_);
v___x_2438_ = lean_apply_7(v_f_2413_, v_fvarId_2436_, v_args_2437_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, lean_box(0));
return v___x_2438_;
}
case 4:
{
lean_object* v_cases_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2458_; 
v_cases_2439_ = lean_ctor_get(v_a_2414_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_a_2414_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2441_ = v_a_2414_;
v_isShared_2442_ = v_isSharedCheck_2458_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_cases_2439_);
lean_dec(v_a_2414_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2458_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v_alts_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; uint8_t v___x_2446_; 
v_alts_2443_ = lean_ctor_get(v_cases_2439_, 3);
lean_inc_ref(v_alts_2443_);
lean_dec_ref(v_cases_2439_);
v___x_2444_ = lean_unsigned_to_nat(0u);
v___x_2445_ = lean_array_get_size(v_alts_2443_);
v___x_2446_ = lean_nat_dec_lt(v___x_2444_, v___x_2445_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
lean_dec_ref(v_alts_2443_);
lean_dec_ref(v_f_2413_);
v___x_2447_ = lean_box(v___x_2446_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set_tag(v___x_2441_, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2447_);
v___x_2449_ = v___x_2441_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
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
if (v___x_2446_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2453_; 
lean_dec_ref(v_alts_2443_);
lean_dec_ref(v_f_2413_);
v___x_2451_ = lean_box(v___x_2446_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set_tag(v___x_2441_, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2451_);
v___x_2453_ = v___x_2441_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
else
{
size_t v___x_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
lean_del_object(v___x_2441_);
v___x_2455_ = ((size_t)0ULL);
v___x_2456_ = lean_usize_of_nat(v___x_2445_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_2412_, v_f_2413_, v_alts_2443_, v___x_2455_, v___x_2456_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec_ref(v_alts_2443_);
return v___x_2457_;
}
}
}
}
case 7:
{
lean_object* v_k_2459_; 
v_k_2459_ = lean_ctor_get(v_a_2414_, 3);
lean_inc_ref(v_k_2459_);
lean_dec_ref_known(v_a_2414_, 4);
v_a_2414_ = v_k_2459_;
goto _start;
}
case 8:
{
lean_object* v_k_2461_; 
v_k_2461_ = lean_ctor_get(v_a_2414_, 3);
lean_inc_ref(v_k_2461_);
lean_dec_ref_known(v_a_2414_, 4);
v_a_2414_ = v_k_2461_;
goto _start;
}
case 9:
{
lean_object* v_k_2463_; 
v_k_2463_ = lean_ctor_get(v_a_2414_, 5);
lean_inc_ref(v_k_2463_);
lean_dec_ref_known(v_a_2414_, 6);
v_a_2414_ = v_k_2463_;
goto _start;
}
case 10:
{
lean_object* v_k_2465_; 
v_k_2465_ = lean_ctor_get(v_a_2414_, 2);
lean_inc_ref(v_k_2465_);
lean_dec_ref_known(v_a_2414_, 3);
v_a_2414_ = v_k_2465_;
goto _start;
}
case 11:
{
lean_object* v_k_2467_; 
v_k_2467_ = lean_ctor_get(v_a_2414_, 2);
lean_inc_ref(v_k_2467_);
lean_dec_ref_known(v_a_2414_, 3);
v_a_2414_ = v_k_2467_;
goto _start;
}
case 12:
{
lean_object* v_k_2469_; 
v_k_2469_ = lean_ctor_get(v_a_2414_, 3);
lean_inc_ref(v_k_2469_);
lean_dec_ref_known(v_a_2414_, 4);
v_a_2414_ = v_k_2469_;
goto _start;
}
case 13:
{
lean_object* v_k_2471_; 
v_k_2471_ = lean_ctor_get(v_a_2414_, 1);
lean_inc_ref(v_k_2471_);
lean_dec_ref_known(v_a_2414_, 2);
v_a_2414_ = v_k_2471_;
goto _start;
}
default: 
{
uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_dec_ref(v_a_2414_);
lean_dec_ref(v_f_2413_);
v___x_2473_ = 0;
v___x_2474_ = lean_box(v___x_2473_);
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
return v___x_2475_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2412_ = stack[0].m_num;
lean_object* v_f_2413_ = stack[1].m_obj;
lean_object* v_a_2414_ = stack[2].m_obj;
lean_object* v_a_2415_ = stack[3].m_obj;
lean_object* v_a_2416_ = stack[4].m_obj;
lean_object* v_a_2417_ = stack[5].m_obj;
lean_object* v_a_2418_ = stack[6].m_obj;
lean_object* v_res_2476_;
v_res_2476_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2412_, v_f_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
stack->m_obj
 = v_res_2476_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(uint8_t v_pu_2477_, lean_object* v_f_2478_, lean_object* v_as_2479_, size_t v_i_2480_, size_t v_stop_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_usize_dec_eq(v_i_2480_, v_stop_2481_);
if (v___x_2487_ == 0)
{
uint8_t v___x_2488_; lean_object* v___y_2490_; lean_object* v___x_2505_; 
v___x_2488_ = 1;
v___x_2505_ = lean_array_uget_borrowed(v_as_2479_, v_i_2480_);
switch(lean_obj_tag(v___x_2505_))
{
case 0:
{
lean_object* v_code_2506_; 
v_code_2506_ = lean_ctor_get(v___x_2505_, 2);
lean_inc_ref(v_code_2506_);
v___y_2490_ = v_code_2506_;
goto v___jp_2489_;
}
case 1:
{
lean_object* v_code_2507_; 
v_code_2507_ = lean_ctor_get(v___x_2505_, 1);
lean_inc_ref(v_code_2507_);
v___y_2490_ = v_code_2507_;
goto v___jp_2489_;
}
default: 
{
lean_object* v_code_2508_; 
v_code_2508_ = lean_ctor_get(v___x_2505_, 0);
lean_inc_ref(v_code_2508_);
v___y_2490_ = v_code_2508_;
goto v___jp_2489_;
}
}
v___jp_2489_:
{
lean_object* v___x_2491_; 
lean_inc_ref(v_f_2478_);
v___x_2491_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_2477_, v_f_2478_, v___y_2490_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2504_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2504_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2504_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
uint8_t v___x_2496_; 
v___x_2496_ = lean_unbox(v_a_2492_);
lean_dec(v_a_2492_);
if (v___x_2496_ == 0)
{
size_t v___x_2497_; size_t v___x_2498_; 
lean_del_object(v___x_2494_);
v___x_2497_ = ((size_t)1ULL);
v___x_2498_ = lean_usize_add(v_i_2480_, v___x_2497_);
v_i_2480_ = v___x_2498_;
goto _start;
}
else
{
lean_object* v___x_2500_; lean_object* v___x_2502_; 
lean_dec_ref(v_f_2478_);
v___x_2500_ = lean_box(v___x_2488_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2500_);
v___x_2502_ = v___x_2494_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
else
{
lean_dec_ref(v_f_2478_);
return v___x_2491_;
}
}
}
else
{
uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec_ref(v_f_2478_);
v___x_2509_ = 0;
v___x_2510_ = lean_box(v___x_2509_);
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
return v___x_2511_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2477_ = stack[0].m_num;
lean_object* v_f_2478_ = stack[1].m_obj;
lean_object* v_as_2479_ = stack[2].m_obj;
size_t v_i_2480_ = stack[3].m_num;
size_t v_stop_2481_ = stack[4].m_num;
lean_object* v___y_2482_ = stack[5].m_obj;
lean_object* v___y_2483_ = stack[6].m_obj;
lean_object* v___y_2484_ = stack[7].m_obj;
lean_object* v___y_2485_ = stack[8].m_obj;
lean_object* v_res_2512_;
v_res_2512_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_2477_, v_f_2478_, v_as_2479_, v_i_2480_, v_stop_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
stack->m_obj
 = v_res_2512_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0___boxed(lean_object* v_pu_2513_, lean_object* v_f_2514_, lean_object* v_as_2515_, lean_object* v_i_2516_, lean_object* v_stop_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
uint8_t v_pu_boxed_2523_; size_t v_i_boxed_2524_; size_t v_stop_boxed_2525_; lean_object* v_res_2526_; 
v_pu_boxed_2523_ = lean_unbox(v_pu_2513_);
v_i_boxed_2524_ = lean_unbox_usize(v_i_2516_);
lean_dec(v_i_2516_);
v_stop_boxed_2525_ = lean_unbox_usize(v_stop_2517_);
lean_dec(v_stop_2517_);
v_res_2526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go_spec__0(v_pu_boxed_2523_, v_f_2514_, v_as_2515_, v_i_boxed_2524_, v_stop_boxed_2525_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v_as_2515_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed(lean_object* v_pu_2527_, lean_object* v_f_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
uint8_t v_pu_boxed_2535_; lean_object* v_res_2536_; 
v_pu_boxed_2535_ = lean_unbox(v_pu_2527_);
v_res_2536_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go(v_pu_boxed_2535_, v_f_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
lean_dec(v_a_2533_);
lean_dec_ref(v_a_2532_);
lean_dec(v_a_2531_);
lean_dec_ref(v_a_2530_);
return v_res_2536_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(uint8_t v_pu_2537_, lean_object* v_f_2538_, lean_object* v_as_2539_, size_t v_i_2540_, size_t v_stop_2541_, lean_object* v_b_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_a_2549_; uint8_t v___x_2553_; 
v___x_2553_ = lean_usize_dec_eq(v_i_2540_, v_stop_2541_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v_value_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2554_ = lean_array_uget_borrowed(v_as_2539_, v_i_2540_);
v_value_2555_ = lean_ctor_get(v___x_2554_, 1);
v___x_2556_ = lean_box(v_pu_2537_);
lean_inc_ref(v_f_2538_);
v___x_2557_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByJmp_go___boxed), 8, 2);
lean_closure_set(v___x_2557_, 0, v___x_2556_);
lean_closure_set(v___x_2557_, 1, v_f_2538_);
lean_inc_ref(v_value_2555_);
v___x_2558_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2555_, v___x_2557_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; uint8_t v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = lean_unbox(v_a_2559_);
lean_dec(v_a_2559_);
if (v___x_2560_ == 0)
{
v_a_2549_ = v_b_2542_;
goto v___jp_2548_;
}
else
{
lean_object* v___x_2561_; 
lean_inc(v___x_2554_);
v___x_2561_ = lean_array_push(v_b_2542_, v___x_2554_);
v_a_2549_ = v___x_2561_;
goto v___jp_2548_;
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec_ref(v_b_2542_);
lean_dec_ref(v_f_2538_);
v_a_2562_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2558_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2558_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v___x_2570_; 
lean_dec_ref(v_f_2538_);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_b_2542_);
return v___x_2570_;
}
v___jp_2548_:
{
size_t v___x_2550_; size_t v___x_2551_; 
v___x_2550_ = ((size_t)1ULL);
v___x_2551_ = lean_usize_add(v_i_2540_, v___x_2550_);
v_i_2540_ = v___x_2551_;
v_b_2542_ = v_a_2549_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2537_ = stack[0].m_num;
lean_object* v_f_2538_ = stack[1].m_obj;
lean_object* v_as_2539_ = stack[2].m_obj;
size_t v_i_2540_ = stack[3].m_num;
size_t v_stop_2541_ = stack[4].m_num;
lean_object* v_b_2542_ = stack[5].m_obj;
lean_object* v___y_2543_ = stack[6].m_obj;
lean_object* v___y_2544_ = stack[7].m_obj;
lean_object* v___y_2545_ = stack[8].m_obj;
lean_object* v___y_2546_ = stack[9].m_obj;
lean_object* v_res_2571_;
v_res_2571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2537_, v_f_2538_, v_as_2539_, v_i_2540_, v_stop_2541_, v_b_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
stack->m_obj
 = v_res_2571_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0___boxed(lean_object* v_pu_2572_, lean_object* v_f_2573_, lean_object* v_as_2574_, lean_object* v_i_2575_, lean_object* v_stop_2576_, lean_object* v_b_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
uint8_t v_pu_boxed_2583_; size_t v_i_boxed_2584_; size_t v_stop_boxed_2585_; lean_object* v_res_2586_; 
v_pu_boxed_2583_ = lean_unbox(v_pu_2572_);
v_i_boxed_2584_ = lean_unbox_usize(v_i_2575_);
lean_dec(v_i_2575_);
v_stop_boxed_2585_ = lean_unbox_usize(v_stop_2576_);
lean_dec(v_stop_2576_);
v_res_2586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_boxed_2583_, v_f_2573_, v_as_2574_, v_i_boxed_2584_, v_stop_boxed_2585_, v_b_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec_ref(v_as_2574_);
return v_res_2586_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp(uint8_t v_pu_2587_, lean_object* v_f_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2595_ = lean_unsigned_to_nat(0u);
v___x_2596_ = lean_array_get_size(v_a_2589_);
v___x_2597_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2598_ = lean_nat_dec_lt(v___x_2595_, v___x_2596_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; 
lean_dec_ref(v_f_2588_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
return v___x_2599_;
}
else
{
size_t v___x_2600_; size_t v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = ((size_t)0ULL);
v___x_2601_ = lean_usize_of_nat(v___x_2596_);
v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByJmp_spec__0(v_pu_2587_, v_f_2588_, v_a_2589_, v___x_2600_, v___x_2601_, v___x_2597_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_);
return v___x_2602_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filterByJmp_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2587_ = stack[0].m_num;
lean_object* v_f_2588_ = stack[1].m_obj;
lean_object* v_a_2589_ = stack[2].m_obj;
lean_object* v_a_2590_ = stack[3].m_obj;
lean_object* v_a_2591_ = stack[4].m_obj;
lean_object* v_a_2592_ = stack[5].m_obj;
lean_object* v_a_2593_ = stack[6].m_obj;
lean_object* v_res_2603_;
v_res_2603_ = l_Lean_Compiler_LCNF_Probe_filterByJmp(v_pu_2587_, v_f_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_);
stack->m_obj
 = v_res_2603_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByJmp___boxed(lean_object* v_pu_2604_, lean_object* v_f_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_){
_start:
{
uint8_t v_pu_boxed_2612_; lean_object* v_res_2613_; 
v_pu_boxed_2612_ = lean_unbox(v_pu_2604_);
v_res_2613_ = l_Lean_Compiler_LCNF_Probe_filterByJmp(v_pu_boxed_2612_, v_f_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
lean_dec(v_a_2610_);
lean_dec_ref(v_a_2609_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
lean_dec_ref(v_a_2606_);
return v_res_2613_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(uint8_t v_pu_2614_, lean_object* v_f_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
switch(lean_obj_tag(v_a_2616_))
{
case 0:
{
lean_object* v_k_2622_; 
v_k_2622_ = lean_ctor_get(v_a_2616_, 1);
lean_inc_ref(v_k_2622_);
lean_dec_ref_known(v_a_2616_, 2);
v_a_2616_ = v_k_2622_;
goto _start;
}
case 1:
{
lean_object* v_decl_2624_; lean_object* v_k_2625_; lean_object* v_value_2626_; lean_object* v___x_2627_; 
v_decl_2624_ = lean_ctor_get(v_a_2616_, 0);
lean_inc_ref(v_decl_2624_);
v_k_2625_ = lean_ctor_get(v_a_2616_, 1);
lean_inc_ref(v_k_2625_);
lean_dec_ref_known(v_a_2616_, 2);
v_value_2626_ = lean_ctor_get(v_decl_2624_, 4);
lean_inc_ref(v_value_2626_);
lean_dec_ref(v_decl_2624_);
lean_inc_ref(v_f_2615_);
v___x_2627_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2614_, v_f_2615_, v_value_2626_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; uint8_t v___x_2629_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v___x_2629_ = lean_unbox(v_a_2628_);
if (v___x_2629_ == 0)
{
lean_dec_ref_known(v___x_2627_, 1);
v_a_2616_ = v_k_2625_;
goto _start;
}
else
{
lean_dec_ref(v_k_2625_);
lean_dec_ref(v_f_2615_);
return v___x_2627_;
}
}
else
{
lean_dec_ref(v_k_2625_);
lean_dec_ref(v_f_2615_);
return v___x_2627_;
}
}
case 2:
{
lean_object* v_decl_2631_; lean_object* v_k_2632_; lean_object* v_value_2633_; lean_object* v___x_2634_; 
v_decl_2631_ = lean_ctor_get(v_a_2616_, 0);
lean_inc_ref(v_decl_2631_);
v_k_2632_ = lean_ctor_get(v_a_2616_, 1);
lean_inc_ref(v_k_2632_);
lean_dec_ref_known(v_a_2616_, 2);
v_value_2633_ = lean_ctor_get(v_decl_2631_, 4);
lean_inc_ref(v_value_2633_);
lean_dec_ref(v_decl_2631_);
lean_inc_ref(v_f_2615_);
v___x_2634_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2614_, v_f_2615_, v_value_2633_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; uint8_t v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v___x_2636_ = lean_unbox(v_a_2635_);
if (v___x_2636_ == 0)
{
lean_dec_ref_known(v___x_2634_, 1);
v_a_2616_ = v_k_2632_;
goto _start;
}
else
{
lean_dec_ref(v_k_2632_);
lean_dec_ref(v_f_2615_);
return v___x_2634_;
}
}
else
{
lean_dec_ref(v_k_2632_);
lean_dec_ref(v_f_2615_);
return v___x_2634_;
}
}
case 4:
{
lean_object* v_cases_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2657_; 
v_cases_2638_ = lean_ctor_get(v_a_2616_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_a_2616_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2640_ = v_a_2616_;
v_isShared_2641_ = v_isSharedCheck_2657_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_cases_2638_);
lean_dec(v_a_2616_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2657_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v_alts_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v_alts_2642_ = lean_ctor_get(v_cases_2638_, 3);
lean_inc_ref(v_alts_2642_);
lean_dec_ref(v_cases_2638_);
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_array_get_size(v_alts_2642_);
v___x_2645_ = lean_nat_dec_lt(v___x_2643_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
lean_dec_ref(v_alts_2642_);
lean_dec_ref(v_f_2615_);
v___x_2646_ = lean_box(v___x_2645_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2646_);
v___x_2648_ = v___x_2640_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
else
{
if (v___x_2645_ == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2652_; 
lean_dec_ref(v_alts_2642_);
lean_dec_ref(v_f_2615_);
v___x_2650_ = lean_box(v___x_2645_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2650_);
v___x_2652_ = v___x_2640_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
else
{
size_t v___x_2654_; size_t v___x_2655_; lean_object* v___x_2656_; 
lean_del_object(v___x_2640_);
v___x_2654_ = ((size_t)0ULL);
v___x_2655_ = lean_usize_of_nat(v___x_2644_);
v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_2614_, v_f_2615_, v_alts_2642_, v___x_2654_, v___x_2655_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
lean_dec_ref(v_alts_2642_);
return v___x_2656_;
}
}
}
}
case 5:
{
lean_object* v_fvarId_2658_; lean_object* v___x_2659_; 
v_fvarId_2658_ = lean_ctor_get(v_a_2616_, 0);
lean_inc(v_fvarId_2658_);
lean_dec_ref_known(v_a_2616_, 1);
lean_inc(v_a_2620_);
lean_inc_ref(v_a_2619_);
lean_inc(v_a_2618_);
lean_inc_ref(v_a_2617_);
v___x_2659_ = lean_apply_6(v_f_2615_, v_fvarId_2658_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, lean_box(0));
return v___x_2659_;
}
case 7:
{
lean_object* v_k_2660_; 
v_k_2660_ = lean_ctor_get(v_a_2616_, 3);
lean_inc_ref(v_k_2660_);
lean_dec_ref_known(v_a_2616_, 4);
v_a_2616_ = v_k_2660_;
goto _start;
}
case 8:
{
lean_object* v_k_2662_; 
v_k_2662_ = lean_ctor_get(v_a_2616_, 3);
lean_inc_ref(v_k_2662_);
lean_dec_ref_known(v_a_2616_, 4);
v_a_2616_ = v_k_2662_;
goto _start;
}
case 9:
{
lean_object* v_k_2664_; 
v_k_2664_ = lean_ctor_get(v_a_2616_, 5);
lean_inc_ref(v_k_2664_);
lean_dec_ref_known(v_a_2616_, 6);
v_a_2616_ = v_k_2664_;
goto _start;
}
case 10:
{
lean_object* v_k_2666_; 
v_k_2666_ = lean_ctor_get(v_a_2616_, 2);
lean_inc_ref(v_k_2666_);
lean_dec_ref_known(v_a_2616_, 3);
v_a_2616_ = v_k_2666_;
goto _start;
}
case 11:
{
lean_object* v_k_2668_; 
v_k_2668_ = lean_ctor_get(v_a_2616_, 2);
lean_inc_ref(v_k_2668_);
lean_dec_ref_known(v_a_2616_, 3);
v_a_2616_ = v_k_2668_;
goto _start;
}
case 12:
{
lean_object* v_k_2670_; 
v_k_2670_ = lean_ctor_get(v_a_2616_, 3);
lean_inc_ref(v_k_2670_);
lean_dec_ref_known(v_a_2616_, 4);
v_a_2616_ = v_k_2670_;
goto _start;
}
case 13:
{
lean_object* v_k_2672_; 
v_k_2672_ = lean_ctor_get(v_a_2616_, 1);
lean_inc_ref(v_k_2672_);
lean_dec_ref_known(v_a_2616_, 2);
v_a_2616_ = v_k_2672_;
goto _start;
}
default: 
{
uint8_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
lean_dec_ref(v_a_2616_);
lean_dec_ref(v_f_2615_);
v___x_2674_ = 0;
v___x_2675_ = lean_box(v___x_2674_);
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
return v___x_2676_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2614_ = stack[0].m_num;
lean_object* v_f_2615_ = stack[1].m_obj;
lean_object* v_a_2616_ = stack[2].m_obj;
lean_object* v_a_2617_ = stack[3].m_obj;
lean_object* v_a_2618_ = stack[4].m_obj;
lean_object* v_a_2619_ = stack[5].m_obj;
lean_object* v_a_2620_ = stack[6].m_obj;
lean_object* v_res_2677_;
v_res_2677_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2614_, v_f_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
stack->m_obj
 = v_res_2677_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(uint8_t v_pu_2678_, lean_object* v_f_2679_, lean_object* v_as_2680_, size_t v_i_2681_, size_t v_stop_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
uint8_t v___x_2688_; 
v___x_2688_ = lean_usize_dec_eq(v_i_2681_, v_stop_2682_);
if (v___x_2688_ == 0)
{
uint8_t v___x_2689_; lean_object* v___y_2691_; lean_object* v___x_2706_; 
v___x_2689_ = 1;
v___x_2706_ = lean_array_uget_borrowed(v_as_2680_, v_i_2681_);
switch(lean_obj_tag(v___x_2706_))
{
case 0:
{
lean_object* v_code_2707_; 
v_code_2707_ = lean_ctor_get(v___x_2706_, 2);
lean_inc_ref(v_code_2707_);
v___y_2691_ = v_code_2707_;
goto v___jp_2690_;
}
case 1:
{
lean_object* v_code_2708_; 
v_code_2708_ = lean_ctor_get(v___x_2706_, 1);
lean_inc_ref(v_code_2708_);
v___y_2691_ = v_code_2708_;
goto v___jp_2690_;
}
default: 
{
lean_object* v_code_2709_; 
v_code_2709_ = lean_ctor_get(v___x_2706_, 0);
lean_inc_ref(v_code_2709_);
v___y_2691_ = v_code_2709_;
goto v___jp_2690_;
}
}
v___jp_2690_:
{
lean_object* v___x_2692_; 
lean_inc_ref(v_f_2679_);
v___x_2692_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_2678_, v_f_2679_, v___y_2691_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2705_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2705_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2705_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
uint8_t v___x_2697_; 
v___x_2697_ = lean_unbox(v_a_2693_);
lean_dec(v_a_2693_);
if (v___x_2697_ == 0)
{
size_t v___x_2698_; size_t v___x_2699_; 
lean_del_object(v___x_2695_);
v___x_2698_ = ((size_t)1ULL);
v___x_2699_ = lean_usize_add(v_i_2681_, v___x_2698_);
v_i_2681_ = v___x_2699_;
goto _start;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
lean_dec_ref(v_f_2679_);
v___x_2701_ = lean_box(v___x_2689_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2701_);
v___x_2703_ = v___x_2695_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_dec_ref(v_f_2679_);
return v___x_2692_;
}
}
}
else
{
uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_dec_ref(v_f_2679_);
v___x_2710_ = 0;
v___x_2711_ = lean_box(v___x_2710_);
v___x_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
return v___x_2712_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2678_ = stack[0].m_num;
lean_object* v_f_2679_ = stack[1].m_obj;
lean_object* v_as_2680_ = stack[2].m_obj;
size_t v_i_2681_ = stack[3].m_num;
size_t v_stop_2682_ = stack[4].m_num;
lean_object* v___y_2683_ = stack[5].m_obj;
lean_object* v___y_2684_ = stack[6].m_obj;
lean_object* v___y_2685_ = stack[7].m_obj;
lean_object* v___y_2686_ = stack[8].m_obj;
lean_object* v_res_2713_;
v_res_2713_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_2678_, v_f_2679_, v_as_2680_, v_i_2681_, v_stop_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
stack->m_obj
 = v_res_2713_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0___boxed(lean_object* v_pu_2714_, lean_object* v_f_2715_, lean_object* v_as_2716_, lean_object* v_i_2717_, lean_object* v_stop_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
uint8_t v_pu_boxed_2724_; size_t v_i_boxed_2725_; size_t v_stop_boxed_2726_; lean_object* v_res_2727_; 
v_pu_boxed_2724_ = lean_unbox(v_pu_2714_);
v_i_boxed_2725_ = lean_unbox_usize(v_i_2717_);
lean_dec(v_i_2717_);
v_stop_boxed_2726_ = lean_unbox_usize(v_stop_2718_);
lean_dec(v_stop_2718_);
v_res_2727_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go_spec__0(v_pu_boxed_2724_, v_f_2715_, v_as_2716_, v_i_boxed_2725_, v_stop_boxed_2726_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v_as_2716_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed(lean_object* v_pu_2728_, lean_object* v_f_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
uint8_t v_pu_boxed_2736_; lean_object* v_res_2737_; 
v_pu_boxed_2736_ = lean_unbox(v_pu_2728_);
v_res_2737_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go(v_pu_boxed_2736_, v_f_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
return v_res_2737_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(uint8_t v_pu_2738_, lean_object* v_f_2739_, lean_object* v_as_2740_, size_t v_i_2741_, size_t v_stop_2742_, lean_object* v_b_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_a_2750_; uint8_t v___x_2754_; 
v___x_2754_ = lean_usize_dec_eq(v_i_2741_, v_stop_2742_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v_value_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2755_ = lean_array_uget_borrowed(v_as_2740_, v_i_2741_);
v_value_2756_ = lean_ctor_get(v___x_2755_, 1);
v___x_2757_ = lean_box(v_pu_2738_);
lean_inc_ref(v_f_2739_);
v___x_2758_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByReturn_go___boxed), 8, 2);
lean_closure_set(v___x_2758_, 0, v___x_2757_);
lean_closure_set(v___x_2758_, 1, v_f_2739_);
lean_inc_ref(v_value_2756_);
v___x_2759_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2756_, v___x_2758_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; uint8_t v___x_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
v___x_2761_ = lean_unbox(v_a_2760_);
lean_dec(v_a_2760_);
if (v___x_2761_ == 0)
{
v_a_2750_ = v_b_2743_;
goto v___jp_2749_;
}
else
{
lean_object* v___x_2762_; 
lean_inc(v___x_2755_);
v___x_2762_ = lean_array_push(v_b_2743_, v___x_2755_);
v_a_2750_ = v___x_2762_;
goto v___jp_2749_;
}
}
else
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec_ref(v_b_2743_);
lean_dec_ref(v_f_2739_);
v_a_2763_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2759_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2759_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
else
{
lean_object* v___x_2771_; 
lean_dec_ref(v_f_2739_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_b_2743_);
return v___x_2771_;
}
v___jp_2749_:
{
size_t v___x_2751_; size_t v___x_2752_; 
v___x_2751_ = ((size_t)1ULL);
v___x_2752_ = lean_usize_add(v_i_2741_, v___x_2751_);
v_i_2741_ = v___x_2752_;
v_b_2743_ = v_a_2750_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2738_ = stack[0].m_num;
lean_object* v_f_2739_ = stack[1].m_obj;
lean_object* v_as_2740_ = stack[2].m_obj;
size_t v_i_2741_ = stack[3].m_num;
size_t v_stop_2742_ = stack[4].m_num;
lean_object* v_b_2743_ = stack[5].m_obj;
lean_object* v___y_2744_ = stack[6].m_obj;
lean_object* v___y_2745_ = stack[7].m_obj;
lean_object* v___y_2746_ = stack[8].m_obj;
lean_object* v___y_2747_ = stack[9].m_obj;
lean_object* v_res_2772_;
v_res_2772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2738_, v_f_2739_, v_as_2740_, v_i_2741_, v_stop_2742_, v_b_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
stack->m_obj
 = v_res_2772_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0___boxed(lean_object* v_pu_2773_, lean_object* v_f_2774_, lean_object* v_as_2775_, lean_object* v_i_2776_, lean_object* v_stop_2777_, lean_object* v_b_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v_pu_boxed_2784_; size_t v_i_boxed_2785_; size_t v_stop_boxed_2786_; lean_object* v_res_2787_; 
v_pu_boxed_2784_ = lean_unbox(v_pu_2773_);
v_i_boxed_2785_ = lean_unbox_usize(v_i_2776_);
lean_dec(v_i_2776_);
v_stop_boxed_2786_ = lean_unbox_usize(v_stop_2777_);
lean_dec(v_stop_2777_);
v_res_2787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_boxed_2784_, v_f_2774_, v_as_2775_, v_i_boxed_2785_, v_stop_boxed_2786_, v_b_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec_ref(v_as_2775_);
return v_res_2787_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn(uint8_t v_pu_2788_, lean_object* v_f_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2796_ = lean_unsigned_to_nat(0u);
v___x_2797_ = lean_array_get_size(v_a_2790_);
v___x_2798_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_2799_ = lean_nat_dec_lt(v___x_2796_, v___x_2797_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; 
lean_dec_ref(v_f_2789_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
return v___x_2800_;
}
else
{
size_t v___x_2801_; size_t v___x_2802_; lean_object* v___x_2803_; 
v___x_2801_ = ((size_t)0ULL);
v___x_2802_ = lean_usize_of_nat(v___x_2797_);
v___x_2803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByReturn_spec__0(v_pu_2788_, v_f_2789_, v_a_2790_, v___x_2801_, v___x_2802_, v___x_2798_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
return v___x_2803_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filterByReturn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2788_ = stack[0].m_num;
lean_object* v_f_2789_ = stack[1].m_obj;
lean_object* v_a_2790_ = stack[2].m_obj;
lean_object* v_a_2791_ = stack[3].m_obj;
lean_object* v_a_2792_ = stack[4].m_obj;
lean_object* v_a_2793_ = stack[5].m_obj;
lean_object* v_a_2794_ = stack[6].m_obj;
lean_object* v_res_2804_;
v_res_2804_ = l_Lean_Compiler_LCNF_Probe_filterByReturn(v_pu_2788_, v_f_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_);
stack->m_obj
 = v_res_2804_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByReturn___boxed(lean_object* v_pu_2805_, lean_object* v_f_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
uint8_t v_pu_boxed_2813_; lean_object* v_res_2814_; 
v_pu_boxed_2813_ = lean_unbox(v_pu_2805_);
v_res_2814_ = l_Lean_Compiler_LCNF_Probe_filterByReturn(v_pu_boxed_2813_, v_f_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec_ref(v_a_2807_);
return v_res_2814_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(uint8_t v_pu_2815_, lean_object* v_f_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
switch(lean_obj_tag(v_a_2817_))
{
case 0:
{
lean_object* v_k_2823_; 
v_k_2823_ = lean_ctor_get(v_a_2817_, 1);
lean_inc_ref(v_k_2823_);
lean_dec_ref_known(v_a_2817_, 2);
v_a_2817_ = v_k_2823_;
goto _start;
}
case 1:
{
lean_object* v_decl_2825_; lean_object* v_k_2826_; lean_object* v_value_2827_; lean_object* v___x_2828_; 
v_decl_2825_ = lean_ctor_get(v_a_2817_, 0);
lean_inc_ref(v_decl_2825_);
v_k_2826_ = lean_ctor_get(v_a_2817_, 1);
lean_inc_ref(v_k_2826_);
lean_dec_ref_known(v_a_2817_, 2);
v_value_2827_ = lean_ctor_get(v_decl_2825_, 4);
lean_inc_ref(v_value_2827_);
lean_dec_ref(v_decl_2825_);
lean_inc_ref(v_f_2816_);
v___x_2828_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2815_, v_f_2816_, v_value_2827_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; uint8_t v___x_2830_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v___x_2830_ = lean_unbox(v_a_2829_);
if (v___x_2830_ == 0)
{
lean_dec_ref_known(v___x_2828_, 1);
v_a_2817_ = v_k_2826_;
goto _start;
}
else
{
lean_dec_ref(v_k_2826_);
lean_dec_ref(v_f_2816_);
return v___x_2828_;
}
}
else
{
lean_dec_ref(v_k_2826_);
lean_dec_ref(v_f_2816_);
return v___x_2828_;
}
}
case 2:
{
lean_object* v_decl_2832_; lean_object* v_k_2833_; lean_object* v_value_2834_; lean_object* v___x_2835_; 
v_decl_2832_ = lean_ctor_get(v_a_2817_, 0);
lean_inc_ref(v_decl_2832_);
v_k_2833_ = lean_ctor_get(v_a_2817_, 1);
lean_inc_ref(v_k_2833_);
lean_dec_ref_known(v_a_2817_, 2);
v_value_2834_ = lean_ctor_get(v_decl_2832_, 4);
lean_inc_ref(v_value_2834_);
lean_dec_ref(v_decl_2832_);
lean_inc_ref(v_f_2816_);
v___x_2835_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2815_, v_f_2816_, v_value_2834_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; uint8_t v___x_2837_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
v___x_2837_ = lean_unbox(v_a_2836_);
if (v___x_2837_ == 0)
{
lean_dec_ref_known(v___x_2835_, 1);
v_a_2817_ = v_k_2833_;
goto _start;
}
else
{
lean_dec_ref(v_k_2833_);
lean_dec_ref(v_f_2816_);
return v___x_2835_;
}
}
else
{
lean_dec_ref(v_k_2833_);
lean_dec_ref(v_f_2816_);
return v___x_2835_;
}
}
case 4:
{
lean_object* v_cases_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2858_; 
v_cases_2839_ = lean_ctor_get(v_a_2817_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_a_2817_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2841_ = v_a_2817_;
v_isShared_2842_ = v_isSharedCheck_2858_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_cases_2839_);
lean_dec(v_a_2817_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2858_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_alts_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v_alts_2843_ = lean_ctor_get(v_cases_2839_, 3);
lean_inc_ref(v_alts_2843_);
lean_dec_ref(v_cases_2839_);
v___x_2844_ = lean_unsigned_to_nat(0u);
v___x_2845_ = lean_array_get_size(v_alts_2843_);
v___x_2846_ = lean_nat_dec_lt(v___x_2844_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2849_; 
lean_dec_ref(v_alts_2843_);
lean_dec_ref(v_f_2816_);
v___x_2847_ = lean_box(v___x_2846_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2847_);
v___x_2849_ = v___x_2841_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
else
{
if (v___x_2846_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2853_; 
lean_dec_ref(v_alts_2843_);
lean_dec_ref(v_f_2816_);
v___x_2851_ = lean_box(v___x_2846_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2851_);
v___x_2853_ = v___x_2841_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
else
{
size_t v___x_2855_; size_t v___x_2856_; lean_object* v___x_2857_; 
lean_del_object(v___x_2841_);
v___x_2855_ = ((size_t)0ULL);
v___x_2856_ = lean_usize_of_nat(v___x_2845_);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_2815_, v_f_2816_, v_alts_2843_, v___x_2855_, v___x_2856_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec_ref(v_alts_2843_);
return v___x_2857_;
}
}
}
}
case 6:
{
lean_object* v_type_2859_; lean_object* v___x_2860_; 
v_type_2859_ = lean_ctor_get(v_a_2817_, 0);
lean_inc_ref(v_type_2859_);
lean_dec_ref_known(v_a_2817_, 1);
lean_inc(v_a_2821_);
lean_inc_ref(v_a_2820_);
lean_inc(v_a_2819_);
lean_inc_ref(v_a_2818_);
v___x_2860_ = lean_apply_6(v_f_2816_, v_type_2859_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, lean_box(0));
return v___x_2860_;
}
case 7:
{
lean_object* v_k_2861_; 
v_k_2861_ = lean_ctor_get(v_a_2817_, 3);
lean_inc_ref(v_k_2861_);
lean_dec_ref_known(v_a_2817_, 4);
v_a_2817_ = v_k_2861_;
goto _start;
}
case 8:
{
lean_object* v_k_2863_; 
v_k_2863_ = lean_ctor_get(v_a_2817_, 3);
lean_inc_ref(v_k_2863_);
lean_dec_ref_known(v_a_2817_, 4);
v_a_2817_ = v_k_2863_;
goto _start;
}
case 9:
{
lean_object* v_k_2865_; 
v_k_2865_ = lean_ctor_get(v_a_2817_, 5);
lean_inc_ref(v_k_2865_);
lean_dec_ref_known(v_a_2817_, 6);
v_a_2817_ = v_k_2865_;
goto _start;
}
case 10:
{
lean_object* v_k_2867_; 
v_k_2867_ = lean_ctor_get(v_a_2817_, 2);
lean_inc_ref(v_k_2867_);
lean_dec_ref_known(v_a_2817_, 3);
v_a_2817_ = v_k_2867_;
goto _start;
}
case 11:
{
lean_object* v_k_2869_; 
v_k_2869_ = lean_ctor_get(v_a_2817_, 2);
lean_inc_ref(v_k_2869_);
lean_dec_ref_known(v_a_2817_, 3);
v_a_2817_ = v_k_2869_;
goto _start;
}
case 12:
{
lean_object* v_k_2871_; 
v_k_2871_ = lean_ctor_get(v_a_2817_, 3);
lean_inc_ref(v_k_2871_);
lean_dec_ref_known(v_a_2817_, 4);
v_a_2817_ = v_k_2871_;
goto _start;
}
case 13:
{
lean_object* v_k_2873_; 
v_k_2873_ = lean_ctor_get(v_a_2817_, 1);
lean_inc_ref(v_k_2873_);
lean_dec_ref_known(v_a_2817_, 2);
v_a_2817_ = v_k_2873_;
goto _start;
}
default: 
{
uint8_t v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec_ref(v_a_2817_);
lean_dec_ref(v_f_2816_);
v___x_2875_ = 0;
v___x_2876_ = lean_box(v___x_2875_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2815_ = stack[0].m_num;
lean_object* v_f_2816_ = stack[1].m_obj;
lean_object* v_a_2817_ = stack[2].m_obj;
lean_object* v_a_2818_ = stack[3].m_obj;
lean_object* v_a_2819_ = stack[4].m_obj;
lean_object* v_a_2820_ = stack[5].m_obj;
lean_object* v_a_2821_ = stack[6].m_obj;
lean_object* v_res_2878_;
v_res_2878_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2815_, v_f_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
stack->m_obj
 = v_res_2878_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(uint8_t v_pu_2879_, lean_object* v_f_2880_, lean_object* v_as_2881_, size_t v_i_2882_, size_t v_stop_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
uint8_t v___x_2889_; 
v___x_2889_ = lean_usize_dec_eq(v_i_2882_, v_stop_2883_);
if (v___x_2889_ == 0)
{
uint8_t v___x_2890_; lean_object* v___y_2892_; lean_object* v___x_2907_; 
v___x_2890_ = 1;
v___x_2907_ = lean_array_uget_borrowed(v_as_2881_, v_i_2882_);
switch(lean_obj_tag(v___x_2907_))
{
case 0:
{
lean_object* v_code_2908_; 
v_code_2908_ = lean_ctor_get(v___x_2907_, 2);
lean_inc_ref(v_code_2908_);
v___y_2892_ = v_code_2908_;
goto v___jp_2891_;
}
case 1:
{
lean_object* v_code_2909_; 
v_code_2909_ = lean_ctor_get(v___x_2907_, 1);
lean_inc_ref(v_code_2909_);
v___y_2892_ = v_code_2909_;
goto v___jp_2891_;
}
default: 
{
lean_object* v_code_2910_; 
v_code_2910_ = lean_ctor_get(v___x_2907_, 0);
lean_inc_ref(v_code_2910_);
v___y_2892_ = v_code_2910_;
goto v___jp_2891_;
}
}
v___jp_2891_:
{
lean_object* v___x_2893_; 
lean_inc_ref(v_f_2880_);
v___x_2893_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_2879_, v_f_2880_, v___y_2892_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2906_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2906_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2906_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
uint8_t v___x_2898_; 
v___x_2898_ = lean_unbox(v_a_2894_);
lean_dec(v_a_2894_);
if (v___x_2898_ == 0)
{
size_t v___x_2899_; size_t v___x_2900_; 
lean_del_object(v___x_2896_);
v___x_2899_ = ((size_t)1ULL);
v___x_2900_ = lean_usize_add(v_i_2882_, v___x_2899_);
v_i_2882_ = v___x_2900_;
goto _start;
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2904_; 
lean_dec_ref(v_f_2880_);
v___x_2902_ = lean_box(v___x_2890_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2902_);
v___x_2904_ = v___x_2896_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
else
{
lean_dec_ref(v_f_2880_);
return v___x_2893_;
}
}
}
else
{
uint8_t v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec_ref(v_f_2880_);
v___x_2911_ = 0;
v___x_2912_ = lean_box(v___x_2911_);
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
return v___x_2913_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2879_ = stack[0].m_num;
lean_object* v_f_2880_ = stack[1].m_obj;
lean_object* v_as_2881_ = stack[2].m_obj;
size_t v_i_2882_ = stack[3].m_num;
size_t v_stop_2883_ = stack[4].m_num;
lean_object* v___y_2884_ = stack[5].m_obj;
lean_object* v___y_2885_ = stack[6].m_obj;
lean_object* v___y_2886_ = stack[7].m_obj;
lean_object* v___y_2887_ = stack[8].m_obj;
lean_object* v_res_2914_;
v_res_2914_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_2879_, v_f_2880_, v_as_2881_, v_i_2882_, v_stop_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
stack->m_obj
 = v_res_2914_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0___boxed(lean_object* v_pu_2915_, lean_object* v_f_2916_, lean_object* v_as_2917_, lean_object* v_i_2918_, lean_object* v_stop_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
uint8_t v_pu_boxed_2925_; size_t v_i_boxed_2926_; size_t v_stop_boxed_2927_; lean_object* v_res_2928_; 
v_pu_boxed_2925_ = lean_unbox(v_pu_2915_);
v_i_boxed_2926_ = lean_unbox_usize(v_i_2918_);
lean_dec(v_i_2918_);
v_stop_boxed_2927_ = lean_unbox_usize(v_stop_2919_);
lean_dec(v_stop_2919_);
v_res_2928_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go_spec__0(v_pu_boxed_2925_, v_f_2916_, v_as_2917_, v_i_boxed_2926_, v_stop_boxed_2927_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v_as_2917_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed(lean_object* v_pu_2929_, lean_object* v_f_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
uint8_t v_pu_boxed_2937_; lean_object* v_res_2938_; 
v_pu_boxed_2937_ = lean_unbox(v_pu_2929_);
v_res_2938_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go(v_pu_boxed_2937_, v_f_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
return v_res_2938_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(uint8_t v_pu_2939_, lean_object* v_f_2940_, lean_object* v_as_2941_, size_t v_i_2942_, size_t v_stop_2943_, lean_object* v_b_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_a_2951_; uint8_t v___x_2955_; 
v___x_2955_ = lean_usize_dec_eq(v_i_2942_, v_stop_2943_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; lean_object* v_value_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2956_ = lean_array_uget_borrowed(v_as_2941_, v_i_2942_);
v_value_2957_ = lean_ctor_get(v___x_2956_, 1);
v___x_2958_ = lean_box(v_pu_2939_);
lean_inc_ref(v_f_2940_);
v___x_2959_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_filterByUnreach_go___boxed), 8, 2);
lean_closure_set(v___x_2959_, 0, v___x_2958_);
lean_closure_set(v___x_2959_, 1, v_f_2940_);
lean_inc_ref(v_value_2957_);
v___x_2960_ = l_Lean_Compiler_LCNF_DeclValue_isCodeAndM___at___00Lean_Compiler_LCNF_Probe_filterByLet_spec__0___redArg(v_value_2957_, v___x_2959_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; uint8_t v___x_2962_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = lean_unbox(v_a_2961_);
lean_dec(v_a_2961_);
if (v___x_2962_ == 0)
{
v_a_2951_ = v_b_2944_;
goto v___jp_2950_;
}
else
{
lean_object* v___x_2963_; 
lean_inc(v___x_2956_);
v___x_2963_ = lean_array_push(v_b_2944_, v___x_2956_);
v_a_2951_ = v___x_2963_;
goto v___jp_2950_;
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec_ref(v_b_2944_);
lean_dec_ref(v_f_2940_);
v_a_2964_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2960_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2960_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v___x_2972_; 
lean_dec_ref(v_f_2940_);
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v_b_2944_);
return v___x_2972_;
}
v___jp_2950_:
{
size_t v___x_2952_; size_t v___x_2953_; 
v___x_2952_ = ((size_t)1ULL);
v___x_2953_ = lean_usize_add(v_i_2942_, v___x_2952_);
v_i_2942_ = v___x_2953_;
v_b_2944_ = v_a_2951_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2939_ = stack[0].m_num;
lean_object* v_f_2940_ = stack[1].m_obj;
lean_object* v_as_2941_ = stack[2].m_obj;
size_t v_i_2942_ = stack[3].m_num;
size_t v_stop_2943_ = stack[4].m_num;
lean_object* v_b_2944_ = stack[5].m_obj;
lean_object* v___y_2945_ = stack[6].m_obj;
lean_object* v___y_2946_ = stack[7].m_obj;
lean_object* v___y_2947_ = stack[8].m_obj;
lean_object* v___y_2948_ = stack[9].m_obj;
lean_object* v_res_2973_;
v_res_2973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_2939_, v_f_2940_, v_as_2941_, v_i_2942_, v_stop_2943_, v_b_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
stack->m_obj
 = v_res_2973_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0___boxed(lean_object* v_pu_2974_, lean_object* v_f_2975_, lean_object* v_as_2976_, lean_object* v_i_2977_, lean_object* v_stop_2978_, lean_object* v_b_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
uint8_t v_pu_boxed_2985_; size_t v_i_boxed_2986_; size_t v_stop_boxed_2987_; lean_object* v_res_2988_; 
v_pu_boxed_2985_ = lean_unbox(v_pu_2974_);
v_i_boxed_2986_ = lean_unbox_usize(v_i_2977_);
lean_dec(v_i_2977_);
v_stop_boxed_2987_ = lean_unbox_usize(v_stop_2978_);
lean_dec(v_stop_2978_);
v_res_2988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_boxed_2985_, v_f_2975_, v_as_2976_, v_i_boxed_2986_, v_stop_boxed_2987_, v_b_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec_ref(v_as_2976_);
return v_res_2988_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach(uint8_t v_pu_2989_, lean_object* v_f_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2997_ = lean_unsigned_to_nat(0u);
v___x_2998_ = lean_array_get_size(v_a_2991_);
v___x_2999_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_filterByLet___closed__0));
v___x_3000_ = lean_nat_dec_lt(v___x_2997_, v___x_2998_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec_ref(v_f_2990_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
return v___x_3001_;
}
else
{
size_t v___x_3002_; size_t v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = ((size_t)0ULL);
v___x_3003_ = lean_usize_of_nat(v___x_2998_);
v___x_3004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Probe_filterByUnreach_spec__0(v_pu_2989_, v_f_2990_, v_a_2991_, v___x_3002_, v___x_3003_, v___x_2999_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
return v___x_3004_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_filterByUnreach_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_2989_ = stack[0].m_num;
lean_object* v_f_2990_ = stack[1].m_obj;
lean_object* v_a_2991_ = stack[2].m_obj;
lean_object* v_a_2992_ = stack[3].m_obj;
lean_object* v_a_2993_ = stack[4].m_obj;
lean_object* v_a_2994_ = stack[5].m_obj;
lean_object* v_a_2995_ = stack[6].m_obj;
lean_object* v_res_3005_;
v_res_3005_ = l_Lean_Compiler_LCNF_Probe_filterByUnreach(v_pu_2989_, v_f_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
stack->m_obj
 = v_res_3005_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_filterByUnreach___boxed(lean_object* v_pu_3006_, lean_object* v_f_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
uint8_t v_pu_boxed_3014_; lean_object* v_res_3015_; 
v_pu_boxed_3014_ = lean_unbox(v_pu_3006_);
v_res_3015_ = l_Lean_Compiler_LCNF_Probe_filterByUnreach(v_pu_boxed_3014_, v_f_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec_ref(v_a_3008_);
return v_res_3015_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(lean_object* v_decl_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_toSignature_3022_; lean_object* v_name_3023_; lean_object* v___x_3024_; 
v_toSignature_3022_ = lean_ctor_get(v_decl_3016_, 0);
v_name_3023_ = lean_ctor_get(v_toSignature_3022_, 0);
lean_inc(v_name_3023_);
v___x_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3024_, 0, v_name_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3016_ = stack[0].m_obj;
lean_object* v___y_3017_ = stack[1].m_obj;
lean_object* v___y_3018_ = stack[2].m_obj;
lean_object* v___y_3019_ = stack[3].m_obj;
lean_object* v___y_3020_ = stack[4].m_obj;
lean_object* v_res_3025_;
v_res_3025_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(v_decl_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
stack->m_obj
 = v_res_3025_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0___boxed(lean_object* v_decl_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg___lam__0(v_decl_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec_ref(v_decl_3026_);
return v_res_3032_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg(lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
lean_object* v___x_3040_; lean_object* v_toApplicative_3041_; lean_object* v_toFunctor_3042_; lean_object* v_toSeq_3043_; lean_object* v_toSeqLeft_3044_; lean_object* v_toSeqRight_3045_; lean_object* v___f_3046_; lean_object* v___f_3047_; lean_object* v___f_3048_; lean_object* v___f_3049_; lean_object* v___x_3050_; lean_object* v___f_3051_; lean_object* v___f_3052_; lean_object* v___f_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v_toApplicative_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3089_; 
v___x_3040_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3041_ = lean_ctor_get(v___x_3040_, 0);
v_toFunctor_3042_ = lean_ctor_get(v_toApplicative_3041_, 0);
v_toSeq_3043_ = lean_ctor_get(v_toApplicative_3041_, 2);
v_toSeqLeft_3044_ = lean_ctor_get(v_toApplicative_3041_, 3);
v_toSeqRight_3045_ = lean_ctor_get(v_toApplicative_3041_, 4);
v___f_3046_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3047_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3042_, 2);
v___f_3048_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3048_, 0, v_toFunctor_3042_);
v___f_3049_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3049_, 0, v_toFunctor_3042_);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___f_3048_);
lean_ctor_set(v___x_3050_, 1, v___f_3049_);
lean_inc(v_toSeqRight_3045_);
v___f_3051_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3051_, 0, v_toSeqRight_3045_);
lean_inc(v_toSeqLeft_3044_);
v___f_3052_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3052_, 0, v_toSeqLeft_3044_);
lean_inc(v_toSeq_3043_);
v___f_3053_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3053_, 0, v_toSeq_3043_);
v___x_3054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3050_);
lean_ctor_set(v___x_3054_, 1, v___f_3046_);
lean_ctor_set(v___x_3054_, 2, v___f_3053_);
lean_ctor_set(v___x_3054_, 3, v___f_3052_);
lean_ctor_set(v___x_3054_, 4, v___f_3051_);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___f_3047_);
v___x_3056_ = l_StateRefT_x27_instMonad___redArg(v___x_3055_);
v_toApplicative_3057_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_3056_, 1);
lean_dec(v_unused_3090_);
v___x_3059_ = v___x_3056_;
v_isShared_3060_ = v_isSharedCheck_3089_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_toApplicative_3057_);
lean_dec(v___x_3056_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3089_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v_toFunctor_3061_; lean_object* v_toSeq_3062_; lean_object* v_toSeqLeft_3063_; lean_object* v_toSeqRight_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3087_; 
v_toFunctor_3061_ = lean_ctor_get(v_toApplicative_3057_, 0);
v_toSeq_3062_ = lean_ctor_get(v_toApplicative_3057_, 2);
v_toSeqLeft_3063_ = lean_ctor_get(v_toApplicative_3057_, 3);
v_toSeqRight_3064_ = lean_ctor_get(v_toApplicative_3057_, 4);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_toApplicative_3057_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v_toApplicative_3057_, 1);
lean_dec(v_unused_3088_);
v___x_3066_ = v_toApplicative_3057_;
v_isShared_3067_ = v_isSharedCheck_3087_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_toSeqRight_3064_);
lean_inc(v_toSeqLeft_3063_);
lean_inc(v_toSeq_3062_);
lean_inc(v_toFunctor_3061_);
lean_dec(v_toApplicative_3057_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3087_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___f_3068_; lean_object* v___f_3069_; lean_object* v___f_3070_; lean_object* v___f_3071_; lean_object* v___f_3072_; lean_object* v___x_3073_; lean_object* v___f_3074_; lean_object* v___f_3075_; lean_object* v___f_3076_; lean_object* v___x_3078_; 
v___f_3068_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3069_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3070_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3061_);
v___f_3071_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3071_, 0, v_toFunctor_3061_);
v___f_3072_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3072_, 0, v_toFunctor_3061_);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___f_3071_);
lean_ctor_set(v___x_3073_, 1, v___f_3072_);
v___f_3074_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3074_, 0, v_toSeqRight_3064_);
v___f_3075_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3075_, 0, v_toSeqLeft_3063_);
v___f_3076_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3076_, 0, v_toSeq_3062_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 4, v___f_3074_);
lean_ctor_set(v___x_3066_, 3, v___f_3075_);
lean_ctor_set(v___x_3066_, 2, v___f_3076_);
lean_ctor_set(v___x_3066_, 1, v___f_3069_);
lean_ctor_set(v___x_3066_, 0, v___x_3073_);
v___x_3078_ = v___x_3066_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___f_3069_);
lean_ctor_set(v_reuseFailAlloc_3086_, 2, v___f_3076_);
lean_ctor_set(v_reuseFailAlloc_3086_, 3, v___f_3075_);
lean_ctor_set(v_reuseFailAlloc_3086_, 4, v___f_3074_);
v___x_3078_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3080_; 
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 1, v___f_3070_);
lean_ctor_set(v___x_3059_, 0, v___x_3078_);
v___x_3080_ = v___x_3059_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___f_3070_);
v___x_3080_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
size_t v_sz_3081_; size_t v___x_3082_; lean_object* v___x_127__overap_3083_; lean_object* v___x_3084_; 
v_sz_3081_ = lean_array_size(v_a_3034_);
v___x_3082_ = ((size_t)0ULL);
v___x_127__overap_3083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3080_, v___f_3068_, v_sz_3081_, v___x_3082_, v_a_3034_);
lean_inc(v_a_3038_);
lean_inc_ref(v_a_3037_);
lean_inc(v_a_3036_);
lean_inc_ref(v_a_3035_);
v___x_3084_ = lean_apply_5(v___x_127__overap_3083_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, lean_box(0));
return v___x_3084_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_declNames___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3034_ = stack[0].m_obj;
lean_object* v_a_3035_ = stack[1].m_obj;
lean_object* v_a_3036_ = stack[2].m_obj;
lean_object* v_a_3037_ = stack[3].m_obj;
lean_object* v_a_3038_ = stack[4].m_obj;
lean_object* v_res_3091_;
v_res_3091_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg(v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
stack->m_obj
 = v_res_3091_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___redArg___boxed(lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_Compiler_LCNF_Probe_declNames___redArg(v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
return v_res_3098_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_declNames(uint8_t v_pu_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
lean_object* v___x_3106_; lean_object* v_toApplicative_3107_; lean_object* v_toFunctor_3108_; lean_object* v_toSeq_3109_; lean_object* v_toSeqLeft_3110_; lean_object* v_toSeqRight_3111_; lean_object* v___f_3112_; lean_object* v___f_3113_; lean_object* v___f_3114_; lean_object* v___f_3115_; lean_object* v___x_3116_; lean_object* v___f_3117_; lean_object* v___f_3118_; lean_object* v___f_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v_toApplicative_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3155_; 
v___x_3106_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3107_ = lean_ctor_get(v___x_3106_, 0);
v_toFunctor_3108_ = lean_ctor_get(v_toApplicative_3107_, 0);
v_toSeq_3109_ = lean_ctor_get(v_toApplicative_3107_, 2);
v_toSeqLeft_3110_ = lean_ctor_get(v_toApplicative_3107_, 3);
v_toSeqRight_3111_ = lean_ctor_get(v_toApplicative_3107_, 4);
v___f_3112_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3113_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3108_, 2);
v___f_3114_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3114_, 0, v_toFunctor_3108_);
v___f_3115_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3115_, 0, v_toFunctor_3108_);
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___f_3114_);
lean_ctor_set(v___x_3116_, 1, v___f_3115_);
lean_inc(v_toSeqRight_3111_);
v___f_3117_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3117_, 0, v_toSeqRight_3111_);
lean_inc(v_toSeqLeft_3110_);
v___f_3118_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3118_, 0, v_toSeqLeft_3110_);
lean_inc(v_toSeq_3109_);
v___f_3119_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3119_, 0, v_toSeq_3109_);
v___x_3120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3116_);
lean_ctor_set(v___x_3120_, 1, v___f_3112_);
lean_ctor_set(v___x_3120_, 2, v___f_3119_);
lean_ctor_set(v___x_3120_, 3, v___f_3118_);
lean_ctor_set(v___x_3120_, 4, v___f_3117_);
v___x_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3120_);
lean_ctor_set(v___x_3121_, 1, v___f_3113_);
v___x_3122_ = l_StateRefT_x27_instMonad___redArg(v___x_3121_);
v_toApplicative_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3155_ == 0)
{
lean_object* v_unused_3156_; 
v_unused_3156_ = lean_ctor_get(v___x_3122_, 1);
lean_dec(v_unused_3156_);
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3155_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_toApplicative_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3155_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v_toFunctor_3127_; lean_object* v_toSeq_3128_; lean_object* v_toSeqLeft_3129_; lean_object* v_toSeqRight_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3153_; 
v_toFunctor_3127_ = lean_ctor_get(v_toApplicative_3123_, 0);
v_toSeq_3128_ = lean_ctor_get(v_toApplicative_3123_, 2);
v_toSeqLeft_3129_ = lean_ctor_get(v_toApplicative_3123_, 3);
v_toSeqRight_3130_ = lean_ctor_get(v_toApplicative_3123_, 4);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_toApplicative_3123_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; 
v_unused_3154_ = lean_ctor_get(v_toApplicative_3123_, 1);
lean_dec(v_unused_3154_);
v___x_3132_ = v_toApplicative_3123_;
v_isShared_3133_ = v_isSharedCheck_3153_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_toSeqRight_3130_);
lean_inc(v_toSeqLeft_3129_);
lean_inc(v_toSeq_3128_);
lean_inc(v_toFunctor_3127_);
lean_dec(v_toApplicative_3123_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3153_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___f_3134_; lean_object* v___f_3135_; lean_object* v___f_3136_; lean_object* v___f_3137_; lean_object* v___f_3138_; lean_object* v___x_3139_; lean_object* v___f_3140_; lean_object* v___f_3141_; lean_object* v___f_3142_; lean_object* v___x_3144_; 
v___f_3134_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_declNames___redArg___closed__0));
v___f_3135_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3136_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3127_);
v___f_3137_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3137_, 0, v_toFunctor_3127_);
v___f_3138_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3138_, 0, v_toFunctor_3127_);
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___f_3137_);
lean_ctor_set(v___x_3139_, 1, v___f_3138_);
v___f_3140_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3140_, 0, v_toSeqRight_3130_);
v___f_3141_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3141_, 0, v_toSeqLeft_3129_);
v___f_3142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3142_, 0, v_toSeq_3128_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 4, v___f_3140_);
lean_ctor_set(v___x_3132_, 3, v___f_3141_);
lean_ctor_set(v___x_3132_, 2, v___f_3142_);
lean_ctor_set(v___x_3132_, 1, v___f_3135_);
lean_ctor_set(v___x_3132_, 0, v___x_3139_);
v___x_3144_ = v___x_3132_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v___f_3135_);
lean_ctor_set(v_reuseFailAlloc_3152_, 2, v___f_3142_);
lean_ctor_set(v_reuseFailAlloc_3152_, 3, v___f_3141_);
lean_ctor_set(v_reuseFailAlloc_3152_, 4, v___f_3140_);
v___x_3144_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3146_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 1, v___f_3136_);
lean_ctor_set(v___x_3125_, 0, v___x_3144_);
v___x_3146_ = v___x_3125_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___f_3136_);
v___x_3146_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
size_t v_sz_3147_; size_t v___x_3148_; lean_object* v___x_185__overap_3149_; lean_object* v___x_3150_; 
v_sz_3147_ = lean_array_size(v_a_3100_);
v___x_3148_ = ((size_t)0ULL);
v___x_185__overap_3149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3146_, v___f_3134_, v_sz_3147_, v___x_3148_, v_a_3100_);
lean_inc(v_a_3104_);
lean_inc_ref(v_a_3103_);
lean_inc(v_a_3102_);
lean_inc_ref(v_a_3101_);
v___x_3150_ = lean_apply_5(v___x_185__overap_3149_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, lean_box(0));
return v___x_3150_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_declNames_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_3099_ = stack[0].m_num;
lean_object* v_a_3100_ = stack[1].m_obj;
lean_object* v_a_3101_ = stack[2].m_obj;
lean_object* v_a_3102_ = stack[3].m_obj;
lean_object* v_a_3103_ = stack[4].m_obj;
lean_object* v_a_3104_ = stack[5].m_obj;
lean_object* v_res_3157_;
v_res_3157_ = l_Lean_Compiler_LCNF_Probe_declNames(v_pu_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
stack->m_obj
 = v_res_3157_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_declNames___boxed(lean_object* v_pu_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_){
_start:
{
uint8_t v_pu_boxed_3165_; lean_object* v_res_3166_; 
v_pu_boxed_3165_ = lean_unbox(v_pu_3158_);
v_res_3166_ = l_Lean_Compiler_LCNF_Probe_declNames(v_pu_boxed_3165_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_);
lean_dec(v_a_3163_);
lean_dec_ref(v_a_3162_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
return v_res_3166_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(lean_object* v_inst_3167_, lean_object* v_x_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = lean_apply_1(v_inst_3167_, v_x_3168_);
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3167_ = stack[0].m_obj;
lean_object* v_x_3168_ = stack[1].m_obj;
lean_object* v___y_3169_ = stack[2].m_obj;
lean_object* v___y_3170_ = stack[3].m_obj;
lean_object* v___y_3171_ = stack[4].m_obj;
lean_object* v___y_3172_ = stack[5].m_obj;
lean_object* v_res_3176_;
v_res_3176_ = l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(v_inst_3167_, v_x_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
stack->m_obj
 = v_res_3176_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed(lean_object* v_inst_3177_, lean_object* v_x_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0(v_inst_3177_, v_x_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
return v_res_3184_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg(lean_object* v_inst_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3192_; lean_object* v_toApplicative_3193_; lean_object* v_toFunctor_3194_; lean_object* v_toSeq_3195_; lean_object* v_toSeqLeft_3196_; lean_object* v_toSeqRight_3197_; lean_object* v___f_3198_; lean_object* v___f_3199_; lean_object* v___f_3200_; lean_object* v___f_3201_; lean_object* v___x_3202_; lean_object* v___f_3203_; lean_object* v___f_3204_; lean_object* v___f_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v_toApplicative_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3241_; 
v___x_3192_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3193_ = lean_ctor_get(v___x_3192_, 0);
v_toFunctor_3194_ = lean_ctor_get(v_toApplicative_3193_, 0);
v_toSeq_3195_ = lean_ctor_get(v_toApplicative_3193_, 2);
v_toSeqLeft_3196_ = lean_ctor_get(v_toApplicative_3193_, 3);
v_toSeqRight_3197_ = lean_ctor_get(v_toApplicative_3193_, 4);
v___f_3198_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3199_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3194_, 2);
v___f_3200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3200_, 0, v_toFunctor_3194_);
v___f_3201_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3201_, 0, v_toFunctor_3194_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___f_3200_);
lean_ctor_set(v___x_3202_, 1, v___f_3201_);
lean_inc(v_toSeqRight_3197_);
v___f_3203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3203_, 0, v_toSeqRight_3197_);
lean_inc(v_toSeqLeft_3196_);
v___f_3204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3204_, 0, v_toSeqLeft_3196_);
lean_inc(v_toSeq_3195_);
v___f_3205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3205_, 0, v_toSeq_3195_);
v___x_3206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3202_);
lean_ctor_set(v___x_3206_, 1, v___f_3198_);
lean_ctor_set(v___x_3206_, 2, v___f_3205_);
lean_ctor_set(v___x_3206_, 3, v___f_3204_);
lean_ctor_set(v___x_3206_, 4, v___f_3203_);
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
lean_ctor_set(v___x_3207_, 1, v___f_3199_);
v___x_3208_ = l_StateRefT_x27_instMonad___redArg(v___x_3207_);
v_toApplicative_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v___x_3208_, 1);
lean_dec(v_unused_3242_);
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3241_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_toApplicative_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3241_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_toFunctor_3213_; lean_object* v_toSeq_3214_; lean_object* v_toSeqLeft_3215_; lean_object* v_toSeqRight_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3239_; 
v_toFunctor_3213_ = lean_ctor_get(v_toApplicative_3209_, 0);
v_toSeq_3214_ = lean_ctor_get(v_toApplicative_3209_, 2);
v_toSeqLeft_3215_ = lean_ctor_get(v_toApplicative_3209_, 3);
v_toSeqRight_3216_ = lean_ctor_get(v_toApplicative_3209_, 4);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_toApplicative_3209_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v_toApplicative_3209_, 1);
lean_dec(v_unused_3240_);
v___x_3218_ = v_toApplicative_3209_;
v_isShared_3219_ = v_isSharedCheck_3239_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_toSeqRight_3216_);
lean_inc(v_toSeqLeft_3215_);
lean_inc(v_toSeq_3214_);
lean_inc(v_toFunctor_3213_);
lean_dec(v_toApplicative_3209_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3239_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___f_3220_; lean_object* v___f_3221_; lean_object* v___f_3222_; lean_object* v___f_3223_; lean_object* v___f_3224_; lean_object* v___x_3225_; lean_object* v___f_3226_; lean_object* v___f_3227_; lean_object* v___f_3228_; lean_object* v___x_3230_; 
v___f_3220_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3220_, 0, v_inst_3185_);
v___f_3221_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3222_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3213_);
v___f_3223_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3223_, 0, v_toFunctor_3213_);
v___f_3224_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3224_, 0, v_toFunctor_3213_);
v___x_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___f_3223_);
lean_ctor_set(v___x_3225_, 1, v___f_3224_);
v___f_3226_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3226_, 0, v_toSeqRight_3216_);
v___f_3227_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3227_, 0, v_toSeqLeft_3215_);
v___f_3228_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3228_, 0, v_toSeq_3214_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 4, v___f_3226_);
lean_ctor_set(v___x_3218_, 3, v___f_3227_);
lean_ctor_set(v___x_3218_, 2, v___f_3228_);
lean_ctor_set(v___x_3218_, 1, v___f_3221_);
lean_ctor_set(v___x_3218_, 0, v___x_3225_);
v___x_3230_ = v___x_3218_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v___f_3221_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v___f_3228_);
lean_ctor_set(v_reuseFailAlloc_3238_, 3, v___f_3227_);
lean_ctor_set(v_reuseFailAlloc_3238_, 4, v___f_3226_);
v___x_3230_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3232_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 1, v___f_3222_);
lean_ctor_set(v___x_3211_, 0, v___x_3230_);
v___x_3232_ = v___x_3211_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___f_3222_);
v___x_3232_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
size_t v_sz_3233_; size_t v___x_3234_; lean_object* v___x_129__overap_3235_; lean_object* v___x_3236_; 
v_sz_3233_ = lean_array_size(v_a_3186_);
v___x_3234_ = ((size_t)0ULL);
v___x_129__overap_3235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3232_, v___f_3220_, v_sz_3233_, v___x_3234_, v_a_3186_);
lean_inc(v_a_3190_);
lean_inc_ref(v_a_3189_);
lean_inc(v_a_3188_);
lean_inc_ref(v_a_3187_);
v___x_3236_ = lean_apply_5(v___x_129__overap_3235_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, lean_box(0));
return v___x_3236_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_toString___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3185_ = stack[0].m_obj;
lean_object* v_a_3186_ = stack[1].m_obj;
lean_object* v_a_3187_ = stack[2].m_obj;
lean_object* v_a_3188_ = stack[3].m_obj;
lean_object* v_a_3189_ = stack[4].m_obj;
lean_object* v_a_3190_ = stack[5].m_obj;
lean_object* v_res_3243_;
v_res_3243_ = l_Lean_Compiler_LCNF_Probe_toString___redArg(v_inst_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
stack->m_obj
 = v_res_3243_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___redArg___boxed(lean_object* v_inst_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Lean_Compiler_LCNF_Probe_toString___redArg(v_inst_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
return v_res_3251_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_toString(lean_object* v_00_u03b1_3252_, lean_object* v_inst_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v___x_3260_; lean_object* v_toApplicative_3261_; lean_object* v_toFunctor_3262_; lean_object* v_toSeq_3263_; lean_object* v_toSeqLeft_3264_; lean_object* v_toSeqRight_3265_; lean_object* v___f_3266_; lean_object* v___f_3267_; lean_object* v___f_3268_; lean_object* v___f_3269_; lean_object* v___x_3270_; lean_object* v___f_3271_; lean_object* v___f_3272_; lean_object* v___f_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v_toApplicative_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3309_; 
v___x_3260_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3261_ = lean_ctor_get(v___x_3260_, 0);
v_toFunctor_3262_ = lean_ctor_get(v_toApplicative_3261_, 0);
v_toSeq_3263_ = lean_ctor_get(v_toApplicative_3261_, 2);
v_toSeqLeft_3264_ = lean_ctor_get(v_toApplicative_3261_, 3);
v_toSeqRight_3265_ = lean_ctor_get(v_toApplicative_3261_, 4);
v___f_3266_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3267_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3262_, 2);
v___f_3268_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3268_, 0, v_toFunctor_3262_);
v___f_3269_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3269_, 0, v_toFunctor_3262_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___f_3268_);
lean_ctor_set(v___x_3270_, 1, v___f_3269_);
lean_inc(v_toSeqRight_3265_);
v___f_3271_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3271_, 0, v_toSeqRight_3265_);
lean_inc(v_toSeqLeft_3264_);
v___f_3272_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3272_, 0, v_toSeqLeft_3264_);
lean_inc(v_toSeq_3263_);
v___f_3273_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3273_, 0, v_toSeq_3263_);
v___x_3274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3270_);
lean_ctor_set(v___x_3274_, 1, v___f_3266_);
lean_ctor_set(v___x_3274_, 2, v___f_3273_);
lean_ctor_set(v___x_3274_, 3, v___f_3272_);
lean_ctor_set(v___x_3274_, 4, v___f_3271_);
v___x_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
lean_ctor_set(v___x_3275_, 1, v___f_3267_);
v___x_3276_ = l_StateRefT_x27_instMonad___redArg(v___x_3275_);
v_toApplicative_3277_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3309_ == 0)
{
lean_object* v_unused_3310_; 
v_unused_3310_ = lean_ctor_get(v___x_3276_, 1);
lean_dec(v_unused_3310_);
v___x_3279_ = v___x_3276_;
v_isShared_3280_ = v_isSharedCheck_3309_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_toApplicative_3277_);
lean_dec(v___x_3276_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3309_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v_toFunctor_3281_; lean_object* v_toSeq_3282_; lean_object* v_toSeqLeft_3283_; lean_object* v_toSeqRight_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3307_; 
v_toFunctor_3281_ = lean_ctor_get(v_toApplicative_3277_, 0);
v_toSeq_3282_ = lean_ctor_get(v_toApplicative_3277_, 2);
v_toSeqLeft_3283_ = lean_ctor_get(v_toApplicative_3277_, 3);
v_toSeqRight_3284_ = lean_ctor_get(v_toApplicative_3277_, 4);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_toApplicative_3277_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; 
v_unused_3308_ = lean_ctor_get(v_toApplicative_3277_, 1);
lean_dec(v_unused_3308_);
v___x_3286_ = v_toApplicative_3277_;
v_isShared_3287_ = v_isSharedCheck_3307_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_toSeqRight_3284_);
lean_inc(v_toSeqLeft_3283_);
lean_inc(v_toSeq_3282_);
lean_inc(v_toFunctor_3281_);
lean_dec(v_toApplicative_3277_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3307_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___f_3288_; lean_object* v___f_3289_; lean_object* v___f_3290_; lean_object* v___f_3291_; lean_object* v___f_3292_; lean_object* v___x_3293_; lean_object* v___f_3294_; lean_object* v___f_3295_; lean_object* v___f_3296_; lean_object* v___x_3298_; 
v___f_3288_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toString___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3288_, 0, v_inst_3253_);
v___f_3289_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3290_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3281_);
v___f_3291_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3291_, 0, v_toFunctor_3281_);
v___f_3292_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3292_, 0, v_toFunctor_3281_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___f_3291_);
lean_ctor_set(v___x_3293_, 1, v___f_3292_);
v___f_3294_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3294_, 0, v_toSeqRight_3284_);
v___f_3295_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3295_, 0, v_toSeqLeft_3283_);
v___f_3296_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3296_, 0, v_toSeq_3282_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 4, v___f_3294_);
lean_ctor_set(v___x_3286_, 3, v___f_3295_);
lean_ctor_set(v___x_3286_, 2, v___f_3296_);
lean_ctor_set(v___x_3286_, 1, v___f_3289_);
lean_ctor_set(v___x_3286_, 0, v___x_3293_);
v___x_3298_ = v___x_3286_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v___f_3289_);
lean_ctor_set(v_reuseFailAlloc_3306_, 2, v___f_3296_);
lean_ctor_set(v_reuseFailAlloc_3306_, 3, v___f_3295_);
lean_ctor_set(v_reuseFailAlloc_3306_, 4, v___f_3294_);
v___x_3298_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3300_; 
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 1, v___f_3290_);
lean_ctor_set(v___x_3279_, 0, v___x_3298_);
v___x_3300_ = v___x_3279_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v___f_3290_);
v___x_3300_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
size_t v_sz_3301_; size_t v___x_3302_; lean_object* v___x_190__overap_3303_; lean_object* v___x_3304_; 
v_sz_3301_ = lean_array_size(v_a_3254_);
v___x_3302_ = ((size_t)0ULL);
v___x_190__overap_3303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_3300_, v___f_3288_, v_sz_3301_, v___x_3302_, v_a_3254_);
lean_inc(v_a_3258_);
lean_inc_ref(v_a_3257_);
lean_inc(v_a_3256_);
lean_inc_ref(v_a_3255_);
v___x_3304_ = lean_apply_5(v___x_190__overap_3303_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, lean_box(0));
return v___x_3304_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_toString_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3253_ = stack[1].m_obj;
lean_object* v_a_3254_ = stack[2].m_obj;
lean_object* v_a_3255_ = stack[3].m_obj;
lean_object* v_a_3256_ = stack[4].m_obj;
lean_object* v_a_3257_ = stack[5].m_obj;
lean_object* v_a_3258_ = stack[6].m_obj;
lean_object* v_res_3311_;
v_res_3311_ = l_Lean_Compiler_LCNF_Probe_toString(lean_box(0), v_inst_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
stack->m_obj
 = v_res_3311_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toString___boxed(lean_object* v_00_u03b1_3312_, lean_object* v_inst_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_Lean_Compiler_LCNF_Probe_toString(v_00_u03b1_3312_, v_inst_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
return v_res_3320_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg(lean_object* v_data_3321_){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3323_ = lean_array_get_size(v_data_3321_);
v___x_3324_ = lean_unsigned_to_nat(1u);
v___x_3325_ = lean_mk_empty_array_with_capacity(v___x_3324_);
v___x_3326_ = lean_array_push(v___x_3325_, v___x_3323_);
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_count___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_3321_ = stack[0].m_obj;
lean_object* v_res_3328_;
v_res_3328_ = l_Lean_Compiler_LCNF_Probe_count___redArg(v_data_3321_);
stack->m_obj
 = v_res_3328_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___redArg___boxed(lean_object* v_data_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_Compiler_LCNF_Probe_count___redArg(v_data_3329_);
lean_dec_ref(v_data_3329_);
return v_res_3331_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_count(lean_object* v_00_u03b1_3332_, lean_object* v_data_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3339_ = lean_array_get_size(v_data_3333_);
v___x_3340_ = lean_unsigned_to_nat(1u);
v___x_3341_ = lean_mk_empty_array_with_capacity(v___x_3340_);
v___x_3342_ = lean_array_push(v___x_3341_, v___x_3339_);
v___x_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
return v___x_3343_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_count_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_3333_ = stack[1].m_obj;
lean_object* v_a_3334_ = stack[2].m_obj;
lean_object* v_a_3335_ = stack[3].m_obj;
lean_object* v_a_3336_ = stack[4].m_obj;
lean_object* v_a_3337_ = stack[5].m_obj;
lean_object* v_res_3344_;
v_res_3344_ = l_Lean_Compiler_LCNF_Probe_count(lean_box(0), v_data_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
stack->m_obj
 = v_res_3344_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_count___boxed(lean_object* v_00_u03b1_3345_, lean_object* v_data_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Compiler_LCNF_Probe_count(v_00_u03b1_3345_, v_data_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
lean_dec(v_a_3350_);
lean_dec_ref(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
lean_dec_ref(v_data_3346_);
return v_res_3352_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg(lean_object* v_data_3354_){
_start:
{
lean_object* v___y_3357_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_3362_ = lean_unsigned_to_nat(0u);
v___x_3363_ = lean_array_get_size(v_data_3354_);
v___x_3364_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3365_ = lean_nat_dec_lt(v___x_3362_, v___x_3363_);
if (v___x_3365_ == 0)
{
lean_dec_ref(v_data_3354_);
v___y_3357_ = v___x_3362_;
goto v___jp_3356_;
}
else
{
lean_object* v___f_3366_; uint8_t v___x_3367_; 
v___f_3366_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3367_ = lean_nat_dec_le(v___x_3363_, v___x_3363_);
if (v___x_3367_ == 0)
{
if (v___x_3365_ == 0)
{
lean_dec_ref(v_data_3354_);
v___y_3357_ = v___x_3362_;
goto v___jp_3356_;
}
else
{
size_t v___x_3368_; size_t v___x_3369_; lean_object* v___x_3370_; 
v___x_3368_ = ((size_t)0ULL);
v___x_3369_ = lean_usize_of_nat(v___x_3363_);
v___x_3370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3364_, v___f_3366_, v_data_3354_, v___x_3368_, v___x_3369_, v___x_3362_);
v___y_3357_ = v___x_3370_;
goto v___jp_3356_;
}
}
else
{
size_t v___x_3371_; size_t v___x_3372_; lean_object* v___x_3373_; 
v___x_3371_ = ((size_t)0ULL);
v___x_3372_ = lean_usize_of_nat(v___x_3363_);
v___x_3373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3364_, v___f_3366_, v_data_3354_, v___x_3371_, v___x_3372_, v___x_3362_);
v___y_3357_ = v___x_3373_;
goto v___jp_3356_;
}
}
v___jp_3356_:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3358_ = lean_unsigned_to_nat(1u);
v___x_3359_ = lean_mk_empty_array_with_capacity(v___x_3358_);
v___x_3360_ = lean_array_push(v___x_3359_, v___y_3357_);
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
return v___x_3361_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_sum___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_3354_ = stack[0].m_obj;
lean_object* v_res_3374_;
v_res_3374_ = l_Lean_Compiler_LCNF_Probe_sum___redArg(v_data_3354_);
stack->m_obj
 = v_res_3374_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___redArg___boxed(lean_object* v_data_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_Compiler_LCNF_Probe_sum___redArg(v_data_3375_);
return v_res_3377_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_sum(lean_object* v_data_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v___y_3385_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3390_ = lean_unsigned_to_nat(0u);
v___x_3391_ = lean_array_get_size(v_data_3378_);
v___x_3392_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sortedBySize___redArg___closed__9));
v___x_3393_ = lean_nat_dec_lt(v___x_3390_, v___x_3391_);
if (v___x_3393_ == 0)
{
lean_dec_ref(v_data_3378_);
v___y_3385_ = v___x_3390_;
goto v___jp_3384_;
}
else
{
lean_object* v___f_3394_; uint8_t v___x_3395_; 
v___f_3394_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_sum___redArg___closed__0));
v___x_3395_ = lean_nat_dec_le(v___x_3391_, v___x_3391_);
if (v___x_3395_ == 0)
{
if (v___x_3393_ == 0)
{
lean_dec_ref(v_data_3378_);
v___y_3385_ = v___x_3390_;
goto v___jp_3384_;
}
else
{
size_t v___x_3396_; size_t v___x_3397_; lean_object* v___x_3398_; 
v___x_3396_ = ((size_t)0ULL);
v___x_3397_ = lean_usize_of_nat(v___x_3391_);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3392_, v___f_3394_, v_data_3378_, v___x_3396_, v___x_3397_, v___x_3390_);
v___y_3385_ = v___x_3398_;
goto v___jp_3384_;
}
}
else
{
size_t v___x_3399_; size_t v___x_3400_; lean_object* v___x_3401_; 
v___x_3399_ = ((size_t)0ULL);
v___x_3400_ = lean_usize_of_nat(v___x_3391_);
v___x_3401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3392_, v___f_3394_, v_data_3378_, v___x_3399_, v___x_3400_, v___x_3390_);
v___y_3385_ = v___x_3401_;
goto v___jp_3384_;
}
}
v___jp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3386_ = lean_unsigned_to_nat(1u);
v___x_3387_ = lean_mk_empty_array_with_capacity(v___x_3386_);
v___x_3388_ = lean_array_push(v___x_3387_, v___y_3385_);
v___x_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
return v___x_3389_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_sum_0interp(lean_interpreter_value* stack)
{
lean_object* v_data_3378_ = stack[0].m_obj;
lean_object* v_a_3379_ = stack[1].m_obj;
lean_object* v_a_3380_ = stack[2].m_obj;
lean_object* v_a_3381_ = stack[3].m_obj;
lean_object* v_a_3382_ = stack[4].m_obj;
lean_object* v_res_3402_;
v_res_3402_ = l_Lean_Compiler_LCNF_Probe_sum(v_data_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_);
stack->m_obj
 = v_res_3402_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_sum___boxed(lean_object* v_data_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_Lean_Compiler_LCNF_Probe_sum(v_data_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
return v_res_3409_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg(lean_object* v_n_3410_, lean_object* v_data_3411_){
_start:
{
lean_object* v_lower_3414_; lean_object* v_upper_3415_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; uint8_t v___x_3422_; 
v___x_3419_ = lean_array_get_size(v_data_3411_);
v___x_3420_ = lean_nat_sub(v___x_3419_, v_n_3410_);
v___x_3421_ = lean_unsigned_to_nat(0u);
v___x_3422_ = lean_nat_dec_le(v___x_3420_, v___x_3421_);
if (v___x_3422_ == 0)
{
v_lower_3414_ = v___x_3420_;
v_upper_3415_ = v___x_3419_;
goto v___jp_3413_;
}
else
{
lean_dec(v___x_3420_);
v_lower_3414_ = v___x_3421_;
v_upper_3415_ = v___x_3419_;
goto v___jp_3413_;
}
v___jp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3416_ = l_Array_toSubarray___redArg(v_data_3411_, v_lower_3414_, v_upper_3415_);
v___x_3417_ = l_Subarray_copy___redArg(v___x_3416_);
v___x_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
return v___x_3418_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_tail___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3410_ = stack[0].m_obj;
lean_object* v_data_3411_ = stack[1].m_obj;
lean_object* v_res_3423_;
v_res_3423_ = l_Lean_Compiler_LCNF_Probe_tail___redArg(v_n_3410_, v_data_3411_);
stack->m_obj
 = v_res_3423_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___redArg___boxed(lean_object* v_n_3424_, lean_object* v_data_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_Compiler_LCNF_Probe_tail___redArg(v_n_3424_, v_data_3425_);
lean_dec(v_n_3424_);
return v_res_3427_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_tail(lean_object* v_00_u03b1_3428_, lean_object* v_n_3429_, lean_object* v_data_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_){
_start:
{
lean_object* v_lower_3437_; lean_object* v_upper_3438_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; 
v___x_3442_ = lean_array_get_size(v_data_3430_);
v___x_3443_ = lean_nat_sub(v___x_3442_, v_n_3429_);
v___x_3444_ = lean_unsigned_to_nat(0u);
v___x_3445_ = lean_nat_dec_le(v___x_3443_, v___x_3444_);
if (v___x_3445_ == 0)
{
v_lower_3437_ = v___x_3443_;
v_upper_3438_ = v___x_3442_;
goto v___jp_3436_;
}
else
{
lean_dec(v___x_3443_);
v_lower_3437_ = v___x_3444_;
v_upper_3438_ = v___x_3442_;
goto v___jp_3436_;
}
v___jp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3439_ = l_Array_toSubarray___redArg(v_data_3430_, v_lower_3437_, v_upper_3438_);
v___x_3440_ = l_Subarray_copy___redArg(v___x_3439_);
v___x_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
return v___x_3441_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_tail_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3429_ = stack[1].m_obj;
lean_object* v_data_3430_ = stack[2].m_obj;
lean_object* v_a_3431_ = stack[3].m_obj;
lean_object* v_a_3432_ = stack[4].m_obj;
lean_object* v_a_3433_ = stack[5].m_obj;
lean_object* v_a_3434_ = stack[6].m_obj;
lean_object* v_res_3446_;
v_res_3446_ = l_Lean_Compiler_LCNF_Probe_tail(lean_box(0), v_n_3429_, v_data_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
stack->m_obj
 = v_res_3446_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_tail___boxed(lean_object* v_00_u03b1_3447_, lean_object* v_n_3448_, lean_object* v_data_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Compiler_LCNF_Probe_tail(v_00_u03b1_3447_, v_n_3448_, v_data_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
lean_dec(v_a_3451_);
lean_dec_ref(v_a_3450_);
lean_dec(v_n_3448_);
return v_res_3455_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg(lean_object* v_n_3456_, lean_object* v_data_3457_){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3459_ = lean_unsigned_to_nat(0u);
v___x_3460_ = l_Array_toSubarray___redArg(v_data_3457_, v___x_3459_, v_n_3456_);
v___x_3461_ = l_Subarray_copy___redArg(v___x_3460_);
v___x_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_head___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3456_ = stack[0].m_obj;
lean_object* v_data_3457_ = stack[1].m_obj;
lean_object* v_res_3463_;
v_res_3463_ = l_Lean_Compiler_LCNF_Probe_head___redArg(v_n_3456_, v_data_3457_);
stack->m_obj
 = v_res_3463_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___redArg___boxed(lean_object* v_n_3464_, lean_object* v_data_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Compiler_LCNF_Probe_head___redArg(v_n_3464_, v_data_3465_);
return v_res_3467_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_head(lean_object* v_00_u03b1_3468_, lean_object* v_n_3469_, lean_object* v_data_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3476_ = lean_unsigned_to_nat(0u);
v___x_3477_ = l_Array_toSubarray___redArg(v_data_3470_, v___x_3476_, v_n_3469_);
v___x_3478_ = l_Subarray_copy___redArg(v___x_3477_);
v___x_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_head_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_3469_ = stack[1].m_obj;
lean_object* v_data_3470_ = stack[2].m_obj;
lean_object* v_a_3471_ = stack[3].m_obj;
lean_object* v_a_3472_ = stack[4].m_obj;
lean_object* v_a_3473_ = stack[5].m_obj;
lean_object* v_a_3474_ = stack[6].m_obj;
lean_object* v_res_3480_;
v_res_3480_ = l_Lean_Compiler_LCNF_Probe_head(lean_box(0), v_n_3469_, v_data_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
stack->m_obj
 = v_res_3480_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_head___boxed(lean_object* v_00_u03b1_3481_, lean_object* v_n_3482_, lean_object* v_data_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l_Lean_Compiler_LCNF_Probe_head(v_00_u03b1_3481_, v_n_3482_, v_data_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
return v_res_3489_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(lean_object* v_probe_3495_, lean_object* v___x_3496_, lean_object* v_inst_3497_, lean_object* v___x_3498_, lean_object* v___x_3499_, lean_object* v_toMonadRef_3500_, lean_object* v___f_3501_, lean_object* v_decls_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v___x_3508_; 
lean_inc(v___y_3506_);
lean_inc_ref(v___y_3505_);
lean_inc(v___y_3504_);
lean_inc_ref(v___y_3503_);
lean_inc_ref(v_decls_3502_);
v___x_3508_ = lean_apply_6(v_probe_3495_, v_decls_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, lean_box(0));
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_toCold_3509_; lean_object* v_options_3510_; uint8_t v_hasTrace_3511_; 
v_toCold_3509_ = lean_ctor_get(v___y_3505_, 0);
v_options_3510_ = lean_ctor_get(v_toCold_3509_, 2);
v_hasTrace_3511_ = lean_ctor_get_uint8(v_options_3510_, sizeof(void*)*1);
if (v_hasTrace_3511_ == 0)
{
lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec_ref(v___f_3501_);
lean_dec_ref(v_toMonadRef_3500_);
lean_dec_ref(v___x_3499_);
lean_dec_ref(v___x_3498_);
lean_dec_ref(v_inst_3497_);
lean_dec_ref(v___x_3496_);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3518_ == 0)
{
lean_object* v_unused_3519_; 
v_unused_3519_ = lean_ctor_get(v___x_3508_, 0);
lean_dec(v_unused_3519_);
v___x_3513_ = v___x_3508_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_dec(v___x_3508_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v_decls_3502_);
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_decls_3502_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3557_; 
v_a_3520_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3522_ = v___x_3508_;
v_isShared_3523_ = v_isSharedCheck_3557_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3508_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3557_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v_inheritedTraceOptions_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; 
v_inheritedTraceOptions_3524_ = lean_ctor_get(v_toCold_3509_, 11);
v___x_3525_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__0));
v___x_3526_ = l_Lean_Name_mkStr2(v___x_3525_, v___x_3496_);
v___x_3527_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__2));
lean_inc(v___x_3526_);
v___x_3528_ = l_Lean_Name_append(v___x_3527_, v___x_3526_);
v___x_3529_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3524_, v_options_3510_, v___x_3528_);
lean_dec(v___x_3528_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3531_; 
lean_dec(v___x_3526_);
lean_dec(v_a_3520_);
lean_dec_ref(v___f_3501_);
lean_dec_ref(v_toMonadRef_3500_);
lean_dec_ref(v___x_3499_);
lean_dec_ref(v___x_3498_);
lean_dec_ref(v_inst_3497_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v_decls_3502_);
v___x_3531_ = v___x_3522_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_decls_3502_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
else
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_978__overap_3539_; lean_object* v___x_3540_; 
lean_del_object(v___x_3522_);
v___x_3533_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___closed__3));
v___x_3534_ = lean_array_to_list(v_a_3520_);
v___x_3535_ = l_List_toString___redArg(v_inst_3497_, v___x_3534_);
v___x_3536_ = lean_string_append(v___x_3533_, v___x_3535_);
lean_dec_ref(v___x_3535_);
v___x_3537_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
v___x_3538_ = l_Lean_MessageData_ofFormat(v___x_3537_);
v___x_978__overap_3539_ = l_Lean_addTrace___redArg(v___x_3498_, v___x_3499_, v_toMonadRef_3500_, v___f_3501_, v___x_3526_, v___x_3538_);
lean_inc(v___y_3506_);
lean_inc_ref(v___y_3505_);
lean_inc(v___y_3504_);
lean_inc_ref(v___y_3503_);
v___x_3540_ = lean_apply_5(v___x_978__overap_3539_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, lean_box(0));
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; 
v_unused_3548_ = lean_ctor_get(v___x_3540_, 0);
lean_dec(v_unused_3548_);
v___x_3542_ = v___x_3540_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_dec(v___x_3540_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v_decls_3502_);
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_decls_3502_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec_ref(v_decls_3502_);
v_a_3549_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3540_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3540_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec_ref(v_decls_3502_);
lean_dec_ref(v___f_3501_);
lean_dec_ref(v_toMonadRef_3500_);
lean_dec_ref(v___x_3499_);
lean_dec_ref(v___x_3498_);
lean_dec_ref(v_inst_3497_);
lean_dec_ref(v___x_3496_);
v_a_3558_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3508_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3508_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_probe_3495_ = stack[0].m_obj;
lean_object* v___x_3496_ = stack[1].m_obj;
lean_object* v_inst_3497_ = stack[2].m_obj;
lean_object* v___x_3498_ = stack[3].m_obj;
lean_object* v___x_3499_ = stack[4].m_obj;
lean_object* v_toMonadRef_3500_ = stack[5].m_obj;
lean_object* v___f_3501_ = stack[6].m_obj;
lean_object* v_decls_3502_ = stack[7].m_obj;
lean_object* v___y_3503_ = stack[8].m_obj;
lean_object* v___y_3504_ = stack[9].m_obj;
lean_object* v___y_3505_ = stack[10].m_obj;
lean_object* v___y_3506_ = stack[11].m_obj;
lean_object* v_res_3566_;
v_res_3566_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(v_probe_3495_, v___x_3496_, v_inst_3497_, v___x_3498_, v___x_3499_, v_toMonadRef_3500_, v___f_3501_, v_decls_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
stack->m_obj
 = v_res_3566_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed(lean_object* v_probe_3567_, lean_object* v___x_3568_, lean_object* v_inst_3569_, lean_object* v___x_3570_, lean_object* v___x_3571_, lean_object* v_toMonadRef_3572_, lean_object* v___f_3573_, lean_object* v_decls_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0(v_probe_3567_, v___x_3568_, v_inst_3569_, v___x_3570_, v___x_3571_, v_toMonadRef_3572_, v___f_3573_, v_decls_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
return v_res_3580_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = l_Lean_Core_instMonadTraceCoreM;
v___x_3584_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3585_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_3584_, v___x_3583_);
return v___x_3585_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___f_3587_; lean_object* v___x_3588_; 
v___x_3586_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__2);
v___f_3587_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___x_3588_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_3587_, v___x_3586_);
return v___x_3588_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3591_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_3592_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__1));
v___x_3593_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__5));
v___x_3594_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_3593_, v___x_3592_, v___x_3591_);
return v___x_3594_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7(void){
_start:
{
lean_object* v___x_3595_; lean_object* v___f_3596_; lean_object* v___f_3597_; lean_object* v___x_3598_; 
v___x_3595_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__6);
v___f_3596_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__0));
v___f_3597_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__4));
v___x_3598_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_3597_, v___f_3596_, v___x_3595_);
return v___x_3598_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg(lean_object* v_inst_3603_, uint8_t v_phase_3604_, lean_object* v_probe_3605_){
_start:
{
lean_object* v___x_3606_; lean_object* v_toApplicative_3607_; lean_object* v_toFunctor_3608_; lean_object* v_toSeq_3609_; lean_object* v_toSeqLeft_3610_; lean_object* v_toSeqRight_3611_; lean_object* v___f_3612_; lean_object* v___f_3613_; lean_object* v___f_3614_; lean_object* v___f_3615_; lean_object* v___x_3616_; lean_object* v___f_3617_; lean_object* v___f_3618_; lean_object* v___f_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v_toApplicative_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3660_; 
v___x_3606_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1, &l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Probe_map___redArg___closed__1);
v_toApplicative_3607_ = lean_ctor_get(v___x_3606_, 0);
v_toFunctor_3608_ = lean_ctor_get(v_toApplicative_3607_, 0);
v_toSeq_3609_ = lean_ctor_get(v_toApplicative_3607_, 2);
v_toSeqLeft_3610_ = lean_ctor_get(v_toApplicative_3607_, 3);
v_toSeqRight_3611_ = lean_ctor_get(v_toApplicative_3607_, 4);
v___f_3612_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__2));
v___f_3613_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_3608_, 2);
v___f_3614_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3614_, 0, v_toFunctor_3608_);
v___f_3615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3615_, 0, v_toFunctor_3608_);
v___x_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___f_3614_);
lean_ctor_set(v___x_3616_, 1, v___f_3615_);
lean_inc(v_toSeqRight_3611_);
v___f_3617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3617_, 0, v_toSeqRight_3611_);
lean_inc(v_toSeqLeft_3610_);
v___f_3618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3618_, 0, v_toSeqLeft_3610_);
lean_inc(v_toSeq_3609_);
v___f_3619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3619_, 0, v_toSeq_3609_);
v___x_3620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3616_);
lean_ctor_set(v___x_3620_, 1, v___f_3612_);
lean_ctor_set(v___x_3620_, 2, v___f_3619_);
lean_ctor_set(v___x_3620_, 3, v___f_3618_);
lean_ctor_set(v___x_3620_, 4, v___f_3617_);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v___f_3613_);
v___x_3622_ = l_StateRefT_x27_instMonad___redArg(v___x_3621_);
v_toApplicative_3623_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3660_ == 0)
{
lean_object* v_unused_3661_; 
v_unused_3661_ = lean_ctor_get(v___x_3622_, 1);
lean_dec(v_unused_3661_);
v___x_3625_ = v___x_3622_;
v_isShared_3626_ = v_isSharedCheck_3660_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_toApplicative_3623_);
lean_dec(v___x_3622_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3660_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v_toFunctor_3627_; lean_object* v_toSeq_3628_; lean_object* v_toSeqLeft_3629_; lean_object* v_toSeqRight_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3658_; 
v_toFunctor_3627_ = lean_ctor_get(v_toApplicative_3623_, 0);
v_toSeq_3628_ = lean_ctor_get(v_toApplicative_3623_, 2);
v_toSeqLeft_3629_ = lean_ctor_get(v_toApplicative_3623_, 3);
v_toSeqRight_3630_ = lean_ctor_get(v_toApplicative_3623_, 4);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_toApplicative_3623_);
if (v_isSharedCheck_3658_ == 0)
{
lean_object* v_unused_3659_; 
v_unused_3659_ = lean_ctor_get(v_toApplicative_3623_, 1);
lean_dec(v_unused_3659_);
v___x_3632_ = v_toApplicative_3623_;
v_isShared_3633_ = v_isSharedCheck_3658_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_toSeqRight_3630_);
lean_inc(v_toSeqLeft_3629_);
lean_inc(v_toSeq_3628_);
lean_inc(v_toFunctor_3627_);
lean_dec(v_toApplicative_3623_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3658_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___f_3634_; lean_object* v___f_3635_; lean_object* v___f_3636_; lean_object* v___f_3637_; lean_object* v___x_3638_; lean_object* v___f_3639_; lean_object* v___f_3640_; lean_object* v___f_3641_; lean_object* v___x_3643_; 
v___f_3634_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__4));
v___f_3635_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_map___redArg___closed__5));
lean_inc_ref(v_toFunctor_3627_);
v___f_3636_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3636_, 0, v_toFunctor_3627_);
v___f_3637_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3637_, 0, v_toFunctor_3627_);
v___x_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___f_3636_);
lean_ctor_set(v___x_3638_, 1, v___f_3637_);
v___f_3639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3639_, 0, v_toSeqRight_3630_);
v___f_3640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3640_, 0, v_toSeqLeft_3629_);
v___f_3641_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3641_, 0, v_toSeq_3628_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 4, v___f_3639_);
lean_ctor_set(v___x_3632_, 3, v___f_3640_);
lean_ctor_set(v___x_3632_, 2, v___f_3641_);
lean_ctor_set(v___x_3632_, 1, v___f_3634_);
lean_ctor_set(v___x_3632_, 0, v___x_3638_);
v___x_3643_ = v___x_3632_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3638_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v___f_3634_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v___f_3641_);
lean_ctor_set(v_reuseFailAlloc_3657_, 3, v___f_3640_);
lean_ctor_set(v_reuseFailAlloc_3657_, 4, v___f_3639_);
v___x_3643_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3645_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 1, v___f_3635_);
lean_ctor_set(v___x_3625_, 0, v___x_3643_);
v___x_3645_ = v___x_3625_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v___f_3635_);
v___x_3645_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v_toMonadRef_3648_; lean_object* v___f_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; lean_object* v___x_3652_; lean_object* v___f_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3646_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__3);
v___x_3647_ = lean_obj_once(&l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7, &l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__7);
v_toMonadRef_3648_ = lean_ctor_get(v___x_3647_, 0);
v___f_3649_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__8));
v___x_3650_ = lean_unsigned_to_nat(0u);
v___x_3651_ = 0;
v___x_3652_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__9));
lean_inc_ref(v_toMonadRef_3648_);
v___f_3653_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___lam__0___boxed), 13, 7);
lean_closure_set(v___f_3653_, 0, v_probe_3605_);
lean_closure_set(v___f_3653_, 1, v___x_3652_);
lean_closure_set(v___f_3653_, 2, v_inst_3603_);
lean_closure_set(v___f_3653_, 3, v___x_3645_);
lean_closure_set(v___f_3653_, 4, v___x_3646_);
lean_closure_set(v___f_3653_, 5, v_toMonadRef_3648_);
lean_closure_set(v___f_3653_, 6, v___f_3649_);
v___x_3654_ = ((lean_object*)(l_Lean_Compiler_LCNF_Probe_toPass___redArg___closed__10));
v___x_3655_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3655_, 0, v___x_3650_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
lean_ctor_set(v___x_3655_, 2, v___f_3653_);
lean_ctor_set_uint8(v___x_3655_, sizeof(void*)*3, v_phase_3604_);
lean_ctor_set_uint8(v___x_3655_, sizeof(void*)*3 + 1, v_phase_3604_);
lean_ctor_set_uint8(v___x_3655_, sizeof(void*)*3 + 2, v___x_3651_);
return v___x_3655_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_toPass___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3603_ = stack[0].m_obj;
uint8_t v_phase_3604_ = stack[1].m_num;
lean_object* v_probe_3605_ = stack[2].m_obj;
lean_object* v_res_3662_;
v_res_3662_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3603_, v_phase_3604_, v_probe_3605_);
stack->m_obj
 = v_res_3662_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___redArg___boxed(lean_object* v_inst_3663_, lean_object* v_phase_3664_, lean_object* v_probe_3665_){
_start:
{
uint8_t v_phase_boxed_3666_; lean_object* v_res_3667_; 
v_phase_boxed_3666_ = lean_unbox(v_phase_3664_);
v_res_3667_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3663_, v_phase_boxed_3666_, v_probe_3665_);
return v_res_3667_;
}
}
lean_object* l_Lean_Compiler_LCNF_Probe_toPass(lean_object* v_00_u03b2_3668_, lean_object* v_inst_3669_, uint8_t v_phase_3670_, lean_object* v_probe_3671_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_Compiler_LCNF_Probe_toPass___redArg(v_inst_3669_, v_phase_3670_, v_probe_3671_);
return v___x_3672_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Probe_toPass_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3669_ = stack[1].m_obj;
uint8_t v_phase_3670_ = stack[2].m_num;
lean_object* v_probe_3671_ = stack[3].m_obj;
lean_object* v_res_3673_;
v_res_3673_ = l_Lean_Compiler_LCNF_Probe_toPass(lean_box(0), v_inst_3669_, v_phase_3670_, v_probe_3671_);
stack->m_obj
 = v_res_3673_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Probe_toPass___boxed(lean_object* v_00_u03b2_3674_, lean_object* v_inst_3675_, lean_object* v_phase_3676_, lean_object* v_probe_3677_){
_start:
{
uint8_t v_phase_boxed_3678_; lean_object* v_res_3679_; 
v_phase_boxed_3678_ = lean_unbox(v_phase_3676_);
v_res_3679_ = l_Lean_Compiler_LCNF_Probe_toPass(v_00_u03b2_3674_, v_inst_3675_, v_phase_boxed_3678_, v_probe_3677_);
return v_res_3679_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = lean_unsigned_to_nat(4008565020u);
v___x_3739_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3740_ = l_Lean_Name_num___override(v___x_3739_, v___x_3738_);
return v___x_3740_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3742_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3743_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3744_ = l_Lean_Name_str___override(v___x_3743_, v___x_3742_);
return v___x_3744_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3746_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3747_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3748_ = l_Lean_Name_str___override(v___x_3747_, v___x_3746_);
return v___x_3748_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3749_ = lean_unsigned_to_nat(2u);
v___x_3750_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3751_ = l_Lean_Name_num___override(v___x_3750_, v___x_3749_);
return v___x_3751_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3753_; uint8_t v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3753_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_));
v___x_3754_ = 1;
v___x_3755_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_, &l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_);
v___x_3756_ = l_Lean_registerTraceClass(v___x_3753_, v___x_3754_, v___x_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3757_;
v_res_3757_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3757_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2____boxed(lean_object* v_a_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l___private_Lean_Compiler_LCNF_Probing_0__Lean_Compiler_LCNF_Probe_initFn_00___x40_Lean_Compiler_LCNF_Probing_4008565020____hygCtx___hyg_2_();
return v_res_3759_;
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
